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

## 10. Finite-precision acquisition of the original rational history

**Definition 10.1 (one original source and a rectangular reading contract).** Keep exactly the root, chronological pair process, name-only event labels and exact response $B$ of Definition 6.1. One unknown finite original word $w$ has already been executed, with original response $x=B(w)$. Every subsequent action acts on that same source and epoch. If the controller has subsequently executed the chronological probe word $u$, its present state is $\operatorname{enc}(wu)$ and its exact current response is

$$
f_u(x)=\frac{ax+b}{cx+d},\qquad
G_u=W(\operatorname{reverse}u)=
\begin{pmatrix}a&b\\c&d\end{pmatrix}.
$$

Here $ad-bc=1$, all entries are nonnegative integers and $d\ge1$. These are the generators and multiplication convention of Definition 6.3. In particular $f_L(x)=x/(1+x)$, $f_R(x)=x+1$ and $f_{uv}=f_v\circ f_u$. The set of original candidates under a supplied promise $|w|\le n$ is

$$
H_{\le n}=\{w\in\{L,R\}^*:|w|\le n\},\qquad
Q_n=\{B(w):w\in H_{\le n}\}.
$$

The integer $n$ is side information promised before acquisition. It is neither a cutoff learned from the reports nor a restriction on legal future actions: $wu$ may have length greater than $n$. For $n=0$ the original word is the known singleton $\varepsilon$, needing no read. Unless stated otherwise below, $n\ge1$.

At a read, the controller requests a finite nonnegative rational radius $\epsilon_i$ and receives a finite rational report $y_i$, with the closed certificate

$$
|y_i-f_{u_i}(x)|\le\epsilon_i.
$$

A read leaves the source state unchanged. Conditional on the entire previous transcript, **every** rational report satisfying this inequality is admissible, independently of which admissible reports occurred earlier. This is a rectangular adversarial joint channel, a support condition rather than a stochastic independence assumption. It imposes no shared bias, averaging law or hidden consistency constraint between errors. Reports may lie outside $\mathbb Q_{>0}$; only the certified absolute bound is required.

The deterministic controller uses its actual transcript, including its own actions, reports and requested radii, to choose the next forward $L/R$ action, read, precision request or stop. Apart from the stated promise, that transcript is its entire source-dependent input. Computation on the given finite rational strings is allowed. There is no reset, copy, inverse source action, exact-equality oracle or accessible archive of the unknown original word. Both actions remain total and their labels give only their names. An acquisition policy must stop after finitely many actions, reads and computation steps and return the correct **original** word for every permitted original source and every admissible report sequence. Recovering the subsequent word $wu$ without identifying its original cut is a different target.

**Theorem 10.2 (sharp precision for original-history acquisition, including a fixed probe).** Under Definition 10.1, fix a chronological word $u$ that must be executed before any read, without any earlier source-dependent record. Set

$$
\begin{aligned}
\alpha&=\min(c,d),&\beta&=\max(c,d),\\
A&=F_n\alpha+F_{n+1}\beta,
&B&=F_{n+1}\alpha+F_{n+2}\beta,
\end{aligned}
$$

where $F_0=0$, $F_1=1$ and $F_{k+2}=F_{k+1}+F_k$. Then

$$
\min_{\substack{x,z\in Q_n\\x\ne z}}|f_u(x)-f_u(z)|=\frac1{AB}.
\tag{10.1}
$$

For a fixed rational report radius $\epsilon\ge0$, exact original-word acquisition after this required probe, with arbitrary subsequent adaptive forward actions and repeated reads, is possible if and only if

$$
2\epsilon<\frac1{AB}.
\tag{10.2}
$$

One read immediately after $u$ suffices when (10.2) holds. In particular, with no required probe, $u=\varepsilon$, this gives the sharp condition

$$
2\epsilon<\delta_n,\qquad
\delta_n=\frac1{F_{n+1}F_{n+2}}.
\tag{10.3}
$$

Thus one read **before** probing suffices below (10.3), and no adaptive forward probing or repeated-reading policy at that fixed radius can recover all original words at or above the threshold. The impossibility also holds if the policy may request coarser radii $\epsilon_i\ge\epsilon$.

Proof. First establish the actual candidate gap, keeping the ordering conventions separate. Start with the ordered endpoint row $0/1,1/0$ and insert the mediant in every adjacent interval, repeatedly. After $k$ such refinements call the full ordered row $\mathcal P_k$. By the Stern–Brocot chart of Definition 6.4, the positive finite interior of $\mathcal P_{n+1}$ is exactly $Q_n$: the mediants first inserted at refinement $j+1$ have Stern–Brocot path length $j$, and reversal is a bijection on words of each length. This identifies the sets, not the chronological prefix orders. The endpoint construction, its adjacency determinant and its relation to the Calkin–Wilf children are classical supporting arithmetic; see Glasby, *Enumerating the rationals from left to right*, [arXiv:1011.2823](https://arxiv.org/abs/1011.2823), introduction.

Write adjacent fractions in this row as $p/q<r/s$, including the auxiliary endpoints. Their determinant is $rq-ps=1$. It holds initially and survives each mediant insertion, since

$$
(p+r)q-p(q+s)=rq-ps=r(q+s)-(p+r)s.
$$

Consequently all inserted fractions are reduced. For finite interior neighbors, the determinant-one transformation gives

$$
f_u(r/s)-f_u(p/q)
=\frac1{(cp+dq)(cr+ds)}.
\tag{10.4}
$$

The weights $cp+dq$ of the two initial endpoints $0/1,1/0$ are $d,c$. Mediant insertion replaces an interval's weight pair $(s,t)$ by either $(s,s+t)$ or $(s+t,t)$. Sort its pair increasingly. If $s\le t$, either sorted child is coordinatewise at most $(t,s+t)$; this upper bound is attained by retaining the endpoint of larger weight and replacing the other by the mediant. Starting at $(\alpha,\beta)$, induction therefore bounds every sorted pair after $k\ge1$ refinements by the single pair

$$
\left(F_{k-1}\alpha+F_k\beta,\quad
F_k\alpha+F_{k+1}\beta\right).
\tag{10.5}
$$

Indeed the bound is $(\beta,\alpha+\beta)$ at $k=1$, and applying $(s,t)\mapsto(t,s+t)$ produces the next displayed pair. Monotonicity of both coordinates gives the bound for every branch, not just for a chosen extremizer.

The two bounds in (10.5) are attained **together** along an actual nested sequence of intervals: at every step retain an endpoint of maximal weight. At the first step retain an original endpoint with weight $\beta$; the new mediant has weight $\alpha+\beta\ge\beta$. At the second step retain that mediant and replace the surviving original endpoint, choosing this option also in the tie case $\alpha=0$. Both endpoints are then inserted positive finite fractions, and subsequent refinements keep them positive and finite. This works also when $c=0$ or $c=d$. Since $k=n+1\ge2$, an actual pair of interior neighbors attains the product $AB$. No maximum from one candidate has been multiplied by an independently attained maximum from another.

All interior neighbor gaps are at least $1/(AB)$ by (10.4)–(10.5), and the constructed interior pair attains it. The function $f_u$ is strictly increasing on positive inputs. A nonneighbor gap is a sum of positive neighbor gaps, so cannot be smaller. This proves (10.1). For $u=\varepsilon$ the initial weights are $(d,c)=(1,0)$, yielding $A=F_{n+1}$, $B=F_{n+2}$. This unprobed Fibonacci arithmetic is literature-attested, rather than a new minimum-gap result: Kesseböhmer–Stratmann, *A multifractal analysis for Stern–Brocot intervals, continued fractions and Diophantine growth rates*, [DOI:10.1515/crelle.2007.029](https://doi.org/10.1515/crelle.2007.029), [arXiv:math/0509603v2](https://arxiv.org/abs/math/0509603v2), gives the smallest length $(F_{n+1}F_{n+2})^{-1}$ for its order-$n$ partition of $[0,1)$. Its initial row is $0/1,1/1$, so it is the part of $\mathcal P_{n+1}$ between $0$ and $1$. The interior attainment above additionally checks that the extremal gap belongs to the actual positive candidates and supplies the required weighted post-probe version.

For sufficiency, enumerate the finitely many original candidates $z\in Q_n$ and their $f_u(z)$. On receiving $y$, retain exactly those with $|y-f_u(z)|\le\epsilon$. The true candidate remains. Two retained candidates would have separation at most $2\epsilon$, contradicting (10.1) and (10.2). All comparisons are computations on specified rationals, so this terminates without a source equality oracle. Decode the unique original rational by Definition 6.3. The enumeration is computed from the supplied root and bound; it is not an archive of the unknown execution.

For necessity, each allowed forward action is nonexpansive in the absolute response metric on positive rationals:

$$
|f_R(x)-f_R(z)|=|x-z|,\qquad
|f_L(x)-f_L(z)|=\frac{|x-z|}{(1+x)(1+z)}\le|x-z|.
\tag{10.6}
$$

Take two actual original candidates attaining (10.1). If $2\epsilon\ge1/(AB)$, their post-$u$ responses differ by at most $2\epsilon$. Before the first read, the deterministic controller has the same source-independent transcript in the two executions and hence takes the same forward actions. By (10.6), the two current responses stay within $2\epsilon$ after any such common word. At each requested read supply the rational midpoint of the two current responses, which is permitted for both sources, including for any requested radius at least $\epsilon$. Induction preserves the identical transcript, the same next actions and radius requests, and the separation bound. The rectangular channel admits these successive choices conditional on the common transcript. Name-only labels and total enabledness give no additional distinction.

If the policy does not stop on this admissible common path, it violates the finite-stopping requirement. If it does stop, its identical output cannot be the two different original words. This proves necessity for all such adaptive policies. At equality, the closed error intervals touch at the rational midpoint, which is still admissible; the inequality must therefore be strict. $\square$

**Corollary 10.3 (precision index and its resource scope).** For the unprobed acquisition of Theorem 10.2, using the convention $\epsilon=2^{-b}$ with an integer precision index $b\ge0$, the least successful index is

$$
b_{\min}=\left\lfloor\log_2\bigl(F_{n+1}F_{n+2}\bigr)\right\rfloor+2.
\tag{10.7}
$$

For a required fixed probe, replace the Fibonacci product inside the logarithm by $AB$.

Proof. With $D=F_{n+1}F_{n+2}$, the strict inequality $2^{1-b}<1/D$ is equivalent to $b>1+\log_2 D$. The least integer satisfying it is (10.7). When $D$ is a power of two, the preceding index gives equality and is excluded by Theorem 10.2. The same calculation applies to $AB$.

This $b$ indexes a certified absolute radius. It is not the bit length of the rational report, an observer-memory bound, an output-size bound or a computation-cost bound. For example there are $2^{n+1}-1$ possible original words of length at most $n$, so a fixed-length binary encoding of all possible word outputs requires at least $\lceil\log_2(2^{n+1}-1)\rceil=n+1$ bits. That elementary counting bound has a different meaning from (10.7). The finite enumeration above proves attainability under the stated access contract without asserting algorithmic optimality. $\square$

**Theorem 10.4 (unbounded finite-certification obstruction and truthful-path scope).** Remove the supplied original-depth bound and allow arbitrary adaptive requests of strictly positive rational radii. No policy under Definition 10.1 can both stop finitely and recover the exact original word for every finite original history and every admissible error sequence.

More precisely, fix any finite truthful transcript, meaning that at each read its rational report is the exact current response of one original source, while its certified radius is strictly positive. For every finite chronological prefix $v$ and every integer $N\ge0$, that same finite transcript is compatible with an original word $w'$ beginning with $v$ and satisfying $|w'|>N$. Thus, even restricted to nonempty original histories, a finite truthful transcript certifies neither the first ancestral $L/R$ letter nor any finite upper bound on the original depth, and hence neither the exact depth nor the exact original word. These assertions concern original ancestry, not the known probe letters in the controller's own transcript.

Proof. Let $x$ be the original rational on the truthful path, with read radii $\epsilon_1,\ldots,\epsilon_m>0$ and chronological probe prefixes $u_1,\ldots,u_m$. If $m>0$, choose $\eta>0$ smaller than every $\epsilon_i$; if $m=0$, choose any $\eta>0$. Each $f_{u_i}$ is nonexpansive by (10.6), so every positive rational $z$ with $|z-x|<\eta$ satisfies

$$
|f_{u_i}(z)-y_i|
=|f_{u_i}(z)-f_{u_i}(x)|
\le |z-x|<\epsilon_i.
\tag{10.8}
$$

Induction through the given finite transcript shows that its very same reports are admissible from $z$: preceding reports agree, so the deterministic controller requests the same precision and takes the same actions. Each named action is legal and has the same name-only label. This induction also preserves a stopping decision if it occurs at the end of the transcript. It does not assume continuity of the controller's choices as functions of a report; the reports themselves are identical.

For the prefix assertion use the classical descendant-density result of Alkauskas–Steuding, *Statistical properties of the Calkin–Wilf tree: real and $p$-adic distribution*, [arXiv:0801.0054v2](https://arxiv.org/abs/0801.0054v2), Corollary 3: every nonempty open interval in $\mathbb R_{>0}$ contains a node reached by continuing any prescribed finite Calkin–Wilf path. Its left and right children are exactly Definition 6.1's chronological actions. This is density for chronological descendants; no Stern–Brocot prefix identification is used.

There are only finitely many rationals in $Q_N$. Choose a nonempty open interval inside $(x-\eta,x+\eta)\cap\mathbb R_{>0}$ avoiding $Q_N$ and $x$. The cited density applied to the prefix $v$ gives $z=B(w')$ in this interval, with $w'$ extending $v$. Theorem 6.2 and $z\notin Q_N$ imply $|w'|>N$. Equation (10.8) and the transcript induction give the claimed compatibility. In particular take $v=L$ and $v=R$ to obtain the two first-letter possibilities, and let $N$ be any proposed finite depth upper bound. This is a finite-path proof with strictly positive slack, not an assertion that every nontruthful boundary-saturating transcript has these ambiguities.

Finally suppose an all-source always-correct policy also always stops finitely. Run it on the original root with truthful reports, an admissible error sequence. Its promised finite stopping supplies such a finite transcript. The compatibility just proved supplies a different finite original word with the identical stopped transcript and hence the identical output, contradicting correctness. Arbitrarily small adaptively chosen positive radii do not change this argument: a finite truthful path has only finitely many of them, with a positive minimum. The conclusion does not address an infinite reading sequence, a zero-radius read, a supplied finite original-depth bound or a stronger joint channel. $\square$

**Proposition 10.5 (the same marginal radii can have different joint acquisition power).** For any rational $\epsilon\ge0$, consider instead a joint channel that supplies two exact rational report strings with one common unknown rational bias $e$, $|e|\le\epsilon$:

$$
y_0=x+e,\qquad
y_1=\frac{x}{1+x}+e,\qquad x\in\mathbb Q_{>0}.
\tag{10.9}
$$

The first read is before probing and the second is after the single chronological action $L$. Every report separately satisfies the same closed absolute-radius guarantee as in Definition 10.1. Nevertheless these two reports determine the exact unbounded original response $x$, and hence its original word.

Proof. Subtraction eliminates the shared bias:

$$
D=y_0-y_1=\frac{x^2}{1+x}>0,\qquad
x^2-Dx-D=0.
$$

The quadratic has exactly one positive root,

$$
x=\frac{D+\sqrt{D^2+4D}}2.
$$

It is rational for every report pair allowed by (10.9), since the actual $x$ is rational; indeed $D^2+4D=(2x-D)^2$. Exact rational arithmetic and rational-square-root extraction recover it from the finite strings. For a concrete allowed pair, $x=2/3$ and $e=\epsilon=1/10$ give $y_0=23/30$, $y_1=1/2$ and $D=4/15$, which determine $x=2/3$ uniquely. Theorem 6.2 then decodes the original word.

For $\epsilon>0$, this channel is not rectangular: after a first report from a specified source, its bias is fixed, so the second report is constrained by that same bias. Its allowed two-report set is a proper subset of the Cartesian product of the two marginal error intervals: the corner $(x+\epsilon,x/(1+x)-\epsilon)$ would require $e=\epsilon$ and $e=-\epsilon$ simultaneously. At $\epsilon=0$, both sets are the singleton $\{(x,x/(1+x))\}$, so the channel is rectangular; the exact recovery identity remains valid. For $\epsilon>0$, therefore, the freely chosen successive midpoint reports in Theorem 10.2, and the replayed truthful reports for alternative sources in Theorem 10.4, need not be allowed by (10.9). There is no contradiction. Per-read error bounds alone do not specify joint acquisition power. $\square$

**Corollary 10.6 (transport to the original four views).** Under the same source/epoch, operation and joint-channel contracts, replace the original-word target in Theorems 10.2 and 10.4 by any one of the original exact boundary response, the original root-oriented named-incidence path, the original literal chronology or the original indexed prefix-memory table of §6. The same attainability thresholds and unbounded finite-certification obstruction hold.

Proof. Each such exact output determines the original word by Theorems 5.2 and 6.2 and Definition 5.4; conversely the word constructs all four finite outputs. Compose these already supplied decoders and transports with the acquisition policy. The original cut is retained, even when probing has extended the source. These are computations of the specified original expressions, not permission to undo an action or retrieve a physically retained archive. Approximate boundaries, unnamed incidence and compressed outputs with a different decoding contract require separate target definitions. $\square$

**Definition 10.7 (mathematical suppliers and extent of the acquisition statement).** The source-specific acquisition conclusions of this section are `repo-derived` consequences for the process of §§5–6: the exact fixed-probe gap with joint interior attainment, the adaptive rectangular-channel threshold, the unbounded truthful-transcript obstruction and their original-four-view transports. This designation locates the synthesis; it does not certify worldwide originality. The mediant determinant arithmetic, Fibonacci minimum-interval formula and chronological descendant density used inside the proofs are `literature-attested` supporting results with the sources and conventions stated there.

The matrix supplier [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean) defines the same $G_L,G_R$ and $W$ and supplies `unimodular_wordMatrix` and `wordMatrix_lower_right_pos`. Its `word_node_is_reduced` states coprimality of the lower row; it does not identify that row with the positive column-action response. [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix`, supplies existence of word factorizations of natural determinant-one matrices, without asserting the noisy original-history theorem. [FiniteHorizonKernelRecurrence](../../../D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.lean) concerns exact iterated readouts and obtains its finite completion bound under a finite-state hypothesis. [FiniteCapacity](../../../D5/S3/ObserverMemory/Knowledge/FiniteCapacity.lean), `finite_knowledge_capacity`, counts realized exact readout classes under its finite-type and factorization hypotheses. Neither supplies a finite noisy certificate on the present unbounded rational carrier. These supplier correspondences assert no new Lean verification of the acquisition proofs.

The contract is a deterministic mathematical acquisition model with finite rational reports, specified errors and permitted forward operations. The precision index, finite computation, output representation and source identity remain distinct obligations. The section asserts no physical spacetime interpretation, universally optimal algorithm or impossibility for observers with other measurements, priors, joint-error relations or source access.

## 追加锚（本行以下为增补区）

## 11. Exact predictive cuts for an installed deterministic floor

**Assumption 11.1 (fixed floor, original cut and one source).** Retain the positive rational chronological source of Definition 6.1 and the original pre-probe word of Definition 10.1. Fix a supplied integer $M\ge1$. Replace the rectangular error channel by the separately installed, nondisturbing read

$$
q_M(x)=\lfloor Mx\rfloor,\qquad x\in\mathbb Q_{>0}.
\tag{11.1}
$$

The report is the entire nonnegative integer, finitely encoded without clipping. Its value is deterministic, including at grid endpoints. Each named forward action remains $L(x)=x/(1+x)$ or $R(x)=x+1$, with its name-only label. Reads, actions and the retained transcript concern the same source and epoch. The only source-dependent inputs to a deterministic controller are its actual reports; its known actions and finite computations may also be retained. There is no reset, copy, inverse source action, unknown-history archive or access to the outcomes of unperformed tests. Installation of (11.1) is a premise, not a consequence of the source dynamics. An integer report's finite encoding does not impose a uniform payload, working-memory or time bound.

For a chronological word $u$, use $f_u$ and its matrix convention from Definition 10.1. Define the semantic predictive equivalence

$$
x\equiv_M y
\quad\Longleftrightarrow\quad
q_M(f_u(x))=q_M(f_u(y))\text{ for every finite }u.
\tag{11.2}
$$

All actions are total and their labels are source-independent, so (11.2) also equates every finite response profile of §4. It compares possible tests from the original cut; it does not assert that all those tests have been performed on the one source. The targets of acquisition below are always functions of the original $x$, rather than of the post-probe state.

**Theorem 11.2 (complete cut classification and finite arithmetic core).** Put

$$
\begin{aligned}
\mathcal G_M&=\{k/M:k\in\mathbb Z_{>0}\},\\
P(z)&=\begin{cases}z/(1-z),&0<z<1,\\z-1,&z>1,\end{cases}\\
\mathcal A_M&=\bigcup_{r=1}^{M-1}
 \{P^i(r/M):i\ge0\text{ and all }i\text{ parent steps are defined}\},\\
\mathcal C_M&=\mathcal G_M\cup\mathcal A_M.
\end{aligned}
\tag{11.3}
$$

Here $P$ is undefined at $1$, and the union defining $\mathcal A_1$ is empty. For every $0<x<y$ in the entire positive rational carrier,

$$
x\equiv_M y
\quad\Longleftrightarrow\quad
\mathcal C_M\cap(x,y]=\varnothing.
\tag{11.4}
$$

The nongrid part has the exact description

$$
\mathcal K_M:=\mathcal C_M\setminus\mathcal G_M
 =\left\{\frac ab:
 \begin{array}{l}
a,b\in\mathbb Z_{>0},\ \gcd(a,b)=1,\ b\nmid M,\\
\exists h,j\in\mathbb Z_{>0},\quad ah+bj=M
\end{array}\right\}.
\tag{11.5}
$$

In particular $a+b\le M$ for every member of $\mathcal K_M$, so this core is finite. The cuts are locally finite and have minimum $1/M$. If they are ordered as $c_1<c_2<\cdots$, the predictive cells are exactly

$$
(0,c_1)\cap\mathbb Q,\qquad
[c_i,c_{i+1})\cap\mathbb Q\quad(i\ge1),\qquad c_1=1/M.
\tag{11.6}
$$

A canonical integer naming these cells on their actual image is

$$
\kappa_M(x)=\lfloor Mx\rfloor+
 \#\{z\in\mathcal K_M:z\le x\},\qquad
\kappa_M(x)=\kappa_M(y)\Longleftrightarrow x\equiv_M y.
\tag{11.7}
$$

Proof. Every $f_u$ is strictly increasing on positive inputs. Two of its floor reports differ precisely when a grid threshold $k/M$ lies in $(f_u(x),f_u(y)]$. Such a threshold has a unique preimage in $(x,y]$. Let $\mathcal D_M$ be the union of all these positive threshold preimages over all words, including the empty word. This proves (11.4) with $\mathcal D_M$ in place of $\mathcal C_M$; the right endpoint is included because floor takes its upper value at a threshold.

The image of $L$ is $(0,1)$ and that of $R$ is $(1,\infty)$. A positive threshold can therefore be pulled back through a last action in exactly one way: through $L$ by the first branch of $P$, or through $R$ by the second. The threshold $1$ has no positive preimage through either action. Conversely every finite legal parent chain reverses to a forward word whose final response is its starting threshold. Thus $\mathcal D_M$ is exactly the legal parent closure of $\mathcal G_M$.

In reduced coordinates $z=p/q$, a parent replaces $(p,q)$ by $(p,q-p)$ or $(p-q,q)$. Positivity and coprimality are preserved, and $p+q$ decreases strictly until $(1,1)$. Each chain is finite. Starting at $k/M>1$, the successive parents are subtractions of $1$, still on the same grid, until reaching $1$ or some $r/M$ with $1\le r<M$. Hence this closure is exactly (11.3), and $\mathcal A_M$ is finite.

For (11.5), let reduced $a/b$ be a nongrid threshold preimage. For some word matrix

$$
G_u=\begin{pmatrix}\alpha&\beta\\c&d\end{pmatrix},\qquad
\alpha d-\beta c=1,\quad d\ge1,
$$

its image is $(\alpha a+\beta b)/(ca+db)$. The numerator and denominator are coprime: a common divisor divides both $a$ and $b$ after multiplication by the integer inverse matrix. Since the image is on $\mathcal G_M$, its reduced denominator $ca+db$ divides $M$. If $c=0$, the determinant forces $\alpha=d=1$, so $b\mid M$, contrary to being nongrid. Thus $c\ge1$. With $t=M/(ca+db)$, take $h=tc$ and $j=td$ to obtain $ah+bj=M$ with both integers positive.

Conversely suppose the conditions on the right of (11.5) hold. Let $g=\gcd(h,j)$ and $(c,d)=(h/g,j/g)$, so $c,d\ge1$ are coprime. Choose $1\le\alpha\le c$ with $\alpha d\equiv1\pmod c$; for $c=1$ take $\alpha=1$. Then $\beta=(\alpha d-1)/c$ is a nonnegative integer. The nonnegative matrix with rows $(\alpha,\beta)$ and $(c,d)$ has determinant one. The supplier `unimodular_iff_wordMatrix` cited in §14 gives its generator factorization; reversing that supplier's word gives the chronological $u$. Consequently

$$
M f_u(a/b)
 =M\frac{\alpha a+\beta b}{ca+db}
 =g(\alpha a+\beta b)\in\mathbb Z_{>0},
$$

since $ca+db=M/g$. Thus $a/b\in\mathcal D_M$, and $b\nmid M$ excludes the initial grid. This proves (11.5).

Every parent in a chain from $r/M$ has reduced denominator at most $M$: subtraction either decreases that denominator or leaves it fixed. Its positive value is therefore at least $1/M$. The grid attains this minimum. A finite extra set together with a positive uniform grid is locally finite, unbounded, and has a successor for each cut. The no-cut condition now gives precisely (11.6), including the exceptional open initial cell. As $x$ crosses a grid cut, the first term of (11.7) increases by one; as it crosses a nongrid cut, the second does. Both terms are constant between cuts and take the upper value at a cut. Their sum therefore names exactly the cells, proving (11.7). $\square$

**Corollary 11.3 (a future quotient loses literal histories).** The relation $\equiv_M$ is a forward congruence for the declared readout and actions. Every one of its cells contains infinitely many distinct original histories, of unbounded original depth. No fixed $M$ predictive profile, even the complete family (11.2), recovers the original word on the full carrier.

Proof. The empty test gives equality of current readouts. If $x\equiv_M y$, then for every $u$ the test $au$ gives $q_M(f_u(f_a(x)))=q_M(f_u(f_a(y)))$. Hence $f_a(x)\equiv_M f_a(y)$, and total enabledness and name-only labels supply the remaining congruence data. Each cell in (11.6) contains a nonempty open real interval and hence infinitely many positive rationals. Theorem 6.2 bijects those rationals with original words. Only finitely many words have depth at most any fixed integer, proving unbounded depth inside each cell. Distinct words in one cell have identical complete predictive profiles, proving the nonrecovery assertion. Congruence alone therefore supplies no injective predecessor on this quotient. $\square$

## 12. A finite horizon on the infinite carrier and exact scale refinement

**Theorem 12.1 (finite test horizon and stronger single-path stabilization).** Under Assumption 11.1 set

$$
H_M=\max(0,M-2).
\tag{12.1}
$$

First, for every positive rational $x,y$,

$$
x\equiv_M y
\quad\Longleftrightarrow\quad
q_M(f_u(x))=q_M(f_u(y))\text{ for all }|u|\le H_M.
\tag{12.2}
$$

Second, fix any chronological path $u_1\cdots u_t$ with $t\ge H_M$, and read at its initial cut and after every action. If two original candidates have the same reports through action $H_M$, they have the same reports through action $t$. More generally they remain indistinguishable under every further common continuation, with a read at every cut, and under every deterministic continuation policy using only that transcript. Thus after $H_M$ actual actions a fully read path cannot gain any new distinctions between original candidates. No optimality of $H_M$ is asserted.

Proof. Write $\delta(p/q)$ for the unique chronological depth of a reduced positive rational. Each parent decreases $\max(p,q)$ by at least one until it becomes $1$. Therefore

$$
\delta(p/q)\le\max(p,q)-1.
\tag{12.3}
$$

In particular $\delta(r/M)\le M-1$ for $1\le r<M$, after reduction. A nongrid ancestor $P^i(r/M)$ cannot be the final root $1$, since $1\in\mathcal G_M$. Thus $i\le\delta(r/M)-1\le M-2$. Every nongrid cut has a witnessing word of length at most $M-2$, and every grid cut is witnessed by the empty word. For $M=1,2$ there are no nongrid cuts: (11.5) would require $a+b\le M$ and $b\nmid M$, which is impossible. Theorem 11.2 now proves (12.2) in all cases. This establishes a hypothetical finite test family; the following argument additionally concerns a single acquired path.

Consider a prefix $v$ of length $n>H_M$ ending in $L$. Since its final image lies in $(0,1)$, a threshold preimage must satisfy $f_v(z)=r/M$ for some $1\le r<M$. Forced parent peeling then gives

$$
P^n(r/M)=z,\qquad n\le\delta(r/M)\le M-1.
$$

For $M\ge2$, the simultaneous inequalities $n>H_M$ and $n\le M-1$ force $n=M-1=\delta(r/M)$, hence $z=1$. For $M=1$ there is no such $r$. Thus every threshold cut of $q_M\circ f_v$ lies in $\{1\}$. The initial report $q_M(x)$ already separates $x<1$ from $x\ge1$, so equality of initial reports implies equality of this later $L$ report. Endpoint equality at $1$ is included in this conclusion. If instead a prefix ends in $R$, then

$$
q_M(R(z))=q_M(z)+M,
\tag{12.4}
$$

so its report is determined by the preceding report. Inductively, no prefix after length $H_M$ refines the transcript partition already obtained. The same induction covers arbitrarily long common continuations. For an adaptive controller, identical reports and known actions give identical next choices; another induction therefore preserves the same reports, local computations and stopping decisions. Repeated nondisturbing reads do not change this argument. $\square$

**Theorem 12.2 (whole-carrier scale refinement is divisibility).** For positive integers $M,N$, the following conditions are equivalent:

$$
\begin{aligned}
&\text{for all }x,y\in\mathbb Q_{>0},\quad
 x\equiv_N y\Longrightarrow x\equiv_M y;\\
&\mathcal C_M\subseteq\mathcal C_N;\\
&M\mid N.
\end{aligned}
\tag{12.5}
$$

In particular a numerically larger fixed scale need not refine a smaller scale on this source.

Proof. Cut inclusion implies the first condition by (11.4). Conversely let $z\in\mathcal C_M\setminus\mathcal C_N$. Local finiteness permits a positive rational $x<z$ so close to $z$ that $\mathcal C_N\cap(x,z]=\varnothing$. Then $x\equiv_N z$ but $x\not\equiv_M z$, contradicting the first condition.

If $M\mid N$, then $\mathcal G_M\subseteq\mathcal G_N$; taking the same legal parent closure gives $\mathcal C_M\subseteq\mathcal C_N$. For necessity suppose that cut inclusion holds. Every nongrid cut $a/b\in\mathcal K_N$ satisfies $a+b\le N$, so its value is at most $N-1$. Choose an integer $s>N$ and put $z=s+1/M$. This lies in $\mathcal G_M$ and hence $\mathcal C_N$, but exceeds every member of $\mathcal K_N$. Therefore $z\in\mathcal G_N$, giving $Ns+N/M\in\mathbb Z$ and hence $M\mid N$.

For the direct observation correspondence when $N=tM$, one also has $q_M(z)=\lfloor q_N(z)/t\rfloor$ at every actual cut: writing $Nz=t k+r+\theta$ with $0\le r<t$ integral and $0\le\theta<1$ gives $Mz=k+(r+\theta)/t$ with $0\le(r+\theta)/t<1$. This is a computation from an acquired finer-scale report when that port is installed; (12.5) by itself does not install a second port. $\square$

## 13. Exact finite-prior acquisition and an injective-source obstruction

**Definition 13.1 (finite prior and finite decision predicate).** Supply a finite list $A\subset\mathbb Q_{>0}$ of possible original responses and a target function $\tau$ on this list with finitely encoded, decidably comparable values. This is public side information independent of which listed source is actual. The list and the action formulas permit exact computation of hypothetical candidate responses; only actual reads enter the acquired transcript. Original-word recovery uses $\tau(x)=\operatorname{dec}(x)$; original predictive-class recovery may use $\tau(x)=\kappa_M(x)$ from (11.7).

At an already read node let $u$ be the actual probe prefix and let $A'$ be the subset of original candidates compatible with all reports so far. For $a\in\{L,R\}$ and an integer $j$ define

$$
A'_{a,j}=\{x\in A':q_M(f_{ua}(x))=j\}.
\tag{13.1}
$$

Define $D_0(A',u)$ to mean that $\tau$ is constant on $A'$, with the empty case vacuous. Recursively $D_{k+1}(A',u)$ holds when $\tau$ is constant on $A'$, or when there is an $a\in\{L,R\}$ for which $D_k(A'_{a,j},ua)$ holds for every nonempty block $A'_{a,j}$. The finite list gives only finitely many such blocks. This predicate refers to the original target values throughout, including when different current predictive classes have merged.

**Theorem 13.2 (necessary and sufficient finite single-path criterion).** Under Assumption 11.1 and Definition 13.1, a deterministic no-reset policy that always stops finitely and recovers $\tau$ exists if and only if

$$
D_{H_M}(A_j,\varepsilon)\text{ holds for every nonempty }
A_j=\{x\in A:q_M(x)=j\}.
\tag{13.2}
$$

Whenever it exists, a policy with at most $H_M$ actions and $H_M+1$ reads exists. Condition (13.2) is decidable by finite exact integer/rational computation from the supplied list. Neither the horizon nor the finite computation asserts a fixed memory or bit-cost bound.

Proof. Induction on $k$ shows that $D_k(A',u)$ is exactly the existence of a decision tree with at most $k$ further actions, reading immediately after each action and returning the original target. A homogeneous block stops. Otherwise the first action is one common $a$, its actual read selects exactly one of the nonempty blocks (13.1), and each block must admit the remaining tree. This proves both directions of the induction, including $k=0$. The initial read gives the blocks in (13.2), so the criterion is sufficient and has the stated resource bound.

For necessity take any successful policy. Insert a read at the initial cut and after every action; these nondisturbing reads can be retained while the old policy is simulated using only the reports it requested. Redundant requested reads can reuse the actual current report. This normalization does not add an action or any unacquired source-dependent input. On the finite prior there is one deterministic terminating run for each original candidate, so the normalized tree has finitely many reachable nodes, although no common bound was initially assumed.

At a node reached after $H_M$ actions, take any two original candidates compatible with its entire fully read transcript. Theorem 12.1 implies identical future reports along every common continuation. The normalized policy therefore has identical further decisions and final output for this pair. Its correctness forces equal original targets. Every such node is consequently homogeneous and can be replaced by an immediate output. Earlier stopped nodes are homogeneous by the same correctness argument. The truncated tree has depth at most $H_M$, so the induction gives (13.2). Empty priors need no reads. Finally the recursion is finite, its action alphabet has size two, and all candidate transformations, floor comparisons and target comparisons are effective on the supplied finite encodings. This proves decidability.

The elementary decision-tree induction is the usual adaptive distinguishing-experiment construction; the new source-specific content enabling its finite completeness here is Theorem 12.1 on the infinite rational carrier. The distinction between separately evaluated tests and one adaptive experiment is already explicit in van den Bos–Vaandrager, [arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), §4, Definitions 10–11 and Figure 3, and in [Transport Memory Completion §§31.4–31.5 and 52](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md). No finite-automaton complexity or homing bound from that literature is used. $\square$

**Proposition 13.3 (depth two: attainable at scale three, obstructed at scale four).** For the original prior $Q_2$ of Definition 10.1,

$$
\mathcal C_3=\mathcal G_3\cup\{1/2\},\qquad
\mathcal C_4=\mathcal G_4\cup\{1/3\}.
\tag{13.3}
$$

At $M=3$ the exact original word is acquirable with at most two reads and one action. At $M=4$ the two originals $L$ and $RL$ are forever indistinguishable, so no policy recovers the original word over $Q_2$.

Proof. In (11.5), $M=3$ permits only the nongrid reduced pair $(a,b)=(1,2)$; $M=4$ permits only $(1,3)$. Both satisfy $a+b=M$ with $h=j=1$. All other positive coprime pairs with $a+b\le M$ have denominator dividing $M$. This gives (13.3).

Here are all actual original candidates and their initial scale-three reports:

| Original word | Original response | $q_3$ |
| --- | --- | --- |
| $\varepsilon$ | $1$ | $3$ |
| $L$ | $1/2$ | $1$ |
| $R$ | $2$ | $6$ |
| $LL$ | $1/3$ | $1$ |
| $LR$ | $3/2$ | $4$ |
| $RL$ | $2/3$ | $2$ |
| $RR$ | $3$ | $9$ |

Read first. Every report except $1$ identifies its original word. On report $1$, execute $L$ on the same source and read again: the originals $1/2$ and $1/3$ become $1/3$ and $1/4$, with reports $1$ and $0$. This supplies the claimed actual policy. At scale four, $(1/2,2/3]$ contains neither a quarter-grid cut nor the extra cut $1/3$. Thus $1/2\equiv_4 2/3$ by (11.4). Congruence and identical transcript decisions preserve their equality of all future reports, proving the impossibility. $\square$

**Theorem 13.4 (three distinct original classes with no one-path acquisition at scale sixteen).** At $M=16$ take the three original sources

$$
(x_1,x_2,x_3)=(1/4,2/7,3/10),\qquad
(w_1,w_2,w_3)=(LLL,RLLL,RRLLL).
\tag{13.4}
$$

Their original predictive classes are pairwise distinct. Nevertheless no deterministic policy under Assumption 11.1 can recover their original predictive class, or their original word, for every member of this three-source prior. This obstruction allows arbitrarily many reads, arbitrary finite computation and an unbounded number of forward actions. The physical maps remain injective.

Proof. Direct chronological execution from $1$ gives (13.4). The exact candidate responses for two possible test words are

$$
\begin{array}{c|ccc|ccc}
 u&f_u(x_1)&f_u(x_2)&f_u(x_3)&q_{16}(f_u(x_1))&q_{16}(f_u(x_2))&q_{16}(f_u(x_3))\\ \hline
 \varepsilon&1/4&2/7&3/10&4&4&4\\
 LL&1/6&2/11&3/16&2&2&3\\
 RL&5/9&9/16&13/23&8&9&9
\end{array}
\tag{13.5}
$$

The $RL$ test separates the first original from the second; the $LL$ test separates the third from each of the first two. Hence all three original classes are different. These are two counterfactual tests starting at the same original cut. Their combined rows are not a transcript obtainable by performing both tests successively.

For an exact all-continuation analysis of the first action, (11.5) gives the following complete nongrid core. Each row lists the allowed reduced numerators for its denominator:

| $b$ | $a$ with $a/b\in\mathcal K_{16}$ |
| --- | --- |
| $3$ | $1,2,4,5,7,10,13$ |
| $5$ | $1,2,3,6,11$ |
| $6$ | $1,5$ |
| $7$ | $1,2,3,9$ |
| $9$ | $1,7$ |
| $10$ | $1,3$ |
| $11$ | $1,5$ |
| $12$ | $1$ |
| $13$ | $1,3$ |
| $14$ | $1$ |
| $15$ | $1$ |

This finite enumeration follows directly by taking $1\le b\le15$ with $b\nmid16$, then $1\le j\le\lfloor15/b\rfloor$, and the positive divisors $a$ of $16-bj$ with $\gcd(a,b)=1$; $h=(16-bj)/a$. These ranges are exhaustive because $ah\ge1$ and $a+b\le16$, and every listed divisor supplies positive $h,j$. Thus the table proves both inclusion directions without a bound on future test length.

If the first action is $L$, the first two states become $1/5$ and $2/9$. The table and the sixteenth grid show they belong to the one cell

$$
1/5\le 2/9<3/13,\qquad
[1/5,3/13)\cap\mathbb Q.
\tag{13.6}
$$

Indeed the neighboring grid points are $3/16<1/5<2/9<4/16$, and the table has no intervening nongrid cut before $3/13$. Hence $L(x_1)\equiv_{16}L(x_2)$. If the first action is $R$, the last two states become $9/7$ and $13/10$, both in the cell

$$
9/7\le13/10<21/16,\qquad
[9/7,21/16)\cap\mathbb Q.
\tag{13.7}
$$

The neighboring grid points are $20/16<9/7<13/10<21/16$, and the next nongrid cut above $9/7$ is $4/3>21/16$. Thus $R(x_2)\equiv_{16}R(x_3)$. The cell criterion proves equality under every finite continuation in both cases, not only agreement for a finite sample of test words.

Before the first action, every read returns $4$. If the controller stops there, one common output cannot identify all three originals. If it never acts or stops, it fails finite acquisition. Otherwise its first action is common to all three executions. The choice $L$ makes the first pair forever indistinguishable; the choice $R$ does so for the last pair. Their previous transcripts were identical, and congruence supplies identical future reports under identical choices. Induction therefore gives the same full acquired transcript and stopping decision for that pair. Its two different original class labels, and its two different original words, cannot both be correct outputs. This proves the impossibility for every such policy.

Finally $R(y)-R(x)=y-x>0$ and $L(y)-L(x)=(y-x)/((1+x)(1+y))>0$ whenever $0<x<y$. Both source maps and all their compositions remain injective. What merges in (13.6)–(13.7) is the predictive quotient, not the physical rational states. $\square$

**Corollary 13.5 (original four-view recovery follows actual acquisition).** Under the same source and access contracts, replace original-word recovery by recovery of any one of the original exact rational boundary, original rooted named-incidence path, original literal chronology, or original indexed prefix-memory table of §§5–6. The policy of Proposition 13.3 at scale three computes each of these targets. Its scale-four impossibility, Theorem 13.4's scale-sixteen impossibility, and Corollary 11.3's full-carrier impossibility hold for each target.

Proof. Each listed exact original expression determines the original word by Theorem 6.2 and Definition 5.4; the word constructs every listed expression. Compose these existing decoders with the actual successful policy to obtain attainability, or with a hypothetical successful policy to contradict the respective original-word obstruction. The original cut and source identity are retained throughout. These computations neither undo a source action nor assert that an indexed archive had been physically stored. A predictive class remains a coarser target and does not itself become a literal-history decoder. $\square$

## 14. Mathematical antecedents and scope of the fixed-floor contract

**Definition 14.1 (antecedents and supplied hypotheses).** The source-specific cut formula (11.3), arithmetic core (11.5), same-path horizon, divisibility criterion and rational acquisition/obstruction results are `repo-derived` ordinary mathematical consequences for Assumption 11.1. This classification makes no claim of worldwide novelty. Classical Calkin–Wilf enumeration, Farey adjacency and unimodular arithmetic are supporting antecedents; Glasby, *Enumerating the rationals from left to right*, [arXiv:1011.2823v1](https://arxiv.org/abs/1011.2823v1), introduction and pp. 1–2, explicitly distinguishes the mediant and chronological child conventions. Their correspondence remains Definition 6.3's reversal convention.

The actual matrix suppliers are [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `unimodular_wordMatrix` and `wordMatrix_lower_right_pos`, and [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix`. The first supplies the nonnegative determinant-one matrices and positive lower-right entry for the specified generators. Its `word_node_is_reduced` concerns the matrix's lower row; it is not substituted for reducedness of the column-action response. The second states that every nonnegative integer determinant-one matrix has such a word factorization, which is precisely the existence used in the converse of (11.5). Coprimality of the transformed response in that proof follows from the integer inverse matrix and the original reduced pair.

[FiniteDistinguishingCertificate](../../../D5/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate.lean), `finite_distinguishing_certificate`, assumes a supplied surjective finite classification exact for all available evaluations and selects a finite set of separately evaluated protocols. It does not execute those protocols successively on one unreset source. The whole-carrier quotient (11.6) has infinitely many classes; finiteness of its extra cut core is a different assertion. [QuantizedWordApproximation](../../../D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.lean), `quantized_word_approximation`, assumes a supplied finite codebook and quantizer with a global state-error bound and Lipschitz transition/readout bounds. Such an approximate codebook and those hypotheses are not an exact original-word acquisition contract for (11.1).

The distinct floor and total-error ports of [Affine Finite Reply Recovery, Definition 4.3](RECURSIVE_RELATIONAL_OBSERVATION_AFFINE_FINITE_REPLY_RECOVERY.md), the dense-entrance floor obstructions and lattice assumptions of [Atomic Generation Acquisition III §§28–33](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_III.md), and the supplied-versus-acquired resource coordinates of [Stationary-Q Endpoint Sensors §22.8](RECURSIVE_RELATIONAL_OBSERVATION_STATIONARY_Q_ENDPOINT_SENSORS.md) retain their own sources and operations. Their distinctions between a specified sensor, an actual report, a computed result and a retained record apply here as hypothesis accounting, without transferring their physical or numerical conclusions. The one-history acquisition distinction is also already developed in [Effective Resolution Continuation §§12–14](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION_CONTINUATION.md); the present cut arithmetic and horizon are for this rational $L/R$ source.

Dubbini–Piccoli–Bicchi, *Left invertibility of discrete-time output-quantized systems: the linear case with finite inputs*, [arXiv:1103.4039v1](https://arxiv.org/abs/1103.4039v1), §§1–4, studies recovery of an unknown input sequence under known linear dynamics. Here the forward actions are known, the original state is unknown, and $L$ is nonlinear. Their left-invertibility results therefore do not supply any of Theorems 11.2–13.4. Likewise the adaptive-test antecedent cited in Theorem 13.2 supplies the experiment distinction, not this source's arithmetic horizon or a reset permission.

This fixed-floor contract has exact deterministic grid endpoints and no freely selectable radius. Section 10's adversarial positive-error reports cannot replace it, and a change from one contract to the other changes the available joint observations. The finite bounds above count actions and reads as stated; report widths, arithmetic, candidate descriptions, output size, retention and physical installation remain separate quantities. The four recovered expressions have §§5–6's mathematical meanings, with no additional metric spacetime, physical clock or apparatus realization assumed.

## 追加锚（本行以下为增补区）

## 15. A sharp installed read for the entire predictive class

**Definition 15.1 (scale comparisons on the original cut).** Retain exactly Assumption 11.1's positive rational source, chronological actions, deterministic unclipped floor convention and source identity. For positive integers $M,D$, saying that a current $q_D$ report determines the full scale-$M$ predictive class means

$$
q_D(x)=q_D(y)\ \Longrightarrow\ x\equiv_M y
\qquad(x,y\in\mathbb Q_{>0}).
\tag{15.1}
$$

This compares partitions of the same original source, with no preceding probe. It is equivalent to a factor from the actual report image to $\kappa_M(\mathbb Q_{>0})$, or to the entire scale-$M$ future-response profile. Put $\Lambda_M=\operatorname{lcm}(1,2,\ldots,M)$, with $\Lambda_1=1$. The scale $D$ is an available read only when its nondisturbing port is supplied; a partition factor does not install a port or execute any counterfactual continuation.

**Theorem 15.2 (least current-read scale and arithmetic saturation).** Under Definition 15.1,

$$
q_D\text{ determines }\equiv_M
\quad\Longleftrightarrow\quad
\mathcal C_M\subseteq\mathcal G_D
\quad\Longleftrightarrow\quad
\Lambda_M\mid D.
\tag{15.2}
$$

Thus $\Lambda_M$ is the least sufficient single current-read scale, both in the divisibility order and in the ordinary numerical order among positive integer scales. This minimum concerns determination of the specified predictive class by one floor report; it is not a minimum of report length, installation cost or history-acquisition resources. Furthermore, for every reduced $a/b>0$,

$$
M>ab\quad\Longrightarrow\quad a/b\in\mathcal C_M.
\tag{15.3}
$$

Proof. The raw $D$-floor cells are $(0,1/D)\cap\mathbb Q$ and $[k/D,(k+1)/D)\cap\mathbb Q$ for $k\ge1$. If every predictive cut is a $D$-grid cut, none of these raw cells crosses a predictive cut, so Theorem 11.2 gives (15.1). Conversely suppose $z\in\mathcal C_M\setminus\mathcal G_D$. Choose a positive rational $x<z$ sufficiently close that $\mathcal G_D\cap(x,z]=\varnothing$. This is possible because $z$ is strictly inside a raw cell. Then $q_D(x)=q_D(z)$ while $x\not\equiv_M z$, proving the first equivalence including its endpoint direction.

Every reduced denominator of a cut in $\mathcal C_M$ is at most $M$: grid denominators divide $M$, and the nongrid core has $a+b\le M$. Consequently $\Lambda_M\mid D$ puts every such cut on $\mathcal G_D$. For the converse, $1/b\in\mathcal C_M$ for each $1\le b\le M$. When $b\mid M$ it is a grid cut. Otherwise $b<M$, and $1\cdot(M-b)+b\cdot1=M$ has both coefficients positive, so (11.5) makes it a nongrid cut. Therefore $\mathcal C_M\subseteq\mathcal G_D$ forces $D/b$ to be an integer for every $b\le M$, exactly $\Lambda_M\mid D$. Every sufficient $D$ is a positive multiple of $\Lambda_M$, proving both stated minimalities. In particular $\Lambda_3=6$ and $\Lambda_4=12$; the extra cuts $1/2$ and $1/3$ respectively explain why the original scale alone does not suffice in these cases.

For (15.3), choose $j\in\{1,\ldots,a\}$ with $bj\equiv M\pmod a$, using $\gcd(a,b)=1$; when $a=1$ take $j=1$. Since $bj\le ab<M$, the integer $h=(M-bj)/a$ is positive. Thus $ah+bj=M$ with $h,j>0$. If $b\mid M$ the fraction is on the grid, and otherwise (11.5) puts it in the nongrid core. The modular step is classical coprime arithmetic; the asserted consequence uses precisely this source's already derived cut formula. $\square$

## 16. The predictive inverse limit and its exact source image

**Definition 16.1 (nested predictive cells).** Fix any sequence of positive integers $s_0,s_1,\ldots$ with $s_n\mid s_{n+1}$ and $s_n\to\infty$. Repetitions are allowed. Write $\mathscr P_n$ for the actual partition of $\mathbb Q_{>0}$ into $\equiv_{s_n}$ cells. By Theorem 12.2 a cell of $\mathscr P_{n+1}$ lies in a unique cell of $\mathscr P_n$; this inclusion defines the restriction map. Let

$$
\mathscr L_{\mathbf s}
 =\{(I_n)_{n\ge0}:I_n\in\mathscr P_n, I_{n+1}\subseteq I_n\},
\qquad
\iota(x)=(\text{the cell of }x\text{ in }\mathscr P_n)_n.
\tag{16.1}
$$

These are compatible families of actual stage cells; no common rational realization is built into their definition. Write the endpoints of $I_n$ as $\ell_n,r_n$. The cell is $[\ell_n,r_n)\cap\mathbb Q$ when $\ell_n>0$ and $(0,r_n)\cap\mathbb Q$ when $\ell_n=0$. Its associated real interval has the same endpoint convention. Every upper endpoint is finite, and

$$
0\le\ell_n<r_n<\infty,\qquad r_n-\ell_n\le1/s_n.
\tag{16.2}
$$

The inequality follows because predictive cells refine the raw $s_n$-floor cells. This carrier is an inverse limit of partitions of the fixed source, rather than a change to the original source of histories.

**Theorem 16.2 (classification and the source-realization criterion).** Every thread in $\mathscr L_{\mathbf s}$ has a unique finite real endpoint limit

$$
t=\sup_n\ell_n=\inf_n r_n\in[0,\infty).
\tag{16.3}
$$

There is exactly one thread over $0$, denoted $0^+$; exactly one over each positive irrational $t$; and exactly two over each positive rational $t$, denoted $t^-$ and $t^+$. Here $t^+$ always selects the cell containing $t$, and $t^-$ selects the cell immediately to the left whenever $t$ is a cut, and the cell containing $t$ otherwise. Consequently the same explicit carrier represents every such predictive limit:

$$
\widehat X
 =\{0^+\}\ \sqcup\ (\mathbb R_{>0}\setminus\mathbb Q)
 \ \sqcup\ \{t^-,t^+:t\in\mathbb Q_{>0}\}.
\tag{16.4}
$$

The map $\iota$ is injective and has exactly the image

$$
\iota(\mathbb Q_{>0})
 =\{t^+:t\in\mathbb Q_{>0}\}
 =\{(I_n):\ell_n\text{ is eventually a constant }c>0\}.
\tag{16.5}
$$

For a thread in this image $\bigcap_n I_n=\{c\}$; for every other thread that intersection in the actual rational carrier is empty. In particular compatibility and separation hold without surjectivity of the original-source map.

Proof. Theorem 15.2 gives $a/b\in\mathcal C_{s_n}$ as soon as $s_n>ab$. Together with nestedness this proves

$$
\bigcup_n\mathcal C_{s_n}=\mathbb Q_{>0}.
\tag{16.6}
$$

Inclusion of rational cells implies inclusion of their real closures, so $\ell_n$ is nondecreasing, $r_n$ is nonincreasing and $\ell_n\le r_m$ for all $n,m$. Both sequences are bounded by the first cell's endpoints. Their limits agree by (16.2), proving (16.3), finiteness and uniqueness. No thread at infinity is possible, since its first coordinate already has a finite upper endpoint.

If $t=0$, every $\ell_n=0$, so each coordinate is the unique initial cell; conversely these initial cells form a thread with limit zero. If $t>0$ is irrational, rationality of every cell endpoint forces $\ell_n<t<r_n$ at every stage. Thus the only possible coordinate is the cell whose associated real interval contains $t$. Those cells are nested and nonempty in the rational carrier and have limit $t$, giving existence and uniqueness.

For rational $t>0$, (16.6) supplies a stage $N$ at which $t$ is a cut and hence a cut at every later stage. At such a stage the only cell closures containing $t$ are the two adjacent ones, $[t,r_n)$ on the right and the left cell with upper endpoint $t$. Once either side is selected, nestedness forbids switching sides at a later stage. Before $t$ is a cut there is only one cell closure containing it. Selecting the same side at every stage with that cut therefore constructs exactly two threads. The cell immediately to the left exists even when $t$ is the smallest positive cut: it is then the initial open cell. This verifies all endpoint cases in (16.4).

The thread $\iota(x)$ is exactly $x^+$ for rational $x>0$, and once $x$ is a cut its lower endpoint is $x$ at every later stage. Conversely suppose $\ell_n=c>0$ for all $n\ge N$. The number $c$ is rational because it is a cell endpoint, and every one of those cells contains $c$. Nestedness puts $c$ in the earlier cells as well. Their widths tend to zero, so their common rational intersection is precisely $\{c\}$ and the thread is $\iota(c)$. If any other thread had a rational realization $x$, it would equal $\iota(x)$ and would satisfy this eventual positive stabilization. This proves (16.5) and emptiness for all the remaining threads. Finally, different rational $x<y$ are separated by a rational cut in $(x,y]$ occurring at some stage by (16.6); hence $\iota$ is injective. The interval-nesting argument is classical; its cut union and exact original-source image here are consequences of the fixed rational process. $\square$

**Definition 16.3 (split order and raw-floor comparison).** Order (16.4) by its numerical coordinate, and put $t^-<t^+$ for a rational coordinate $t$; $0^+$ is the least point. Only rational positive coordinates are split. This is a rationally split unbounded ray, not the compact double-arrow space obtained by splitting every real coordinate. Its interval notation below refers to this order, without an added point at infinity.

For comparison let $\mathscr R_n$ be the raw $s_n$-floor partition and let $\mathscr L^{\mathrm{raw}}_{\mathbf s}$ be its cell-inclusion inverse limit. The raw restriction sends a fine integer report $j$ to $\lfloor j/(s_m/s_n)\rfloor$ when $n\le m$. Call the chain **divisibility-cofinal** if every positive integer divides some $s_n$. This is stronger than being unbounded.

**Theorem 16.4 (when raw and predictive towers agree).** The numerical-limit classification of the raw tower has one thread at zero, two at exactly the positive rationals in $\bigcup_n\mathcal G_{s_n}$, and one at every other positive real coordinate. The canonical map from predictive threads to raw threads forgets predictive distinctions; it is bijective exactly when the chain is divisibility-cofinal. Under that condition there are explicit stage refinement maps in both directions, and the resulting limit bijection fixes every original rational source. In particular the factorial chain $s_n=(n+1)!$ has this property. For $s_n=2^n$, the predictive threads $(1/3)^-$ and $(1/3)^+$ have the same raw thread.

Proof. The raw partitions are nested and their widths tend to zero. Repeat the endpoint argument of Theorem 16.2 with cut union $\bigcup_n\mathcal G_{s_n}$. A coordinate in that union is permanently a cut after its first occurrence and has two consistent sides; any positive coordinate outside the union is strictly interior at every stage and has just one thread. This proves the raw classification directly, including positive rational coordinates absent from the raw union. Every predictive cell lies inside a raw cell at the same scale, defining the asserted forgetful map. Under the two classifications it preserves numerical coordinate and side whenever the raw tower records a side, and merges the two sides at each missing rational cut. Therefore it is bijective iff the raw union contains every positive rational. This is equivalent to divisibility cofinality: $1/d\in\mathcal G_{s_n}$ iff $d\mid s_n$.

For explicit interleaving, fix $i$. Cofinality supplies a $j\ge i$ with $\Lambda_{s_i}\mid s_j$. Theorem 15.2 then gives a map from the raw stage $\mathscr R_j$ to the predictive stage $\mathscr P_i$, sending each raw cell into its unique containing predictive cell. In the opposite direction $\mathscr P_i$ maps to $\mathscr R_i$ by grid inclusion. All maps are induced by the identity on the actual rational carrier. Compositions agree with the corresponding restriction maps: choose any rational in a finer input cell and compute its unique containing coarser cell. Independence of that choice follows from the stated refinements. Choosing a common larger index also proves independence of the permitted $j$. Applied coordinatewise, these maps define inverse maps on compatible families. Their composites are the identity because the same containing-cell calculation fixes each coordinate. Thus equality of completed carriers is accompanied here by proved refinement maps, not used to infer such maps without hypotheses.

Every integer divides a sufficiently large factorial; for the refinement of stage $i$, any factorial with index at least $s_i$ is already divisible by $\Lambda_{s_i}$. This proves the factorial assertion. In contrast $1/3$ belongs to no dyadic grid, whereas $1/3\in\mathcal C_4$ by (11.5). The raw dyadic limit has a single coordinate-$1/3$ thread, while the predictive dyadic limit has its two sides. This supplies the stated failure for an unbounded noncofinal chain. $\square$

## 17. Canonical actions, predecessor and the original four expressions

**Definition 17.1 (actions on compatible cells).** For $a\in\{L,R\}$ and $I\in\mathscr P_n$, define $U_{a,n}(I)$ to be the cell containing $f_a(x)$ for any $x\in I$. Corollary 11.3 makes this independent of $x$. These maps commute with restriction: choose a rational in the finer cell, apply the same action, and take containing cells at the two stages. Hence

$$
\widehat a((I_n)_n)=(U_{a,n}(I_n))_n
\tag{17.1}
$$

is a well-defined action on $\mathscr L_{\mathbf s}$. It extends the actual source action in the exact sense $\widehat a\circ\iota=\iota\circ f_a$. This definition uses the predictive tower. On a general raw tower no stagewise action or commutation law is presumed.

**Theorem 17.2 (action ranges and the complete incoming-edge criterion).** Under the classification (16.4), the actions in (17.1) are

$$
\begin{aligned}
\widehat L(0^+)&=0^+,&\widehat R(0^+)&=1^+,\\
\widehat L(t^{\pm})&=(t/(1+t))^{\pm},&
\widehat R(t^{\pm})&=(t+1)^{\pm}\quad(t\in\mathbb Q_{>0}),\\
\widehat L(t)&=t/(1+t),&\widehat R(t)&=t+1
\quad(t>0\text{ irrational}).
\end{aligned}
\tag{17.2}
$$

Both maps are injective. Their disjoint ranges, with the order of Definition 16.3, are

$$
\widehat L(\widehat X)=[0^+,1^-),\qquad
\widehat R(\widehat X)=[1^+,\infty).
\tag{17.3}
$$

The second notation means all points at least $1^+$, with no infinite endpoint adjoined. Every point except $1^-$ consequently has exactly one incoming named edge; $1^-$ has none. In particular the unique incoming edges at the special points are $0^+\xrightarrow{L}0^+$ and $0^+\xrightarrow{R}1^+$. The unique $\widehat L$ fixed point is $0^+$, and the original root is recovered from these named maps by

$$
\iota(1)=1^+=\widehat R(\text{the unique fixed point of }\widehat L).
\tag{17.4}
$$

Proof. Take a thread $(I_n)$ of limit $t$. For each $m$ choose a positive rational $x_m\in I_m$; for the thread $t^-$ choose it strictly below $t$, and for $t^+$ strictly above $t$. Such choices exist because the cells have nonempty interior. At an irrational limit the side of the choices is immaterial. For each fixed $n$, all $m\ge n$ have $x_m\in I_n$, so the cell of $f_a(x_m)$ at stage $n$ is exactly $U_{a,n}(I_n)$. The bound (16.2) gives $x_m\to t$. Both rational transformations extend continuously and strictly increasingly to finite nonnegative real inputs, taking zero to $0$ and $1$ respectively. At positive rational $t$ they preserve the chosen strict side; at zero both have only the right side. At irrational $t$ both transformed values are irrational, since the rational inverse formulas would otherwise make $t$ rational. The unique-thread and two-side classification now proves (17.2).

For $0<t<1$, the inverse of $L$ is $t/(1-t)$, a finite positive value, preserving irrationality or rational side as appropriate. It also has the inverse $0^+\mapsto0^+$. Every finite input has $L$-value strictly below $1$, so neither $1^-$ nor $1^+$ is in its range. This gives the first equality of (17.3). For a value strictly above $1$, the inverse of $R$ is subtraction of $1$, preserving side; $1^+$ has inverse $0^+$. There is no value with $R$-image $1^-$, since a positive input gives a value strictly above $1$ and the only zero-limit input is $0^+$. This gives the second equality. The inverse descriptions prove individual injectivity, range disjointness and the complete incoming-edge assertion. Finally no positive $t$ satisfies $t/(1+t)=t$, while $0^+$ is fixed. Equation (17.4) follows. Notice that the unattained limit $1^-$ of increasingly large $L$-inputs is not an extra action value: the carrier has no input at infinity. $\square$

**Theorem 17.3 (the original orbit retains exact four-view recovery).** Put

$$
\mathscr A=\{t^+:t\in\mathbb Q_{>0}\},\qquad
E(w)=\iota(B(w))\quad(w\in\{L,R\}^*).
\tag{17.5}
$$

Then $\mathscr A$ is exactly the finite forward orbit of the original root $1^+$, and $E$ is a bijection from the original chronological word set onto $\mathscr A$. On this orbit ROOT and PREDECESSOR of §5 hold for that same root and the restricted actions. Each of the original rational boundary, the limit boundary $E(w)$, original rooted named-incidence path, original literal chronology and original indexed prefix-memory table recovers all the others on their actual images.

On the whole $\widehat X$, the incoming-edge map is still injective, but ROOT for the original root $1^+$ fails and there is no global finite-word decoder satisfying the original root and extension equations. The rootless point $1^-$, the point $0^+$, and all irrational threads lie outside the original finite orbit. These are global enlargement obstructions, not counterexamples to the restricted recovery theorem.

Proof. Equation (17.2) preserves positive rational plus-points and intertwines their actions with the original $L/R$ actions. Theorem 6.2 reaches each positive rational from $1$ by one unique finite chronological word. Together with injectivity of $\iota$, this proves the orbit assertion and bijectivity of $E$. Within $\mathscr A$, both incoming ranges are disjoint and actionwise injective, and the only global predecessor of $1^+$ is $0^+\notin\mathscr A$. Thus the original root is excluded from the restricted incoming image. All other orbit points have their usual positive rational predecessor, so the criterion is exactly the original ROOT/PREDECESSOR criterion, with no replacement of its reachable domain.

For explicit correspondence, if $z\in\mathscr A$, recover the unique rational $c>0$ by (16.5) and define

$$
\begin{aligned}
D_E(z)&=\operatorname{dec}(c),\\
T_z&=D_E(z),\\
S_z&=S(D_E(z)),\\
M_z&=\bigl((k,\operatorname{enc}(D_E(z)|_k))\bigr)_{0\le k\le|D_E(z)|}.
\end{aligned}
\tag{17.6}
$$

Here $S$ is exactly §6's original root-oriented path with named edges, and $\operatorname{enc}$ returns its reduced positive pair. The scalar boundary is $c$, and $E(D_E(z))=z$. Conversely the original word constructs its pair, its thread, path and table. The path or table recovers that word by §§5–6. These equations prove all actual-image inverse transports. A table of prefix threads is also equivalent: apply $\iota$ rowwise to its pair ratios and retain its indices; conversely decode each realized row. In particular the same decoded word determines the original prefixes and their order, not just a numerical duration or a current post-probe history. The eventual condition in (16.5) gives a mathematical inverse on its promised image; it supplies no finite stopping certificate for acquiring that promise.

On the full carrier $1^+=\widehat R(0^+)$ violates root exclusion, although injectivity of the named predecessor map follows from (17.3). If a finite-word decoder $D$ on all $\widehat X$ satisfied $D(1^+)=\varepsilon$ and $D(\widehat a z)=D(z)a$ for both names and every $z$, the fixed point would give $D(0^+)=D(0^+)L$, contradicting finite word length. Already the incoming edge to the original root would force $\varepsilon=D(0^+)R$. Neither point is in $\mathscr A$ except the original root itself. Irrationality is preserved by the forward actions and by their positive inverse branches, so an irrational predecessor chain never reaches any rational root; no such point has a finite original rational history. This proves the stated global failures without classifying irrational components or changing the original root. $\square$

## 18. Finite cylinders and adaptive variable-scale acquisition

**Theorem 18.1 (finite coordinates do not certify original-source realization).** In $\mathscr L_{\mathbf s}$, every nonempty cylinder specified by finitely many exact stage coordinates contains infinitely many members of $\mathscr A$ and also members outside $\mathscr A$. More strongly, for every prescribed finite original chronological prefix $v$ and every integer $N\ge0$, that cylinder contains an $E(w)$ with $w$ extending $v$ and $|w|>N$. Thus finitely many predictive coordinates cannot certify membership or nonmembership in the actual-source image, cannot identify a unique original word under the rational-source promise, and cannot give a finite upper bound on its original depth.

Proof. Choose a thread in the cylinder and let $n$ be at least every specified index; with no specified coordinates take $n=0$. Its cell $I_n$ is a subset of all the specified cells and contains a nonempty open positive real interval $J$. Every positive rational $x\in J$ gives an actual thread $\iota(x)$ agreeing with all those coordinates. There are infinitely many such rationals and their histories are distinct by Theorem 6.2. Any irrational in $J$ gives a thread outside $\mathscr A$ with the same coordinates. One can also choose $t^-\notin\mathscr A$ for a rational $t\in J$: since $t$ is strictly interior at stage $n$, its left-side thread has that same coordinate and hence all the specified ones.

For the stronger assertion, extend $v$ to any finite word $v'$ of length greater than $N$. Alkauskas–Steuding, *Statistical properties of the Calkin–Wilf tree: real and $p$-adic distribution*, [arXiv:0801.0054v2](https://arxiv.org/html/0801.0054v2), §2, Corollary 3 and its continued-fraction proof, states that every nonempty positive open interval contains the endpoint of a continuation of any given finite Calkin–Wilf path. Its §1 children are exactly $a/b\mapsto a/(a+b),(a+b)/b$, read chronologically from the root, as here. Apply that existing density result to $v'$ and $J$. The resulting word $w$ extends $v'$ and therefore $v$, has length greater than $N$, and satisfies $B(w)\in J$. This proves the strengthened ambiguity using classical subtree density, not a new density theorem. The cylinder contains both membership classes and, under the rational-source promise, arbitrarily deep original candidates. No function of just those finite coordinates can make the contrary certifications. $\square$

**Assumption 18.2 (finite variable-scale observation on one original source).** Start with the same unknown original $x=B(w)\in\mathbb Q_{>0}$ at the original cut of Definition 10.1. Grant, conditionally, nondisturbing unclipped $q_D$ reads for every positive integer scale $D$ a controller requests. The deterministic controller may select $D$ adaptively from its acquired transcript, perform actual forward $L/R$ actions and arbitrary finite computation, retain its actual reports and actions, and choose when to stop. There is no common bound on scales, number of reads, action count, computation, storage or original depth. Each successful run must nevertheless finish all its computation, reads and actions in finite time and output the original target. The only source-dependent input is the acquired transcript. No reset, copy, inverse source action, original-word archive, exact target supplied as input, or access to an infinite thread is granted. The promise is the full positive rational source, without an original depth or denominator bound. Allowing a restricted installed scale menu is a special case of this stronger grant.

**Theorem 18.3 (finite adaptive observations leave a right neighborhood of original ambiguity).** Under Assumption 18.2, fix a run that terminates on an actual original $x>0$. There exists a real $\delta>0$ such that every rational $y\in[x,x+\delta)$ produces exactly the same complete acquired transcript, stopping decision and output. In every open subinterval of $(x,x+\delta)$ there are alternative originals extending any prescribed chronological prefix, at arbitrarily large original depth. Consequently no such deterministic policy can stop finitely and correctly recover the original word for every positive rational source. The same impossibility holds for each exact original four-view expression in Theorem 17.3, even though the entire mathematical tower separates all original sources.

Proof. List the finitely many reads on the terminating run. A read made after its known chronological probe prefix $u_i$, at its chosen integer scale $D_i$, returns

$$
q_{D_i}(f_{u_i}(x))
 =\lfloor D_i f_{u_i}(x)\rfloor=:k_i.
\tag{18.1}
$$

For fixed $u_i$, the nonnegative determinant-one matrix of Definition 10.1 makes $f_{u_i}$ continuous and strictly increasing at every positive input. Since

$$
k_i\le D_i f_{u_i}(x)<k_i+1,
\tag{18.2}
$$

continuity gives $\delta_i>0$ such that $D_i f_{u_i}(y)<k_i+1$ whenever $x\le y<x+\delta_i$. Monotonicity gives the other inequality $D_i f_{u_i}(y)\ge k_i$ on that interval, including when the original input is exactly on a floor threshold. Hence the report remains $k_i$. Let $\delta$ be the minimum of these finitely many positive $\delta_i$; if there are no reads take any positive $\delta$.

Now replay the controller from an original $y\in[x,x+\delta)$. Before its first read, its decisions and actions agree because it has no different source-dependent input. The first read has the fixed prefix and scale listed above, so it gives the same report. Inductively equal previous reports and known actions force the same computations, next scale, probe actions and stop choice, and the corresponding read agrees by the same bound. Deterministic computations between reads therefore terminate exactly as on the fixed run. This proves transcript and output equality without presuming that scales on different branches would have been bounded or predetermined. The minimum is taken only over one completed branch; adaptivity is handled by equality of its prefixes.

Every positive open subinterval of the resulting right neighborhood contains a descendant of any finite chronological prefix by the same Calkin–Wilf density corollary used in Theorem 18.1. Extending that prescribed prefix beyond any requested depth before applying density gives arbitrarily deep alternatives. Choose one such rational $y\ne x$. Its unique original word differs from that of $x$, yet the policy returns the same output. If a policy were correct on every original source and terminated on each, applying this argument to any one of its runs would contradict correctness on this alternative. The original pair boundary, oriented named path, literal chronology and indexed prefix table each determine the original word, and the word constructs each, by Theorem 17.3. Composing a hypothetical correct acquisition of any one with its word decoder therefore gives the same contradiction. This proves the four-view claim at the unchanged original cut. $\square$

**Proposition 18.4 (finite predictive-class queries do not evade the obstruction).** Suppose a finite adaptive policy is additionally described as requesting an exact scale-$M$ predictive-class coordinate at its current cut, with the scale chosen adaptively. If every such request is implemented by a supplied current floor report at $D$ satisfying $\Lambda_M\mid D$ and the factor of Theorem 15.2, the original-history and four-view impossibility of Theorem 18.3 still applies. Merely receiving a finite set of compatible coordinates cannot certify eventual positive stabilization in (16.5).

Proof. Replace each requested class coordinate by its one stipulated floor read and deterministic factor computation. A terminating run remains finite and satisfies Assumption 18.2, so Theorem 18.3 applies. Independently Theorem 18.1 provides both actual and nonactual threads with every nonempty finite coordinate specification; hence no such specification can imply the eventual property that distinguishes the actual image. With an explicit promise that the source is rational, the semantic inverse (17.6) exists on the full thread, but the same finite cylinder still contains infinitely many alternative rational histories. Neither argument grants an infinite-thread query or treats eventual stabilization as a decidable finite stopping test. $\square$

## 19. Mathematical supplier contracts for the rational limit

**Definition 19.1 (source and antecedent correspondence).** The hypotheses and conclusions used in §§15–18 have the following fixed mathematical roles. The synthesis is `repo-derived` ordinary mathematics for the source of §§6 and 11, without a worldwide novelty assertion. Classical modular arithmetic, nested interval reasoning, one-sided floor continuity and Calkin–Wilf subtree density are supporting mathematics within those derivations.

| Supplier | Correspondence and scope |
| --- | --- |
| Theorems 11.2 and 12.2 of this volume | The exact cut set, finite core $ah+bj=M$, endpoint convention, denominator bound and divisibility refinement supply the partitions in §16. Arithmetic saturation proves their rational cut union, rather than assuming that an arbitrary increasing scale is a raw divisibility refinement. |
| [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `wordMatrix`, `unimodular_wordMatrix`, `wordMatrix_lower_right_pos`; [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix` | The nonnegative generators, determinant one, positive lower-right entry and natural unimodular factorization are the matrix antecedents already used in §§10–11. The chronological response uses `wordMatrix` on the reversed probe word. The reduced lower-row statement is not a replacement for reducedness of the source pair. |
| [CompletionIsomorphismCriterion](../../../D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion.lean), `InverseStageSystem`, `CompatibleStageFamily`, `completion_map_equiv_iff` | The declared restriction identity and composition laws, source projections and compatibility equations are prerequisites. Its equivalence requires joint separation and a unique source realization for every compatible family. Here actual cells and containing-cell maps provide those structural data; (16.5) proves separation but refutes universal source realization. The criterion therefore does not identify the original rational carrier with all of $\widehat X$. |
| [InverseLimitCompletion](../../../D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean), `ThreadComplete`, `SeparatesStates`, `stateThread_bijective_iff_complete_and_separates` | `ThreadComplete` requires every compatible thread to be realized by a source state. It is distinct from the condition that every finite coordinate has a representative. The explicit nonactual threads in (16.4) fail this premise for the original source. |
| [ItineraryCompletion](../../../D5/S3/ObserverMemory/Prediction/ItineraryCompletion.lean), `completeItinerary`, `ItineraryRange`; [BehaviorCompletionUniqueStability](../../../D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionUniqueStability.lean), `behavior_completion_has_unique_induced_update` | `ItineraryRange` is the actual range of the complete future itinerary for one specified update, and the unique induced update theorem acts on that range. It does not adjoin every compatible finite family. The two-action maps (17.1) instead come from the explicitly proved congruences and restrictions of this source. An actual behavior quotient and a point-adjoining inverse limit are separate carriers. |
| Alkauskas–Steuding, [arXiv:0801.0054v2](https://arxiv.org/html/0801.0054v2), §1 and §2, Corollary 3 | The same root and chronological child formulas, together with density of continuations of any finite path in every nonempty positive open interval, supply the prescribed-prefix part of Theorems 18.1 and 18.3. Only this deterministic existence statement is used; no probability, uniform hitting-time or finite acquisition bound is inferred from the paper's random-walk results. |

These are correspondences to the stated source declarations and literature hypotheses. They assert no new kernel check of the rational completion, its source-image criterion, its predecessor graph or its acquisition obstruction.

**Definition 19.2 (remaining recovery conditions).** Exact recovery of the original four mathematical expressions from a full predictive thread is conditional on membership in the actual finite orbit $\mathscr A$, equivalently eventual positive lower-endpoint stabilization. The original root is $1^+$ throughout; $1^-$ is the ambient graph's unique point without an incoming edge and does not replace it. Semantic forward compatibility on $\widehat X$ preserves the source orbit and its exact histories, while global root exclusion and a global original-word decoder fail as stated in §17. Acquisition from finitely many installed reads remains obstructed on the unrestricted source even with adaptive scales. A finite original prior, a distinct equality or certification port, an infinite supplied thread, changed allowed operations, or a different target would impose a different recovery problem. None is supplied by the limit construction. Spatial incidence, ordered prefixes and memory remain the expressions of §§5–6; no metric spacetime, physical duration or physical apparatus law is asserted.

## 追加锚（本行以下为增补区）

## 20. Marked anchors and the exact finite-history fibers

**Definition 20.1 (one joint source of anchored histories).** Retain the split carrier $\widehat X$ of (16.4), its order and the two total named actions of (17.2). Write $U_L=\widehat L$, $U_R=\widehat R$. For a chronological word $w=a_1\cdots a_n$, put

$$
U_w=U_{a_n}\circ\cdots\circ U_{a_1},\qquad
U_{uv}=U_v\circ U_u,\qquad U_\varepsilon=\operatorname{id}.
\tag{20.1}
$$

The mathematical comparison source is $\mathcal H=\widehat X\times\{L,R\}^*$, with a specified anchor $a$ and the finite word executed from it. Its expressions are the anchored endpoint $E(a,w)=(a,U_w(a))$, literal chronology $T(a,w)=(a,w)$, the occurrence path $S(a,w)$ of Definition 5.4 with root state $a$, and the indexed prefix table $M_*(a,w)=((j,U_{w|_j}(a)))_{j=0}^{|w|}$. The table retains its row indices and the root row. Adjacent states determine their named edge by Theorem 17.2, even at the $0^+$ loop, so the table and the occurrence path each recover $(a,w)$. All memory records below are specified deterministic functions on this same $\mathcal H$; all inverse maps are on their actual images. Restricting to one declared anchor means $\mathcal H_a=\{a\}\times\{L,R\}^*$.

These are mathematical anchored histories on an ambient carrier. The original actual source remains exactly $\mathcal H_{1^+}$ with endpoint orbit $\mathscr A$ in (17.5). Declaring another anchor does not make it an original rational realization. An exact supplied anchor or endpoint below is an input to a mathematical inverse, with no finite acquisition or computation claim.

Let $P$ be the partial predecessor on $\widehat X$, undefined only at $1^-$. Its incoming name $\lambda(z)$ satisfies $z=U_{\lambda(z)}(Pz)$. In numerical coordinates,

$$
\begin{aligned}
P(0^+)&=0^+,&\lambda(0^+)&=L,\\
P(1^+)&=0^+,&\lambda(1^+)&=R,\\
P(t)&=t/(1-t),&\lambda(t)&=L\quad(0<t<1),\\
P(t)&=t-1,&\lambda(t)&=R\quad(t>1).
\end{aligned}
\tag{20.2}
$$

For rational coordinates the last two formulas preserve the displayed $-$ or $+$ side. A **cyclic anchor** admits a nonempty return word $c$ with $U_c(a)=a$; a **free anchor** admits none. A component means a component of the graph after forgetting edge orientation, while a directed cycle retains the named directed edges.

**Theorem 20.2 (source-specific anchored recovery and complete ambiguity).** Define

$$
\mathscr C=\{0^+\}\ \sqcup\
\{t>0:t\text{ is a quadratic irrational and its algebraic conjugate }t'<0\}.
\tag{20.3}
$$

For every declared anchor $a$, the following are equivalent: $a\notin\mathscr C$; $a$ is free; the endpoint map on $\mathcal H_a$ is injective; and $E,T,S,M_*$ restricted to $\mathcal H_a$ are pairwise mutually recoverable. Thus both rational sides, including $1^-$ and the original $1^+$, permit finite-word recovery; the remaining free anchors are the positive nonquadratic irrationals and the positive quadratic irrationals with positive conjugate.

For a cyclic anchor let $c_a$ be its shortest nonempty chronological return word and $p_a=|c_a|$. This word is unique, every return word is a power of $c_a$, and $p_{0^+}=1$, with $c_{0^+}=L$. Every positive irrational cyclic anchor has $p_a\ge2$. For every $z\in\widehat X$, put

$$
\mathcal F_a(z)=\{w:U_w(a)=z\}.
\tag{20.4}
$$

An unreachable endpoint has empty fiber. At a reachable endpoint let $v_{a,z}$ be the unique shortest reaching word and $d_{a,z}=|v_{a,z}|$. The entire fiber, including endpoints reached after leaving a cycle, is

$$
\mathcal F_a(z)=
\begin{cases}
\{v_{a,z}\},&a\text{ free},\\
\{c_a^k v_{a,z}:k\in\mathbb N\},&a\text{ cyclic}.
\end{cases}
\tag{20.5}
$$

Equivalently the possible starting occurrences in the endpoint's predecessor record are

$$
\{n:P^n z\text{ is defined and equals }a\}
 =\{d_{a,z}\}\quad\text{or}\quad
 \{d_{a,z}+kp_a:k\in\mathbb N\},
\tag{20.6}
$$

respectively. In particular a cyclic anchor loses finite-history information at every reachable endpoint, and a free anchor loses none, even when its component contains a directed cycle.

Proof. First apply the unique incoming named-edge statement of Theorem 17.2. If $U_u(a)=U_v(a)$, peel the last incoming edge from both sides as long as both words remain nonempty. The names and predecessor states must agree at each step. Equal lengths force $u=v$. Otherwise, say $|u|>|v|$, one obtains $u=rv$ with a nonempty return $U_r(a)=a$. Conversely any return gives a collision between $\varepsilon$ and $r$, and between $v$ and $rv$ for every $v$. This proves the recovery iff the anchor is free. The other three views are injective on $\mathcal H_a$ by Definition 20.1, so it also proves their asserted equivalence with $E$. In §5's terminology PREDECESSOR always holds on this orbit, and ROOT fails exactly when the anchor itself has a return within that orbit. An incoming edge from outside it does not violate the restricted ROOT condition.

We identify those returns using the classical quadratic-surd recurrence as an antecedent, not as a new periodicity theorem. On finite numerical coordinates a pure $R^m$ acts by $t\mapsto t+m$ and has no fixed point, while a pure $L^m$ acts by $t\mapsto t/(mt+1)$ and fixes only $0$. A word containing both letters has a matrix

$$
A_w=G_{a_n}\cdots G_{a_1}
 =\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix},
\quad \alpha,\beta,\gamma,\delta>0,\quad
\alpha\delta-\beta\gamma=1.
\tag{20.7}
$$

Indeed the product containing the first occurrence of both generators has all four entries positive, and subsequent multiplication preserves positivity. A fixed positive coordinate solves

$$
\gamma t^2+(\delta-\alpha)t-\beta=0.
\tag{20.8}
$$

Its roots have product $-\beta/\gamma<0$. The discriminant is $(\alpha+\delta)^2-4$. The integral trace $h=\alpha+\delta$ is at least three: trace two would force $\alpha=\delta=1$ and contradict the positive off-diagonal product in the determinant equation. For $h\ge3$ one has $(h-1)^2<h^2-4<h^2$, so the discriminant is not a square. Thus the positive root is quadratic irrational with negative conjugate. No positive rational coordinate, on either split side, can be fixed. Zero itself has just its $L$ loop. This proves necessity in (20.3), without inferring evaluation freeness from any matrix-generation or matrix-freeness assertion.

For sufficiency take a positive quadratic irrational $t$ with $t'<0$, and an integral irreducible quadratic $Ax^2+Bx+C$ for it, normalized with $A>0$. Then $C<0$, and

$$
\Delta=B^2-4AC,\qquad
 t=\frac{\sqrt\Delta-B}{2A},\qquad
 (N,p,q)=(\Delta,-B,2A).
\tag{20.9}
$$

Here $\Delta$ is a positive nonsquare integer, $p^2<N$, $q>0$, and $q\mid N-p^2$ because $N-p^2=-4AC$. These are precisely the standing hypotheses in §3 of Lionel Ponton, *The Calkin-Wilf tree of a quadratic surd*, [arXiv:1709.00473v2](https://arxiv.org/html/1709.00473v2). Its Definition 1 selects the left-positive path in the tree with children $x/(x+1)$ and $x+1$. Its §4, Proposition 3 says that this path is purely periodic, so a positive-length path from its root returns to $t$ itself. The path letters $\ell,r$ are our chronological $L,R$, with the same child functions, not the reversed Stern–Brocot chart. At an irrational coordinate the split carrier has only one point, so this is a return in $\widehat X$. No assertion for arbitrary positive quadratics is being imported: (20.9) verifies the negative-conjugate hypotheses, and (20.8) excludes the positive-conjugate case. This proves (20.3) and the classification of free anchors. Neither $L$ nor $R$ alone fixes a positive irrational, which also proves $p_a\ge2$.

For completeness prove the fiber formula, using the elementary lap-count mechanism already present for finite graphs in [Typed residual cocycles](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md), §§7.2–7.5. Here the ambient graph is infinite, but uniqueness of the incoming edge makes the normal form more restrictive. At each fixed length there is at most one word reaching $z$, since peeling determines that entire word. A reachable endpoint therefore has a unique least-length word $v=v_{a,z}$. Comparing any longer reaching word with $v$ by peeling gives $w=rv$ with $r$ a return. For a cyclic anchor choose a least positive return length $p$ and its unique word $c$. Comparing any return $r$ of length at least $p$ with $c$ gives $r=sc$, where $s$ is another return or empty. Repeating removes blocks of length $p$; a remaining positive return of length less than $p$ would contradict minimality. Thus $r=c^k$, which proves (20.5); conversely all its listed words reach $z$. Peeling $n$ steps from an endpoint is exactly reversing a reaching word of length $n$, so (20.6) follows, including halting predecessor chains.

The cycle visited by $c$ has no repeated vertex before its return to $a$: a shorter internal repetition and unique predecessors would force a return of $a$ of smaller length. Every cycle vertex has its incoming edge occupied by that cycle. Therefore no path from outside a cycle can enter it. In particular a free anchor cannot reach a directed cycle, although it can lie on a branch leaving a cycle. An endpoint reached by leaving a cycle cannot reenter it; its repetitions in (20.5) are laps made at the anchor before the exit. This establishes the component distinction without a classification of all irrational components. $\square$

**Proposition 20.3 (the golden-ratio separating pair).** Let $\phi=(1+\sqrt5)/2$. The anchor $\phi$ is cyclic with $c_\phi=LR$ and $p_\phi=2$, whereas $\phi+1$ is free. They lie in the same component, and the latter has an infinite predecessor record that is eventually periodic. More precisely,

$$
U_L(\phi)=\phi-1,\quad U_R(\phi-1)=\phi,
\quad U_R(\phi)=\phi+1,
\quad \mathcal F_\phi(\phi+1)=\{(LR)^kR:k\ge0\}.
\tag{20.10}
$$

From the declared anchor $\phi+1$, every reachable endpoint instead has a singleton fiber.

Proof. The identities follow from $\phi^2=\phi+1$. They give a two-edge cycle, and no one-edge return is possible at a positive irrational. The conjugate $\phi'=(1-\sqrt5)/2$ is negative, but the conjugate of $\phi+1$ is $(3-\sqrt5)/2>0$, so Theorem 20.2 applies to both. The shortest word from $\phi$ to $\phi+1$ is $R$, giving the displayed fiber. The predecessor of $\phi+1$ is $\phi$, after which the predecessor states alternate between $\phi-1$ and $\phi$. Thus an infinite, even eventually periodic, unmarked past does not force a return to the marked anchor. The two anchors are joined by the displayed $R$ edge. $\square$

## 21. Complete predecessor records and the missing occurrence

**Definition 21.1 (unmarked maximal records).** Starting from $z_0=z$, repeatedly set $z_{n+1}=Pz_n$ while defined. The full state record retains this ordered sequence, including $z_0$, with a halt marker $!$ if the last state is $1^-$. The full name record is

$$
\mathcal N(z)=
\begin{cases}
(\lambda(z_0),\ldots,\lambda(z_{m-1}),!),&P^m z=1^-,\\
(\lambda(z_n))_{n\ge0},&\text{the predecessor sequence is infinite}.
\end{cases}
\tag{21.1}
$$

These names are read backwards from the endpoint; they are not the chronological word from an anchor. A full record has its endpoint index zero but no selected earlier occurrence as the start of a history. On $\mathcal H$ compare the unmarked views $(a,\mathcal N(U_w(a)))$ and $(a,\text{full state record of }U_w(a))$. The anchor value is supplied in both, while its occurrence index is not.

**Theorem 21.2 (endpoint sufficiency on the split carrier).** The map $z\mapsto\mathcal N(z)$ is a bijection from $\widehat X$ to its actual record image. Consequently, with the anchor retained, either full unmarked record has exactly the same history fibers as $E$. It determines the endpoint, its unique maximal predecessor sequence and every index at which the anchor occurs. It recovers the finite anchored history exactly for free anchors. For a cyclic anchor it fails to choose among all the occurrences $d_{a,z}+kp_a$, and hence among all words in (20.5), even when every predecessor state and name is supplied.

Proof. The classification of actual records must include the split rational sides. For $z=t^-$ with $t>0$ rational, the subtractive Euclidean descent of Theorem 6.2, preserving the minus side by (20.2), reaches $1^-$ in finitely many steps and halts there. These are exactly the finite records: any point reaching $1^-$ is a finite forward image of it, and these images remain positive rational minus-points. Reverse the listed names and execute that chronological word from the fixed terminal state $1^-$; this reconstructs the endpoint uniquely. The halt marker is part of this information, including the record consisting only of $!$ at $1^-$ itself.

For $t^+$ the same descent reaches $1^+$, then $0^+$, then repeats $0^+$ forever with name $L$. The zero point itself has record $LLLL\cdots$. Conversely an actual infinite record that is eventually all $L$ must reach $0^+$: if its state at the beginning of that tail had positive coordinate $x$, repeated inverse-$L$ steps would have numerical value $x/(1-nx)$ while defined, which cannot remain finite and positive for every $n$. The only zero-coordinate point is $0^+$. Thus a finite prefix of the record, reversed and executed from $0^+$, reconstructs the endpoint. This covers exactly zero and the positive rational plus-points. The tail is not a halt marker and cannot be substituted for one; it distinguishes the plus-points from the rational minus-points.

All other endpoints are positive irrational points and have infinite predecessor records. Such a record is not eventually $L$ by the preceding argument and cannot be eventually $R$, since repeated inverse-$R$ steps subtract one and cannot remain positive forever. Hence both letters occur infinitely often. To prove uniqueness from its names $b_0,b_1,\ldots$, without assuming a binary-shift identification, form

$$
A_n=G_{b_0}\cdots G_{b_{n-1}}
 =\begin{pmatrix}\alpha_n&\beta_n\\\gamma_n&\delta_n\end{pmatrix}.
\tag{21.2}
$$

The endpoint is the result of applying the first incoming name to the next predecessor, and so forth. Its numerical coordinate therefore belongs, for each $n$ with $\gamma_n>0$, to the closed real interval

$$
\left[\frac{\beta_n}{\delta_n},
      \frac{\alpha_n}{\gamma_n}\right],
\qquad
\frac{\alpha_n}{\gamma_n}-\frac{\beta_n}{\delta_n}
 =\frac1{\gamma_n\delta_n}.
\tag{21.3}
$$

This follows by letting the remaining nonnegative numerical input range from zero to arbitrarily large finite values in its increasing determinant-one fractional map; only containment in the closure is needed. Right multiplication by $G_L$ changes the lower row $(\gamma,\delta)$ to $(\gamma+\delta,\delta)$, and right multiplication by $G_R$ changes it to $(\gamma,\gamma+\delta)$. Starting from $(0,1)$, after the first $L$ both entries are positive. Infinitely many occurrences of each letter make their product tend to infinity. The widths in (21.3) tend to zero, so two endpoints with these same names have the same numerical coordinate. Both endpoints are irrational in this case and (16.4) assigns only one split point to that coordinate. They are therefore equal.

The three cases exhaust actual records. This proves endpoint sufficiency including zero, the rational sides and termination. It asserts no surjectivity onto an arbitrary binary code space: for instance $RRRR\cdots$ is not an actual predecessor record. The endpoint determines the full records by (20.2), and the state record includes that endpoint. Thus both records and the endpoint recover each other on actual images. Pulling these maps back to the common source $\mathcal H$ gives precisely the fibers (20.5). Formula (20.6) then gives every possible starting occurrence, but nothing in the unmarked record selects one. $\square$

**Theorem 21.3 (exact record condition for chronological memory).** Let $Q:\mathcal H\to\mathcal Q$ be any deterministic supplementary record and retain the exact anchored endpoint as well. The observation

$$
R_Q(a,w)=(a,U_w(a),Q(a,w))
\tag{21.4}
$$

recovers $T,S,M_*$ on its actual image if and only if, for every cyclic anchor $a$ and every reachable $z$, the function

$$
k\longmapsto Q(a,c_a^k v_{a,z})\quad(k\in\mathbb N)
\tag{21.5}
$$

is injective. Free anchors impose no further within-endpoint condition. The same assertion holds if the exact endpoint is replaced by either complete unmarked record of Definition 21.1. A marked starting index $n=d_{a,z}+kp_a$ or its lap number $k$ is sufficient, whereas a supplementary function only of the unmarked endpoint record cannot repair a cyclic fiber.

For an arbitrary memory view $(a,M(a,w))$ without a separately supplied endpoint, exact history recovery is equivalent to both of the following: that memory determines $E$ on its actual image, and that it separates all the occurrences in (20.5). In the free regime the first condition alone suffices; in the cyclic regime it must be supplemented by the injectivity condition on the whole lap sequence.

Proof. Equality of (21.4) first fixes $a$ and $z$. Equation (20.5) then lists every remaining possibility, so injectivity on that list is necessary and sufficient. In the cyclic case the list is parameterized bijectively by $k$; in the free case it has one member. Selecting $n$ permits peeling $n$ steps and reversing the names to recover $w$; selecting $k$ determines $n$ and has the same effect. A function of an unmarked endpoint record is constant on each entire list and therefore fails (21.5). Theorem 21.2 justifies replacing the endpoint by that record. Finally an injective memory determines the endpoint because it determines the history. Conversely endpoint determination reduces equal memory values to one fiber, where the second condition separates them. The reconstructed finite word constructs all indexed earlier prefix records and the oriented occurrence path. No retention interface or effective decoder is implicit in these actual-image inverses. $\square$

## 22. Sharp supplementary ranges with the anchor and endpoint supplied

**Proposition 22.1 (exact finite-horizon and unrestricted label requirements).** Supply an exact anchor $a$, an exact endpoint $z$, and a horizon $N\in\mathbb N$, with the promise that a finite history of length at most $N$ from $a$ ended at $z$. Count only the range of a supplementary deterministic label $Q$ accompanying those supplied inputs. For a reachable $z$ with $d_{a,z}\le N$, the sharp number of labels required on that endpoint fiber is

$$
m_N(a,z)=
\begin{cases}
1,&a\text{ free},\\
1+\left\lfloor\dfrac{N-d_{a,z}}{p_a}\right\rfloor,
 &a\text{ cyclic}.
\end{cases}
\tag{22.1}
$$

The fiber is empty when $z$ is unreachable or $d_{a,z}>N$. A single label alphabet reused across all endpoints for a fixed supplied anchor has sharp size $1$ for a free anchor, and $1+\lfloor N/p_a\rfloor$ for a cyclic anchor. Uniformly over all ambient anchors the sharp size is $N+1$, attained at $a=z=0^+$. If anchors are restricted to positive irrational points, it is $1+\lfloor N/2\rfloor$, attained at $a=z=\phi$. These are range cardinalities; a fixed-length binary label needs the ceiling of their base-two logarithms.

Without a finite horizon, no finite supplementary range recovers all finite histories from even one fixed cyclic anchor, even with exact $a,z$ supplied. A countably infinite range suffices there, by the lap number. A free anchor needs just the single constant label for every finite history.

Proof. Intersect (20.5) with $|w|\le N$. In the cyclic case its distinct words have lengths $d_{a,z}+kp_a$, so the permitted integers are exactly $0\le k\le\lfloor(N-d_{a,z})/p_a\rfloor$. The free case has just its one word. Recovery needs distinct supplementary labels on this fiber by Theorem 21.3 and the pigeonhole principle; assigning those $k$ values is sufficient. For a fixed cyclic anchor the largest fiber occurs at $z=a$, where $d_{a,a}=0$, and the same $k$ alphabet works at all other endpoints. For free anchors the unique label works everywhere. Since every $p_a\ge1$, the all-anchor maximum is at most $N+1$, with equality at the $0^+$ loop. For positive irrational cyclic anchors $p_a\ge2$, and the period-two anchor $\phi$ gives equality in that restricted maximum; free anchors do not increase it. Arbitrarily many laps at $z=a$ give an infinite fiber when the horizon is removed, excluding every fixed finite label range, while $k\in\mathbb N$ still suffices. $\square$

The counting mechanism is the classical lap ambiguity and finite-range obstruction already used in [Typed residual cocycles](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md), §§7.2–7.5. Its parameters here are the marked anchor, its actual primitive return length and the endpoint's shortest reaching depth in the split action graph. These counts include neither the information in the exact anchor and endpoint nor computation, representation or acquisition of them. In particular a one-label supplement at a free irrational anchor does not assert that an exact irrational endpoint occupies finite apparatus memory or that its finite history can be acquired from finitely many predictive coordinates.

## 23. Finite predictive coordinates cannot recognize the ambient recovery regime

**Theorem 23.1 (mixed cylinders and finite adaptive non-certifiability).** For the predictive tower of Definition 16.1, every nonempty cylinder specified by finitely many exact coordinates contains both a free anchor and a cyclic anchor. Consequently no deterministic rule whose only source-dependent inputs are finitely many adaptively chosen predictive coordinates of an unknown ambient anchor can terminate with a correct certificate of either regime on any terminating branch that it claims to certify. This statement permits arbitrary coordinate indices and no common bound on the number of queries across branches, but a terminating branch has finitely many queries and computations.

Here the anchor is observed through those coordinates; its exact value is not additionally supplied as an input. Under the original promise $a\in\mathscr A$, the regime predicate is instead constant: every such rational plus-anchor is free. Thus this is an ambient regime-recognition limitation, neither a counterexample to original four-view recovery nor a replacement for the original-history acquisition obstruction of Theorem 18.3.

Proof. Choose a member of the nonempty cylinder, and take a stage $n$ at least all its specified indices (or $n=0$ for an unrestricted cylinder). The associated real interval of its cell $I_n$ has a nonempty positive open interior $J$ by Definition 16.1. Any thread with numerical coordinate strictly inside $J$ has that same stage coordinate, and hence all the specified earlier coordinates. Choose a positive rational $r\in J$. Its thread $r^+$ is a free anchor by Theorem 20.2. To choose a cyclic one, use density of positive rational multiples of $\sqrt2$: there is a rational $u>0$ with $u\sqrt2\in J$, since $J/\sqrt2$ is a nonempty positive open interval. This point is quadratic irrational with conjugate $-u\sqrt2<0$, hence cyclic by (20.3). The same cell therefore contains both regimes; there is no rational-side ambiguity at either chosen interior coordinate.

For an adaptive rule fix one terminating branch. Its finite list of queried indices and answers specifies a nonempty cylinder. Every anchor in it produces the same queries and answers inductively: the next index, finite computation and stopping decision are determined by the previous identical answers. Both regime classes occur in this cylinder by the first part. The returned certificate is therefore false for one of them. This argument uses a single finite branch and does not presume a uniform bound on query indices or run lengths. On the promised original source all anchors are positive rational plus-points and (20.3) excludes every one from $\mathscr C$, so constant certification of freeness there is valid. It still identifies no unique original word from finite coordinates; Theorems 18.1–18.3 address that separate acquisition target. $\square$

**Definition 23.2 (antecedents and remaining scope).** The ordinary mathematical increment is the anchored finite-history classification and its complete memory fibers for this particular split predictive completion, together with the split-carrier endpoint sufficiency of maximal predecessor names and the resulting mixed-cylinder regime obstruction. The recurrence of positive quadratic surds with negative conjugate is a literature-attested antecedent, with its exact parameter substitution given in (20.9). The general cancellation, cycle-lap and finite-range arguments are elementary antecedents, not newly discovered mathematics; §§7.2–7.5 of the cited residual-cocycle volume already give their finite-graph counterparts. The use of actual predictive interval interiors comes from §§11–12 and 16–18 here. These source-specific conclusions are `repo-derived` ordinary proofs, without a worldwide novelty assertion or a global classification of modular components.

The following supplier statements are cited at their source-inspection scope only:

| Supplier | Exact correspondence and limit |
| --- | --- |
| [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `wordMatrix`, `unimodular_wordMatrix`; [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix` | The generators are $G_L,G_R$ with `false`, `true` respectively. The chronological matrix in (20.7) is `wordMatrix` of the reversed chronological word; the incoming-name prefix in (21.2) has its displayed direct matrix order. The determinant identity and nonnegative matrix generation are supplier facts; generation is not evaluation freeness at an anchor. The fixed-point calculation and the checked literature correspondence establish the anchor distinction. |
| [BackwardOrbitCore](../../../D5/S3/ObserverMemory/InverseLimits/BackwardOrbitCore.lean), `backward_orbit_coordinate_periodic`, `backward_orbit_eval_zero_bijective` | These require a finite carrier and one self-map. The infinite split carrier and its partial named predecessor do not meet those hypotheses. Infinite predecessor records here therefore imply no periodic-core conclusion from that supplier; $\phi+1$ already separates an eventually periodic record from membership of the anchor in a cycle. |
| [CompletionIsomorphismCriterion](../../../D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion.lean), `completion_map_equiv_iff` | Its equivalence requires joint separation and unique actual-source realization of every compatible thread. The original rational source is separated, but its completion has the nonactual points of (16.4)–(16.5). A declared ambient anchor is not an additional original-source realization. |
| [QuadraticImpliesPeriodic](../../../D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic.lean), `quadratic_irrational_eventually_periodic_of_bounded_complete_quotients` | It assumes `BoundedCompleteQuotientCertificate`. No unconditional kernel Lagrange statement or certificate for these anchors is inferred. The return used in (20.9) comes from Ponton's specific forward left-positive-path theorem, with the paper's hypotheses explicitly verified. |

No fresh kernel verification of §§20–23 is asserted. The mathematical inverses, including occurrence selection and the cardinalities of supplementary ranges, preserve the common-source, action, exactness and resource contracts stated above. They do not provide a code-space topological equivalence, an acquisition interface, physical memory bounds or a metric or physical spacetime interpretation.

## 追加锚（本行以下为增补区）

## 24. Effective stopping presentations at the unchanged original cut

**Assumption 24.1 (public prior, finite target and effective controller).** Retain the original positive rational $x=B(w)$, the root $1$, chronological $L(x)=x/(1+x)$ and $R(x)=x+1$, and the exact nondisturbing ports of Assumption 18.2. Every requested positive integer scale is conditionally supplied, each reached service finishes, and its complete integer report is finitely encoded. A public presentation $\pi$, fixed independently of the unknown $x$, specifies a promised domain $P_\pi\subseteq\mathbb Q_{>0}$ and a single-valued original target $\tau_\pi:P_\pi\to\{0,1\}^*$. Distinct target values have specified distinct finite encodings. The presentation need not decide membership in $P_\pi$ or supply a procedure deciding which observations certify a target.

Acquisition means the existence, for this fixed presentation, of one effective deterministic finite program that terminates with $\tau_\pi(x)$ for every $x\in P_\pi$. Each individual run uses finitely many services, actions, computation steps and storage cells and finishes its finite output. There is no common bound on these quantities, scales or operand widths. A stationary controller performs no source action; a forward controller may perform the actual chronological actions. The target in both cases remains $\tau_\pi$ of the original $x$, not a target at the attained cut. Initial data, program and any declared auxiliary access are independent of $x$. There is no free exact original input, source-dependent advice, timing observation, inverse action, reset, copy, archive, or infinite-thread port. Mathematical simulation using a known rational in a reduction below is not an additional source interface.

For comparison only, fix an arbitrary set $O\subseteq\mathbb N$ independently of $x$. An $O$-controller is a finite oracle program with membership access to this same fixed $O$; every terminating run makes finitely many such queries. All definitions below have this explicitly conditional relativization. The actual ordinary model has $O=\varnothing$ and is granted no oracle. The assertion $H\le_T O$ means that one finite $O$-program decides membership in $H$ on every integer input, with pointwise finite computation.

**Definition 24.2 (labeled observation cells and their presentation).** A finite observation description is a list $s=((D_1,k_1),\ldots,(D_r,k_r))$ with $D_i\ge1$ and $k_i\ge0$. Its ambient and relative cells are

$$
\begin{aligned}
C(s)&=\{y\in\mathbb Q_{>0}:q_{D_i}(y)=k_i\text{ for all }i\},\\
C_\pi(s)&=P_\pi\cap C(s).
\end{aligned}
\tag{24.1}
$$

A single ambient cell is $[k/D,(k+1)/D)\cap\mathbb Q_{>0}$; for $k=0$ its lower endpoint is excluded by positivity. The empty list describes all positive rationals. Contradictory lists and lists missing the prior may describe empty relative cells. An $O$-computably enumerable family $\mathcal E_\pi$ of pairs $(s,\ell)$ is **sound** if

$$
(s,\ell)\in\mathcal E_\pi\ \Longrightarrow\
\forall y\in C_\pi(s),\quad \tau_\pi(y)=\ell,
\tag{24.2}
$$

and **complete** if every $x\in P_\pi$ belongs to at least one $C_\pi(s)$ with $(s,\tau_\pi(x))\in\mathcal E_\pi$. Enumeration means an effective staged listing, possibly with repetitions, relative to the declared $O$. Soundness on an empty relative cell is vacuous; completeness obtains no coverage from that cell. Neither condition requires recognizing emptiness.

The general realizer and effective-open-set principles behind such listings are supporting mathematics: Pauly, *On the topological aspects of the theory of represented spaces*, [version 3, §§3–4](https://arxiv.org/html/1204.3763v3), defines computability through realizers and open-set names through Sierpiński-valued maps. Schröder, *Admissibly Represented Spaces and Qcb-Spaces*, [Proposition 2.4](https://arxiv.org/html/2004.09450v1), gives computability-implies-continuity on Baire-space names. Here a mathematical name can list $q_D(x)$ for $D=1,2,\ldots$, with domain restricted to names of promised originals. This representation is used to explain finite information, not supplied as an infinite observed input. The exact floor specialization and the effective forward simulation are established next and consumed by the rational prior in §25; the general realizer principle is not a separate new result.

**Theorem 24.3 (source-specific stationary replacement and usable stopping).** Under Assumption 24.1, for each fixed public $(P_\pi,\tau_\pi)$ and fixed conditional $O$, the following are equivalent:

1. A stationary $O$-controller acquires the original target pointwise finitely.
2. A forward $O$-controller acquires that same original target pointwise finitely.
3. There is an $O$-computably enumerable sound complete family of labeled cells as in Definition 24.2.

The correspondence between controllers and enumerators is effective from their finite codes and the declared interfaces. Without the effectiveness requirement, existence of a sound complete family of cells is equivalent to the semantic condition

$$
\forall x\in P_\pi\ \exists\epsilon>0\ \forall y\in P_\pi:\quad
x\le y<x+\epsilon\ \Longrightarrow\ \tau_\pi(y)=\tau_\pi(x).
\tag{24.3}
$$

Condition (24.3) alone does not assert an enumerable family or an executable stopping rule. No equality of actual action archives, final physical cuts, durations or resource vectors is implied by the stationary/forward output equivalence.

Proof. First turn a forward program into a stationary one, retaining its computation, oracle access and known chronological probe prefix $u$ in simulated memory. When the simulated program requests $q_M$ at that attained cut, compute $D=\Lambda_M$ and obtain the stationary report $k=q_D(x)$ at the original cut. Set

$$
r=\frac{2k+1}{2D}>0,
\qquad
\text{return to the simulation }\lfloor M f_u(r)\rfloor.
\tag{24.4}
$$

The rational $r$ belongs to the same raw $D$-cell as $x$, including the $k=0$ cell. Theorem 15.2, applied at the original cut, says precisely that $q_D$ determines the whole scale-$M$ future profile. Consequently (24.4) is exactly $q_M(f_u(x))$. This uses that theorem's already established sharp divisibility result, without rederiving its cut or LCM classification. It also makes its factor effective: the midpoint, $\Lambda_M$, the fractional map and its floor are computed by finite integer and rational arithmetic. The matrix for chronological $u$ is `wordMatrix` of $\operatorname{reverse}u$, as in Definition 6.3; alternatively append an action by left-multiplying the current column-action matrix by its generator. No source inverse is executed.

Each simulated action updates this finite known word or matrix and leaves the actual stationary source unchanged. Identical returned reports and the same fixed oracle preserve the original program's choices inductively. A promised terminating run has finitely many actions, reads and computations; replacing each read by the finite calculation above still terminates and returns the identical original-target string. Conversely a stationary program is a forward program that chooses no actions. Thus 1 and 2 are equivalent effectively. The construction may request much larger scales and use different arithmetic and memory; it is a termination and output correspondence.

For 1 implies 3 use the standard halting-branch enumeration, spelling out its interface here. Dovetail bounded simulations of the stationary program on all finite lists of guessed nonnegative integer replies. Supply a guessed reply whenever it asks for a floor report, and resolve its ordinary computation and oracle queries relative to the fixed $O$. For every simulation that terminates using its available guessed replies and emits a complete label $\ell$, list the actually requested scale/reply pairs as $s$ and emit $(s,\ell)$. This is an $O$-enumeration: the guessed lists and step bounds have effective finite encodings. If an original $y$ belongs to $C_\pi(s)$, induction on requests reproduces that very terminating computation on $y$, so correctness of the controller implies (24.2). A guessed list with no promised realization causes no exception. Conversely each promised actual run has a finite reply list and a finite termination bound, and its labeled cell is eventually listed. This proves completeness.

For 3 implies 1 run the enumerator, and test each emitted $s$ by its finitely many stationary exact reports. Output its label when every reported integer agrees. Every such test is finite, the source is unchanged, and soundness gives correctness. For a promised $x$, some matching cell is emitted after finitely many enumeration steps and earlier tests, so the program stops. One may cache reports, but caching is not required for this proof. These two constructions are the elementary finite-realizer argument cited in Definition 24.2, with exact finite service semantics supplied here.

A finite cell containing $x$ contains a relative right neighborhood of $x$: each of its upper endpoints $(k_i+1)/D_i$ is strictly greater than $x$, so take a positive number smaller than all their distances from $x$. Its lower endpoints are at most $x$. A sound complete family therefore implies (24.3). Conversely write $x=p/q$ in reduced positive form. Given the radius in (24.3), choose a positive multiple $D$ of $q$ with $1/D<\epsilon$. Then $Dx$ is an integer and its exact cell is $[x,x+1/D)\cap\mathbb Q$, homogeneous relative to $P_\pi$. Taking all semantically sound labeled cells covers the prior. This collection is countable but need not be computably enumerable. The proof chooses $D$ from the exact mathematical $x$ and a semantic radius; it gives no controller either datum. Section 25 supplies the strict failure of the effective implication.

A universal procedure deciding semantic soundness for every candidate cell and label is a stronger demand than these constructions use. A decidable acceptance test for a sound complete subfamily is sufficient, but an enumerable subfamily already suffices; neither all homogeneous cells nor a decision of their universal property is needed. If an enumeration-stage witness is added to a certificate, its bounded generation can of course be checked decidably. Thus the criterion does not posit a strict separation between enumerable proof systems and checkers with such witnesses. It distinguishes a usable sound complete enumeration from semantic homogeneity and from a universal decision of homogeneity. $\square$

## 25. Decidable sparse rational priors with exact acquisition degree

**Definition 25.1 (a public unique-pulse prior and original-history bit).** Fix a public finite program for a total computable function $b:\mathbb N^2\to\{0,1\}$ satisfying

$$
\forall e,s,t,\qquad b(e,s)=b(e,t)=1\ \Longrightarrow\ s=t.
\tag{25.1}
$$

The program and the uniqueness promise are independent of the unknown original. Put

$$
\begin{aligned}
H_b&=\{e:\exists t,\ b(e,t)=1\},& a_e&=e+1,\\
P_b&=\{a_e:e\ge0\}\ \cup\
 \{a_e+2^{-(t+2)}:b(e,t)=1\},\\
\tau_b(x)&=\begin{cases}0,&x\text{ is an integer},\\1,&x\text{ is not an integer}.\end{cases}
\end{aligned}
\tag{25.2}
$$

The target is a single encoded bit of the original $x$. Under the original chronological source it is equivalently the bit that $L$ occurred somewhere in the original word, not the bit that a probing controller performed $L$. Integers $n\ge1$ have the word $R^{n-1}$, and these are exactly the words with no $L$: Theorem 6.2 gives the unique word at each rational, while executing only $R$ gives exactly those integers. The original exact rational has its reduced positive pair as encoding. The other finite targets are precisely the original literal word, its rooted oriented path with named edges, and its finite indexed prefix-memory table of §§5–6. Their encoding and decoding retain the same source, root and original cut.

An exhaustive cutoff is a total function $N:\mathbb N\to\mathbb N$ such that

$$
\forall e,\quad
\bigl[\forall t\le N(e),\ b(e,t)=0\bigr]
 \ \Longrightarrow\ \forall t,\ b(e,t)=0.
\tag{25.3}
$$

This is the inclusive cutoff convention of `UniformFirstHitMemory.ExhaustiveZeroPrefix`, with the Boolean values written $0,1$.

**Theorem 25.2 (rational acquisition realizes the unique-pulse hit degree).** The prior $P_b$ has decidable membership for finitely encoded rationals, is locally finite in the ordinary real metric, and has at most two members in every band $[n,n+1)$, $n\in\mathbb Z_{\ge0}$. Every member is isolated and hence semantically admits a finite relative singleton observation cell with all integer-scale ports. Nevertheless, for every fixed, explicitly conditional source-independent $O$, the following are equivalent:

1. $H_b\le_T O$.
2. There is an $O$-computable exhaustive cutoff satisfying (25.3).
3. The original bit $\tau_b$ is pointwise-finitely acquired by an $O$-controller.
4. The exact original rational is pointwise-finitely acquired by an $O$-controller.
5. Any one, equivalently every one, of the exact original four finite views in Definition 25.1 is pointwise-finitely acquired by an $O$-controller.
6. There is an $O$-computably enumerable sound complete labeled-cell family for $(P_b,\tau_b)$.

In 3–5, stationary and forward acquisition have the same meaning of existence, by Theorem 24.3. From a supplied reduction in 1 one obtains a stationary exact-rational controller using at most two floor reads on each original. From a correct bit controller one obtains a total $O$-computable cutoff and a decision procedure for $H_b$. These constructions use the stated public program; they are uniform in such supplied codes and correctness promises, not an algorithm deciding whether an arbitrary presentation has those properties.

Proof. Membership does not require deciding whether a row ever hits. Given an encoded rational $z$, reject $z<1$ and accept every integer $z\ge1$. Otherwise let $n=\lfloor z\rfloor\ge1$ and reduce $z-n$ to a positive fraction. Decide whether it is exactly $2^{-k}$ for an integer $k\ge2$, by testing that its reduced numerator is $1$ and its denominator is a power of two of that exponent. If not, reject. If so, accept exactly when the single terminating computation $b(n-1,k-2)$ returns $1$. This covers all and only (25.2). In band $[n,n+1)$, $n\ge1$, the integer $n$ and at most its one pulse occur; band zero is empty. A bounded real interval meets finitely many such bands and thus finitely many members. Every member has a positive ordinary isolation radius. Taking a sufficiently fine scale divisible by its reduced denominator gives a right cell containing no other member, as in the last part of Theorem 24.3. These singleton cells exist without an effective list of them.

Suppose 1 holds. A total $O$-decision for $H_b$ yields a cutoff by returning $N(e)=0$ if the answer is no and, if the answer is yes, searching $b(e,0),b(e,1),\ldots$ until its hit $t$ and returning $N(e)=t$. The yes branch terminates by its premise and (25.3) follows. Conversely, given 2, evaluate $b(e,t)$ for the finite range $0\le t\le N(e)$. A hit proves membership in $H_b$; all zeros prove nonmembership by (25.3). Thus 1 and 2 are equivalent. This cutoff/hit equivalence is the classical first-occurrence principle, used here as a supplier rather than as a new computability theorem.

For the acquisition upper bound, first read $q_1(x)=n$. On $P_b$ this identifies $e=n-1$ and its band, not which of its possible two members is present. Decide $e\in H_b$ by the supplied $O$-reduction. If the answer is no, the original is $n$ and return its reduced pair. If the answer is yes, search for the unique hit $t$ and put $D=2^{t+2}$. The only two promised possibilities and their reports are

$$
\begin{array}{c|c}
\text{original }x& q_D(x)\\ \hline
n&Dn\\
n+2^{-(t+2)}&Dn+1.
\end{array}
\tag{25.4}
$$

The second exact read selects the correct original rational. All arithmetic, the search, and the finite reduction computation terminate on the selected branch. The known program $b$ does not initialize the controller with the unknown row or its hit time: the first report identifies the row and the declared reduction supplies its hit decision. Thus 1 implies 4, with the claimed read bound. Theorem 6.2's finite Euclidean decoder then constructs the original word and the other original finite views, giving 5. Each such view determines the original rational and therefore the integer bit, so 4 or 5 implies 3. These are output computations, not access to a stored original archive.

For the matching lower bound, take a bit controller as in 3 and first replace it effectively by a stationary one using Theorem 24.3. On integer input $e$ to a reduction, simulate this program against the computably specified original $a_e=e+1$, computing each requested floor reply exactly and answering its oracle queries from the same fixed $O$. This integer is in $P_b$ for every $e$, so the simulation terminates and its correct output is $0$. Let

$$
D_*(e)=\max\bigl(\{1\}\cup\{D_i:\text{scales read in this simulation}\}\bigr),
\qquad
N(e)=\min\{N\ge0:2^{N+2}>D_*(e)\}.
\tag{25.5}
$$

Both are total $O$-computable functions of $e$ and the controller code. The maximum also handles a run with no reads. If $t>N(e)$ were a hit in row $e$, the promised rational $y=a_e+2^{-(t+2)}$ would satisfy, for every one of the finitely many simulated reads,

$$
0<D_i2^{-(t+2)}<1,
\qquad
q_{D_i}(y)=D_i a_e=q_{D_i}(a_e).
\tag{25.6}
$$

Replay induction gives the same complete finite computation and output on $y$: equal previous reports select the same next scale and the same oracle queries, since $O$ is fixed independently of the source. That output would be $0$ whereas $\tau_b(y)=1$. Correctness excludes every such hit. In fact every hit in row $e$ lies at most $N(e)$, which implies (25.3). Thus 3 implies 2, and the finite search through this computed cutoff decides $H_b$. The exact value $a_e$ is used only in this reduction's simulation; no acquisition program is handed its actual unknown rational. Conditions 3 and 6 are equivalent by Theorem 24.3, completing the equivalence and both reductions. $\square$

**Theorem 25.3 (strictness with a completely specified finite prior program).** There is a total computable unique-pulse program $b$ for which $H_b$ is undecidable. Its rational prior has all the decidability, sparsity and local-isolation properties of Theorem 25.2, and $\tau_b$ is decidable when an exact rational is supplied. Yet no ordinary effective stationary or forward controller acquires even that bit pointwise finitely from the specified floor ports. In particular ordinary-metric isolation and semantic right-local homogeneity do not supply an enumerable sound complete stopping family, even for this decidable prior and binary target.

More generally every computably enumerable set occurs as $H_b$ for a public total computable first-hit program satisfying (25.1). Hence Theorem 25.2 realizes every such hit degree as the conditional acquisition degree of this rational prior construction; it does not introduce an oracle into the actual model.

Proof. For a fixed computable enumerator of a set $A$, let $A(e,t)$ be the decidable predicate that $e$ has appeared during its first $t$ computation steps. Define $b(e,t)=1$ exactly when $A(e,t)$ holds and $A(e,s)$ fails for every $s<t$. This is a finite bounded test for each $(e,t)$, has at most one hit per row, and has a hit exactly for $e\in A$. The first-occurrence construction is classical; the consequence for rational acquisition is Theorem 25.2.

One explicit finite presentation of an undecidable instance uses the pinned partial-recursive code evaluator. Let $c_e=\operatorname{ofNatCode}(e)$ and

$$
A(e,t)\ \Longleftrightarrow\
\operatorname{evaln}(t,c_e,0)\ne\mathrm{none},
\qquad
b(e,t)=1\ \Longleftrightarrow\ A(e,t)\land\forall s<t,\neg A(e,s).
\tag{25.7}
$$

Here `Nat.Partrec.Code.ofNatCode` and `Nat.Partrec.Code.evaln` have exactly the definitions in [PartrecCode.lean at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/PartrecCode.lean). The code decoder is a terminating recursion on its integer argument, and `evaln` is the finite resource-bounded evaluator; `primrec_evaln` supplies its primitive recursiveness. Thus (25.7), including its bounded earlier-stage test, is a public total finite-program specification independent of the unknown $x$. `evaln_complete` and `evaln_sound` identify existence of a successful finite evaluation with termination of $c_e$ on $0$. The code numbering represents every code effectively. If this $H_b$ were decidable, composing its decision with code encoding would decide code termination at $0$, contrary to `ComputablePred.halting_problem 0` in [Halting.lean at the same revision](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Halting.lean). The corresponding recursively enumerable termination predicate is `halting_problem_re 0`. These are mature computability suppliers with their exact fixed-input domain, not claims that the new rational bridge is already a kernel theorem.

Apply Theorem 25.2 with $O=\varnothing$. Conditions 1–6 all fail for this instance, while the membership and isolation conclusions still hold. The bit as a function of an exact encoded rational is computed simply by testing integrality. Its failure of acquisition is therefore a failure of obtaining a usable finite stopping distinction from the allowed reports, not a failure to compute the bit after exact input has been acquired. A source-dependent program that already selected the row's hit status would change Assumption 24.1 and is excluded. $\square$

**Definition 25.4 (quantifier and resource boundaries of the degree correspondence).** Theorem 25.2 concerns one fixed public $b$ and one program valid for all originals in its $P_b$. Its uniform constructions take, respectively, a code for an $H_b$-decision relative to $O$, or a code for a correct terminating controller, as supplied mathematical inputs. They do not decide totality, uniqueness or correctness of arbitrary program codes, and do not uniformly synthesize a decision for $H_b$ from $b$ alone. A separate program or advice string selected by the unknown $x$ is forbidden. Decidable rational membership in $P_b$ cannot substitute for deciding whether an entire integer band has a second member: that band-existence question is exactly $e\in H_b$.

The upper bound is two floor reads, not two bounded-cost operations. Reading $q_1$ already has unbounded report width as $e$ varies. A yes branch must execute the supplied hit-decision reduction, locate $t$, construct a scale of bit length $t+3$, read its complete payload and perform exact arithmetic. A word output may be long: the integer original $n$ has word $R^{n-1}$. All these finite costs and storage remain paid. If the set of hit times is unbounded, no single bound on stationary scales can suffice even for the bit: for any such bound $D_0$, a row with $2^{t+2}>D_0$ makes its two originals agree at every allowed scale $D\le D_0$, hence on every adaptive run restricted to those scales. This is separate from the stronger undecidable-instance obstruction, which permits arbitrary finite scales and still excludes an ordinary controller.

A fixed decidable hit set may admit the two-read controller with unbounded search, payload and scale costs. An undecidable hit set admits no ordinary controller regardless of how much pointwise finite computation or how many finite reads it is allowed. The conditional equivalence $H_b\le_T O$ records exactly what additional source-independent decision access would suffice; none is supplied to remove that obstruction. These statements do not assert a common total resource bound or an optimal resource vector.

## 26. Endpoint separation and an unbounded menu that forward actions strengthen

**Theorem 26.1 (the same original target under dyadic and integer ports).** Let

$$
c=\frac13,\qquad
P^- =\{c\}\cup\{c-1/m:m\in\mathbb Z,\ m\ge4\},\qquad
\sigma(c)=1,\quad \sigma(c-1/m)=0.
\tag{26.1}
$$

All are originals from the same rational chronological source. With all integer ports, the stationary read $q_3$ acquires $\sigma$ exactly, although $\sigma$ is not locally constant at $c$ in the relative ordinary two-sided metric. With the restricted, numerically unbounded menu $\{q_{2^n}:n\ge0\}$, no pointwise-finite stationary controller acquires $\sigma$ on this same prior, whereas one actual $L$ followed by $q_4$ does. These comparisons preserve the original target and the menu within each stationary/forward comparison. They make no assertion that every integer port is necessary for a particular prior or task.

Proof. The prior has a finite rational presentation and decidable membership: accept $c$; otherwise require $0<x<c$ and that $1/(c-x)$ is an integer at least four. At $c$, the sequence $c-1/m$ approaches from below with the other target value, so no two-sided relative metric neighborhood has constant $\sigma$. Yet the exact floor convention gives

$$
q_3(c)=1,\qquad q_3(c-1/m)=0\quad(m\ge4).
\tag{26.2}
$$

This is a valid one-read stationary algorithm. At $c$ its cell includes the endpoint on the right, with no smaller point, and so (24.3) holds there. Every smaller member of the prior is isolated. Ordinary two-sided metric locality is therefore not a necessary replacement for the exact floor-cell condition, even with an effective one-read certificate.

Now suppose a stationary controller with just the dyadic menu terminates correctly at $c$. Its finite run queries finitely many exponents; let $N$ be their maximum, taking $N=0$ if there are no queries. Since $3$ never divides $2^n$, the fractional part of $2^nc$ is either $1/3$ or $2/3$. Choose an integer $m>\max(4,3\cdot2^N)$. For every queried exponent,

$$
0<\frac{2^n}{m}<\frac13\le\{2^nc\},
\qquad
q_{2^n}(c-1/m)=q_{2^n}(c).
\tag{26.3}
$$

Replay of that finite adaptive branch gives identical decisions and output on the smaller promised original, contradicting its target $0$. This argument also covers a fixed source-independent auxiliary oracle: its answers are the same on the replay. It places no common bound on the controller's query exponents or stopping times, only a finite maximum on the one completed run at $c$.

On the other hand monotonicity and the endpoint identity give

$$
L(c)=\frac14,\qquad
0<L(c-1/m)<\frac14,
\qquad
q_4(L(c))=1,\quad q_4(L(c-1/m))=0.
\tag{26.4}
$$

Thus actually perform $L$ and read the available dyadic port $q_4$; its report is the exact value of $\sigma$ of the original. It is not a task distinguishing the final values under a changed prior. Both this forward algorithm and the impossible stationary dyadic algorithm start with (26.1) and aim at that same $\sigma(x)$. The stationary all-integer algorithm (26.2) uses only $q_3$, so the counterexample does not require all integer scales for its positive stationary solution. Theorem 24.3's general simulation of a $q_4$ request instead calls for $q_{\Lambda_4}=q_{12}$, absent from the dyadic menu. The menu's numerical unboundedness provides neither that port nor a replacement for its relevant endpoint: (26.3) rules out every finite combination of stationary dyadic reports on this task. $\square$

## 27. Supplier correspondence and the scope of original four-view acquisition

**Definition 27.1 (mathematical antecedents and source-specific increment).** The source-specific increment is the matching rational-prior/acquisition reductions (25.4)–(25.6), including decidable locally finite membership, the binary original-history task and its exact acquisition degree. The effective use of Theorem 15.2 in (24.4) connects that degree to actual forward access under the same original target. The endpoint construction (26.1)–(26.4) identifies a failure of that replacement when the supplied menu is only numerically unbounded. These are `repo-derived` ordinary mathematical consequences with the complete proofs above, without a worldwide priority assertion. First-hit coding, oracle reducibility, halting undecidability and finite-realizer enumeration are literature-attested supporting mathematics; the generic realizer principle in Theorem 24.3 is included as an intermediate supplier for this application.

The source statements have the following precise correspondences and limits:

| Supplier | Correspondence and hypothesis boundary |
| --- | --- |
| [ActualFirstTerminationMemory](../../../D5/S3/ObserverMemory/Prediction/ActualFirstTerminationMemory.lean), `Oldest8330Proposal.UniformFirstHitMemory.ExhaustiveZeroPrefix`, `uniform_single_pulse_obstruction` | The cutoff convention is exactly (25.3). The theorem assumes `Computable₂ b`, uniqueness of a true value in each row, and noncomputability of the existential hit predicate; its final conjunct excludes a computable exhaustive cutoff. The rational prior is not a supplier hypothesis or conclusion: (25.5)–(25.6) provide the additional acquisition-to-cutoff bridge. Its unary-state minima are not being used as apparatus-memory costs here. |
| The same module, `Oldest8330Proposal.OperationalFirstTermination.original_section_6_4` | This supplies an existential universal native first-termination pulse with total computability and the cutoff obstruction. It is not an executed extraction of a particular public program. Definition 25.1 requires the actual finite program as part of its public presentation; (25.7) instead specifies an explicit evaluator-based instance and does not purport to extract the existential native code. |
| [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `wordMatrix`, `unimodular_wordMatrix`, `wordMatrix_lower_right_pos`; [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix` | The generators are precisely $G_L,G_R$, with `false`, `true`. Chronological $u$ uses `wordMatrix(reverse u)`. The natural determinant-one and positive-denominator contracts support the fractional maps already used by Theorem 15.2; they do not by themselves provide a finite stopping certificate. Matrix generation supplies no extra port or exact original input. |
| [FinitePrefixLocalConstancy](../../../D5/S3/Observer/SymbolicStability/FinitePrefixLocalConstancy.lean), `finite_prefix_locally_constant_off_boundary` | This assumes a pseudo-metric space, a finite family of locally constant symbols away from their specified boundaries, and a point outside their union. It supplies an existential common metric radius. On-wall exact floors in (26.2) and (26.4) do not satisfy the stated off-boundary premise, and the statement provides no effective stopping radius. It therefore cannot replace the one-sided condition or enumerable family used here. |
| [FiniteDistinguishingCertificate](../../../D5/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate.lean), `finite_distinguishing_certificate` | Its finite class is a surjective classification exact for equality of every available evaluation. A binary target alone does not give that hypothesis. In $P_b$, different bands already have different $q_1$ reports, and the full behavioral classification is infinite. The theorem neither turns those infinitely many behaviors into two exact classes nor selects and executes a stopping policy for (25.2). |
| Pinned mathlib `PartrecCode` and `Halting`, cited in Theorem 25.3 | The finite evaluator, its soundness/completeness, effective code numbering and fixed-input halting obstruction support (25.7). Reading their source statements is distinct from a new kernel check of the rational acquisition theorem. |

The stopping obstruction of [Atomic Generation Acquisition III §§19–20](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_III.md) concerns its noisy complete post-clock digital service; its metric necessary condition and supplied-denominator decoder are not an effective sufficiency theorem for this deterministic floor interface. [Finite Unit Catalogue Identifiability §§2–3](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_UNIT_CATALOGUE_IDENTIFIABILITY.md) supplies explicit finite catalogue values and exact comparisons for its different scale law. Here only two candidates per band are present, but knowing whether the second exists is exactly the undecidable question in Theorem 25.3. The delayed-constraint construction in [Effective Resolution §§2.2.5–2.2.8](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md#225-按事件逐条加入的实际-lcm-塔) already distinguishes existence of compatible infinite threads from computable thread selection; the rational membership and matching acquisition-degree construction are the added correspondence, not a relabeling of that general distinction.

The four-view transports remain exactly those of Theorem 6.2 and Theorem 17.3 on their original rational source. Acquiring an exact reduced rational permits finite construction of its original word, named incidence path and indexed prefix table. A rational's predictive thread may then be specified mathematically by its rational parameter, but no infinite list of reports has been read or emitted. Nothing here extends these original-source decoders to the ambient cyclic-anchor fibers of §§20–23, installs a certification service, or identifies actual probe histories with simulated histories. The resource contract counts every acquired report, scale encoding, operand width, computation, storage and finite output. The conclusions assert neither a physical spacetime interpretation nor new kernel verification of the ordinary proofs above.

## 追加锚（本行以下为增补区）

## 28. Effective scale menus and the original acquisition problem

**Assumption 28.1 (enumerated names and separately supplied services).** Keep precisely the original source $x=B(w)\in\mathbb Q_{>0}$, root $1$, chronological actions $L(x)=x/(1+x)$ and $R(x)=x+1$, and public original-target presentations $(P_\pi,\tau_\pi)$ of Assumption 24.1. A menu is specified by one public source-independent finite program $E$. On each input stage $n\in\mathbb N$, it finishes and emits a finite list of positive integers. Let $S$ be the union of its lists. Repetition, empty stages, finite menus and the empty menu are allowed. This is a staged effective enumeration, without a decision procedure for membership, boundedness or divisibility cofinality.

Separately assume that each $D\in S$ names a reusable exact nondisturbing service $q_D(z)=\lfloor Dz\rfloor$ at every cut attained by the one actual source. Each requested service completes finitely and returns the complete integer in a fixed finite encoding. Giving $E$ does not install any of these ports. Source actions and services are performed serially; waiting for an enumerator stage or a service supplies no source-dependent timing report. Ordinary finite exact computation is permitted and charged. No source reset, copy, inverse action, unknown-history archive, exact unknown-source input, infinite observed thread or auxiliary oracle is supplied.

**Definition 28.2 (task classes and the joint divisor set).** Write $\operatorname{Stat}(S)$ and $\operatorname{Fwd}(S)$ for the classes of these same public pairs $(P_\pi,\tau_\pi)$ acquired by one ordinary effective deterministic program that is correct and terminates on every promised original, respectively with no source actions and with actual forward actions allowed. Outputs remain $\tau_\pi(x)$ at the original cut. Programs and any auxiliary computations have finite source-independent descriptions. No effective presentation of all correct controllers or all homogeneous priors is assumed. Put

$$
\operatorname{Div}(S)=\{b\in\mathbb Z_{>0}:\exists D\in S,\ b\mid D\}.
\tag{28.1}
$$

The divisor $1$ belongs to this set exactly when $S$ is nonempty. A legal read uses a name in $S$. Requiring an enumeration witness before using that name gives the same task class: before any legal request for $D$, run stages until $D$ appears. That extra search finishes and leaves the source unchanged. Such searches are part of the cost. The all-integer menu $\mathbb N_{>0}$ has its usual effective enumeration and the conditional services of Assumption 24.1. Comparisons of classes below vary the access menu while keeping the public presentation, actual source law, original target and endpoint convention fixed.

## 29. Comparing original thresholds after every actual prefix

**Theorem 29.1 (a repeatable comparison on one source).** Under Assumption 28.1, suppose $S$ is numerically unbounded. From $E$, any known already executed chronological probe prefix $u$, and a known positive rational threshold $r$, there is a finite effective continuation which reports exactly whether the original $x$ satisfies $x\ge r$. It executes only further forward actions and one supplied floor read. Its retained data permit another such comparison from the newly attained cut. More precisely, the controller can maintain the invariant

$$
A_u=\begin{pmatrix}\alpha&\beta\\c&d\end{pmatrix}\in\mathbb N^{2\times2},\qquad
\alpha d-\beta c=1,\quad d\ge1,\qquad
z=f_u(x)=\frac{\alpha x+\beta}{cx+d}.
\tag{29.1}
$$

Initially $A_u$ is the identity. The construction transforms finite descriptions into a finite ordinary program under the unboundedness promise; it does not recognize that promise.

Proof. Reduce the given threshold to $r=a/b>0$. From the known matrix, compute

$$
t=f_u(r)=p/q,\qquad p=\alpha a+\beta b,\quad q=ca+db.
$$

Both integers are positive and coprime. Indeed the integer inverse matrix carries $(p,q)$ back to $(a,b)$, so a common divisor of $p,q$ divides both $a,b$. Positivity also follows directly from the positive-domain action formulas. In particular the denominator is not zero. The derivative sign, or the determinant identity after cross multiplication, shows that every $f_u$ is strictly increasing on positive inputs.

Run $E$ through successive stages until a listed $D>pq$ occurs. Unboundedness ensures a finite successful stage, including when earlier stages are empty. Equation (15.3), applied to the current rational threshold $t$, says it is a predictive cut at scale $D$. For actual repeatable acquisition we need a computable continuation attaining a grid threshold, not just its counterfactual existence. The constructive arithmetic in that equation gives it as follows. Search $j=1,\ldots,p$ for $qj\equiv D\pmod p$; when $p=1$ take $j=1$. Coprimality guarantees success, and $qj\le pq<D$. Thus

$$
h=(D-qj)/p>0,\quad ph+qj=D,\quad
g=\gcd(h,j),\quad C=h/g,\quad F=j/g.
$$

Here $C,F\ge1$ and $\gcd(C,F)=1$. Search $A=1,\ldots,C$ for $AF\equiv1\pmod C$, taking $A=1$ when $C=1$, and put $B=(AF-1)/C$. This is an effective finite search, $B\ge0$, and the matrix

$$
H=\begin{pmatrix}A&B\\C&F\end{pmatrix},\qquad AF-BC=1
$$

has nonnegative integer entries. Neither $p=1$ nor $q=1$ has been excluded; the strict inequality $D>pq$ ensures the positive coefficients in all these cases. This is the positive-coefficient construction already used in (15.3), rather than an application of a two-generator Frobenius formula with extra nonunit assumptions.

To obtain an executable chronological word for $H$, use the finite row descent underlying `unimodular_iff_wordMatrix`. Its arithmetic realization can be described without extracting executable code from an existential Lean proof. At a nonidentity nonnegative determinant-one matrix, its two rows are componentwise comparable. If its upper first entry exceeds the lower first entry while its lower second entry exceeds the upper second entry, the determinant is at least the sum of the two smaller entries plus one; determinant one forces those smaller entries to be zero and gives precisely the identity. The other strictly crossed order has negative determinant. Equal coordinates cause no additional incomparable case. Subtract the smaller row from the larger, recording $L$ when the lower row was reduced and $R$ when the upper row was reduced. Each row is nonzero, the new entries stay nonnegative, the determinant stays one, and the sum of the four entries strictly decreases. The procedure therefore terminates at the identity. If the recorded labels are $e_1,\ldots,e_\ell$ in peeling order, then $H=G_{e_1}\cdots G_{e_\ell}$; execute their reverse order to obtain a chronological word $v$ with matrix $H$. These are finite comparisons, subtractions and list operations on known integers. They supply an ordinary terminating procedure, not an additional source inverse. Descent is performed on the known matrix before any of the new actions are executed.

The current threshold is now sent to an exact scale-$D$ grid point:

$$
D f_v(t)
 =D\frac{Ap+Bq}{Cp+Fq}
 =g(Ap+Bq)=:k\in\mathbb Z_{>0},
\tag{29.2}
$$

because $Cp+Fq=D/g$. Actually execute $v$ on the attained source, obtain $Q=q_D(f_v(z))$, and return the bit $[Q\ge k]$. Strict monotonicity and the exact upper value of floor at an integer give

$$
Q\ge k
\ \Longleftrightarrow\ f_v(f_u(x))\ge f_v(f_u(r))
\ \Longleftrightarrow\ x\ge r.
\tag{29.3}
$$

Equality belongs to the yes branch. This convention is essential for original rational endpoints. Update the retained matrix to $H A_u$ while recording the actions as executed; the actual state is $f_{uv}(x)$ and (29.1) holds with $uv$. The update only uses known actions and integer arithmetic, never an unknown original value. Thus any finite adaptive sequence of these comparisons is one actual experiment: the next comparison begins with this updated matrix and uses the image of its new original threshold. It does not restart from the original cut. All searches and the read finish finitely, so an induction over completed comparisons proves the assertion. $\square$

**Theorem 29.2 (finite-code simulation of stationary integer reads).** If $S$ is numerically unbounded, every correct all-integer stationary controller for a public $(P_\pi,\tau_\pi)$ can be transformed, using its finite code and $E$, into a forward $S$-controller for the same original target. No test of correctness of the given controller, of membership in $P_\pi$, or of semantic homogeneity is required.

Proof. Retain a simulation of the given program and one matrix satisfying (29.1) for the actual source. When the simulated program requests $q_m(x)$, compare the original $x$ successively with

$$
1/m,\ 2/m,\ 3/m,\ldots
\tag{29.4}
$$

using Theorem 29.1 from the updated actual cut after each comparison. Stop at the first no answer, say at $J/m$, and return $J-1$ as the simulated report. If the true report is $K=\lfloor mx\rfloor$, exactly the first $K$ comparisons answer yes and the $(K+1)$st answers no. Hence $J=K+1<\infty$, and the return is exact, also when $K=0$ or $mx$ is an integer. All thresholds are positive known rationals. No numerical value of the unknown $x$ was input to the comparison program.

Inductively the simulated program receives precisely the stationary reports it would have obtained from the original source. Its chosen scales, internal computation, stopping decision and finite output therefore agree with that original run. On each promised original the run has finitely many requests, each replaced by finitely many comparisons and actual continuations. The transformed run consequently terminates. The matrix persists across requests as well as across thresholds within one request. The finite code consists of the given controller, the menu enumerator, exact arithmetic and these loops. The construction is conditional on the stated promises and preserves the output, without identifying simulated and actual action archives, attained cuts or costs. $\square$

## 30. The exact stationary preorder and the forward universality threshold

**Theorem 30.1 (joint divisibility is the stationary invariant).** For any two effective supplied menus $S,T$ of Assumption 28.1,

$$
\operatorname{Stat}(S)\subseteq\operatorname{Stat}(T)
\quad\Longleftrightarrow\quad
\operatorname{Div}(S)\subseteq\operatorname{Div}(T).
\tag{30.1}
$$

The forward implication is a necessary comparison of task classes. The reverse implication has a finite-code transformation from a correct $S$-controller and the enumerator of $T$, under the displayed inclusion promise.

Proof. Suppose the divisor inclusion holds. When the simulated $S$-controller requests $q_D(x)$, search stages of $T$ for an $F$ with $D\mid F$. Such an $F$ exists since $D\in S$ implies $D\in\operatorname{Div}(S)$. Write $F=hD$, read its installed port with result $k$, and return $\lfloor k/h\rfloor$. For $y=Dx$ the identity $\lfloor\lfloor hy\rfloor/h\rfloor=\lfloor y\rfloor$ proves exactness. This uses one actual available port, not a port at the LCM of several separately read scales. Finite searches and finite integer division preserve every promised terminating run. The actual source is stationary throughout.

For necessity take $b\in\operatorname{Div}(S)\setminus\operatorname{Div}(T)$, set $c=1/b$, and use the following public prior and binary original target:

$$
P_b=\{c\}\cup\{x_n=c-1/n:n\in\mathbb Z,\ n>b\},\qquad
\sigma_b(c)=1,\quad \sigma_b(x_n)=0.
\tag{30.2}
$$

The rational membership procedure accepts $c$, or accepts $y$ exactly when $0<y<c$ and $1/(c-y)$ is an integer greater than $b$. It terminates on every rational input. Thus the prior is decidable and has a source-independent finite presentation, including $b=1$. Choose $D\in S$ divisible by $b$. Then $q_D(y)\ge D/b$ if and only if $y\ge c$, so one stationary read acquires $\sigma_b$ on this prior. Such a $D$ is also found effectively by the enumerator of $S$.

Suppose a stationary $T$-controller terminates correctly at $c$. It queries finitely many scales, forming a finite set $F_0$. If this set is nonempty, $b\nmid D$ for each $D\in F_0$ gives $\{D/b\}>0$. Choose an integer $n>b$ so large that

$$
1/n<\min_{D\in F_0}\frac{\{D/b\}}{D}.
\tag{30.3}
$$

It follows that $q_D(x_n)=q_D(c)$ at every queried scale. If $F_0$ is empty choose any $n>b$. All enumeration and ordinary computations are source-independent, and induction replays exactly the same finite adaptive branch, stopping and output at $x_n$. This contradicts their different target values. When $b=1$, absence from $\operatorname{Div}(T)$ means $T$ is empty, so only the empty-query case is needed. Therefore $(P_b,\sigma_b)$ belongs to $\operatorname{Stat}(S)$ and not to $\operatorname{Stat}(T)$, proving necessity. $\square$

**Theorem 30.2 (sharp acquisition classification).** Under Assumption 28.1,

$$
\operatorname{Stat}(S)\subseteq\operatorname{Fwd}(S)
 \subseteq\operatorname{Stat}(\mathbb N_{>0}),
\tag{30.4}
$$

and the exact universality criteria, for the same class of public original-target presentations, are

$$
\begin{aligned}
\operatorname{Fwd}(S)=\operatorname{Stat}(\mathbb N_{>0})
 &\quad\Longleftrightarrow\quad S\text{ is numerically unbounded},\\
\operatorname{Stat}(S)=\operatorname{Stat}(\mathbb N_{>0})
 &\quad\Longleftrightarrow\quad\operatorname{Div}(S)=\mathbb N_{>0}.
\end{aligned}
\tag{30.5}
$$

If $S$ is empty both its classes consist exactly of tasks whose target has at most one value on the promised prior. The statements quantify over pointwise finite controllers; none supplies a uniform resource budget or an algorithm deciding the right-hand arithmetic properties from arbitrary menu codes.

Proof. A stationary program is a forward program using no actions. A forward $S$-program is a forward all-integer program that requests only names in $S$. The reverse simulation of Theorem 24.3, using a stationary $q_{\Lambda_D}$ to simulate each requested future $q_D$, therefore gives the second inclusion in (30.4). Every all-integer service used by that simulation is among the conditional services for the comparison class. This invokes the established exact simulation, without assuming $\Lambda_D\in S$.

Unboundedness gives the first equality in (30.5) by Theorem 29.2 and (30.4). Conversely, if $S$ is bounded choose an integer $M\ge1$ with $D\le M$ for every $D\in S$. This bound is chosen in the impossibility proof; it need not be computable from $E$. Take the explicit finite original prior

$$
A_M=\{1/(3M),1/(2M)\}.
\tag{30.6}
$$

For every available scale $D$, both points are below $1/M\le1/D$. Theorem 11.2 gives $1/D$ as the minimum predictive cut at scale $D$, so the two points have identical $q_D(f_u(\cdot))$ for every finite chronological $u$. A deterministic forward controller therefore obtains identical reports along every common actual branch: actions, enumeration and computations choose the same next step, and induction applies the preceding equality at each read. No terminating such controller can distinguish the two originals. This also covers $S=\varnothing$, with no reports. Yet the stationary all-integer port $q_{2M}$ returns respectively $0$ and $1$. The public list (30.6) consequently permits exact original rational recovery and hence original-word recovery with all-integer reads, but not forward $S$-recovery. Forward universality fails.

Apply Theorem 30.1 with $T=\mathbb N_{>0}$ in both directions to obtain the stationary equality criterion, since $\operatorname{Div}(\mathbb N_{>0})=\mathbb N_{>0}$. Explicitly, divisor cofinality finds an actually listed multiple for each requested scale; if it fails, (30.2) separates an all-integer stationary task from every stationary $S$-controller. A menu with every positive divisor is necessarily unbounded, consistently with the first criterion.

For an empty menu the entire evolution of an ordinary program, including any forward actions, is source-independent. A terminating output must therefore be identical on all promised sources. Every task with at most one target value has a constant-output finite program, including the vacuous empty-prior case. This proves the empty-menu statement without treating $1$ as an available divisor. The positive proofs use enumerator searches under supplied promises; the negative proofs do not turn boundedness or a missing divisor into decidable menu properties. $\square$

## 31. Original four-view witnesses and the failure of marginal arithmetic

**Theorem 31.1 (effective exact recovery on the endpoint priors).** For each $b\ge1$, the prior $P_b$ in (30.2) admits exact stationary all-integer acquisition of its original rational, original chronological word, rooted named-incidence path and indexed prefix table. If $b\notin\operatorname{Div}(S)$ no stationary $S$-controller acquires any of these four exact views on that same prior. If $S$ is unbounded all four are acquired by a forward $S$-controller. If $S$ is bounded the finite prior (30.6) witnesses failure of forward exact acquisition of each view.

Proof. Here is an actual finite stopping decoder for $P_b$, rather than a semantic assertion of local isolation. Read $q_b$. Its value is $1$ exactly at $c$ and is $0$ at every $x_n$, because $0<bx_n=1-b/n<1$. If it is $1$, output $c$. Otherwise, start $j=b+1$ and compare $x$ with the known rational $x_{j+1}=1/b-1/(j+1)$. Writing this threshold in reduced form $a_j/d_j>0$, the stationary read $q_{d_j}$ decides $x\ge x_{j+1}$ by comparison with $a_j$. On a yes answer increment $j$; on a no answer output the known rational $x_j$.

For an actual $x_n$, the sequence $x_j$ is strictly increasing. Every $j<n$ gives $x_n\ge x_{j+1}$, including equality at $j+1=n$, and $j=n$ gives $x_n<x_{n+1}$. The first no answer therefore occurs exactly at $j=n$. There are $n-b$ such comparisons and one initial read. All thresholds, scale names and outputs are computed from the fixed $b$ and finite loop index; the unknown exact source is never an input. The endpoint run has one read. Thus the rational decoder is correct and pointwise finite, with no common bound on $n$.

Apply the explicit subtractive decoder of Definition 6.3 to the recovered reduced pair: each inverse calculation on this known output pair strictly decreases the sum of its positive coordinates, until $(1,1)$. Reverse the peeled labels to recover the original chronological word. Executing that known word mathematically from the root gives the named incidence path and its indexed prefix table as in Theorems 6.2 and 17.3. These are computations of the original finite views, not inverse actions on the disturbed source. Conversely each of the three other views computes the exact original rational by those same finite transports. Therefore failure to distinguish $c$ from all smaller prior points in Theorem 30.1 precludes acquisition of every exact view when $b$ is missing. Unboundedness transports the displayed all-integer decoder through Theorem 29.2 on this unchanged prior. The two distinct rationals of (30.6) have distinct original words and hence distinct other exact views, giving the final bounded-menu assertion.

More generally, for any fixed promised prior the four exact-view tasks have equal acquisition membership for any one of the stationary or forward interfaces here, since their finite decoders can be composed after the same acquired output. In particular (30.5) is sharp even when its necessity witnesses are required to concern exact original four-view recovery: use $P_b$ for stationary necessity and (30.6) for forward necessity. This is a comparison with all-integer acquisition, not a claim that the full positive rational carrier is finitely acquirable. Theorem 18.3 excludes that full-carrier task from all these classes, and §24's effective stopping obstruction remains an additional requirement on every public presentation. $\square$

**Proposition 31.2 (identical prime marginals, different acquisition).** Let

$$
S_{\mathrm{pp}}=\{1\}\cup\{p^e:p\text{ prime},\ e\ge1\},\qquad
T=\mathbb N_{>0}.
\tag{31.1}
$$

These have effective staged enumerators and identical complete prime-valuation marginals: for every prime $p$,

$$
\{v_p(D):D\in S_{\mathrm{pp}}\}
 =\{v_p(D):D\in T\}=\mathbb N.
\tag{31.2}
$$

Nevertheless $\operatorname{Stat}(S_{\mathrm{pp}})$ is a proper subclass of $\operatorname{Stat}(T)$, while their forward acquisition classes agree with the all-integer stationary class. The dyadic menu $S_2=\{2^n:n\ge0\}$ likewise has universal forward power in this task sense and strictly smaller stationary power.

Proof. At stage $n$ one can list $1$ and all $p^e$ with prime $p\le n+2$ and $1\le e\le n+1$; trial division decides the finite primality tests. This enumerates $S_{\mathrm{pp}}$. Listing $n+1$ enumerates $T$, and listing $2^n$ enumerates $S_2$. For any fixed $p$, the value $0$ in (31.2) occurs at $1$, and every positive $e$ occurs at $p^e$. This proves equality of the full marginal sets, not merely equality of their suprema.

But $\operatorname{Div}(S_{\mathrm{pp}})$ contains precisely $1$ and prime powers; in particular it misses $6$. The target $\sigma_6$ on $P_6$ is acquired by the single stationary integer port $q_6$, and Theorem 30.1 excludes every stationary $S_{\mathrm{pp}}$-controller. The exact four-view task on $P_6$ gives the stronger consumed witness of Theorem 31.1. Separate reads at scales $2$ and $3$, or at any finitely many available prime powers, do not synthesize a $q_6$ port: at $c=1/6$ and a sufficiently close $c-1/n$ their finite transcripts agree by (30.3). What is required is the joint condition $\exists D\in S,\ b\mid D$ for a requested denominator $b$. The separate assertions $\forall p\mid b\ \exists D_p\in S,\ v_p(D_p)\ge v_p(b)$ have different quantifiers and are insufficient.

Both menus in (31.1) are unbounded, so Theorem 30.2 gives their identical universal forward power. The dyadic menu is unbounded with $\operatorname{Div}(S_2)=\{2^n:n\ge0\}$, missing $3$. Thus its forward universality and stationary failure follow from the same classification. The binary witness $P_3$ is exactly §26's prior after renaming its index; the one-$L$, one-$q_4$ controller there is a particularly short instance, while Theorem 29.2 handles every all-integer stationary task and arbitrarily many subsequent comparisons. The nested-chain raw-versus-predictive criterion of Theorem 16.4 is an antecedent about mathematical threads; (29.1)–(29.4) provide the actual sequential acquisition bridge needed for these menu conclusions. No LCM service is silently added to any restricted menu. $\square$

## 32. Finite resource contracts and mathematical suppliers

**Proposition 32.1 (per-run accounting for the transformations and decoders).** The constructions of §§29–31 have finite per-run action, read, encoding, enumeration, exact-computation, controller-memory, probe-memory and output costs under their stated promises. They imply no common budget, efficiency optimum, service implementation bound or equality of resource vectors between the compared controllers.

Proof. Fix one promised terminating all-integer stationary run used in Theorem 29.2. Let its successive requested scales and true reports be $m_t,K_t$ for $1\le t\le R$. The forward simulation makes exactly

$$
J=\sum_{t=1}^{R}(K_t+1)
\tag{32.1}
$$

actual floor reads. For comparison $i$, let $D_i$ be the enumerated scale chosen, $Q_i$ the actual report, $p_i/q_i$ the image of its original threshold under the current known matrix, and $\ell_i$ the length of its constructed continuation. The number of actual actions is exactly $H=\sum_{i=1}^{J}\ell_i$. All these integers are finite; a run with no virtual reads has $J=H=0$.

For each comparison the menu search executes finitely many entire stages up to its first success. Charge their actual computation steps and peak work space, including construction and scanning of their finite output lists. These costs cannot be bounded merely by the successful scale: an arbitrary public enumerator can delay a name or use large temporary data. The search is ordinary serial computation on the one supplied enumerator, not a free parallel enumerating thread. It can restart that computation from stage zero for each comparison; this resets no source. The modular searches have at most $p_i$ and $C_i$ trials. Euclid computes $g_i$ finitely. The row-descent has at most $A_i+B_i+C_i+F_i-2$ steps. In the displayed construction all four entries are at most $D_i$, so in particular

$$
\ell_i\le4D_i-2.
\tag{32.2}
$$

Store the peeled finite label list, then execute it in reverse and discard it. Charge each actual action and each local matrix update. Retaining four integer entries for the actual prefix is sufficient; no full unknown history or copy of the original source is stored.

Use $\operatorname{bits}(n)=1+\lceil\log_2(n+1)\rceil$ as a conservative finite integer encoding length, together with finite delimiters. Charge at least the actual scale-name and report payload totals

$$
\sum_{i=1}^{J}\operatorname{bits}(D_i),\qquad
\sum_{i=1}^{J}\operatorname{bits}(Q_i),
\tag{32.3}
$$

and charge the encodings scanned during enumeration separately. Exact arithmetic is charged by bit operations, not by treating unbounded integers as unit-cost reals. After $h$ actual actions, every entry of the prefix matrix is at most $2^h$, since a generator only replaces one row by its sum with the other. For a reduced original threshold $a/b$, its computed image integers satisfy $p,q\le2^h(a+b)$. The known image threshold therefore has operand width bounded in terms of $h$ and $\operatorname{bits}(a+b)$, and the modular and descent operands have widths bounded in terms of these quantities and $\operatorname{bits}(D_i)$. The grid integer $k_i=g_i(A_ip_i+B_iq_i)$ is computed with these same finite product widths. The accumulated matrix after executing the new word has entries at most $2^{h+\ell_i}$.

For a bound on actual report width, write the fixed original mathematically as $r/s$ in reduced positive form. Its attained positive numerator and denominator after $h$ actions are at most $2^h\max(r,s)$. Hence at comparison $i$ the returned integer is at most $D_i2^{h+\ell_i}\max(r,s)$. This is an analysis of a run's payload size, not exact $r/s$ supplied to its controller. Thus all report and comparison operands have finite explicit width bounds once the run's parameters are fixed. If $W_i$ is the maximum width of these operands, ordinary schoolbook integer addition, multiplication, division, remainder and comparison take finite bit work, with multiplication and division bounded by a constant times $W_i^2$ per operation. Euclid has finitely many such operations. The number of modular trials, row steps and matrix updates above therefore gives finite arithmetic work; the original simulated controller's computation and encoding work are charged as well.

Probe storage can be bounded by a constant times $\ell_i+W_i$ bits for the pending label list, prefix and working matrices, rational threshold, counters, grid integer and current report, using elementary arithmetic with linear working space. Add the simulated controller's actual peak state, the enumerator's actual peak state and the finite output buffer. A chosen implementation can discard each completed report after the controller consumes it; retaining a complete actual action/report archive instead incurs its additional $H$ action symbols and the payloads in (32.3), with delimiters. Neither choice includes an archive of the unknown pre-probe word. These bounds also charge the threshold loop index and scale arithmetic in (29.4).

For the stationary transformation in Theorem 30.1, each simulated read uses one actual read, zero source actions, a finite enumerator search for $F$, its encoded scale and complete report, and finite division by $F/D$. Charge that search's actual steps and work space exactly as above; an arbitrarily large listed multiple can enlarge both payload and memory. The reverse transformation used in (30.4) has the already declared cost of computing $\Lambda_D$, its scale and stationary report, the known simulated prefix and the exact rational arithmetic of (24.4). No equality of these costs is needed by the class inclusions.

Finally the stationary endpoint-prior decoder makes one read at $c$, and $1+n-b$ reads at $x_n$. Each later comparison threshold has a reduced denominator dividing $b(j+1)$, so its scale and numerator are finitely computed from $b,j$. Once a rational $r/s$ has been recovered, the subtractive original-word decoder has at most $r+s-2$ steps, with ancestor coordinates bounded by $r+s$. The recovered word, path and prefix table all have finite encodings. A literal table of all word prefixes uses $N(N+1)/2$ action symbols for a word of length $N$, in addition to its indices and any explicitly emitted boundary coordinates. Charge the entire selected finite output, rather than only its last rational entry. Composing this decoder with the forward transformation incurs its charged comparison costs before this output computation. Finite service completion is an interface premise; the service's internal physical time and memory have no quantitative law here. The acquisition proof uses neither their timing nor a promised bound on them. $\square$

**Definition 32.2 (supplier correspondence and the scope of the classification).** The new source-specific assertions are the repeated actual-prefix comparison (29.1)–(29.3), its use in simulating a whole all-integer stationary controller, and the consumed original-target menu classification (30.1)–(30.6), with the exact four-view witnesses in §31. They are `repo-derived` ordinary mathematical consequences, with no worldwide priority assertion. Their supplier contracts are:

| Supplier | Exact use and boundary |
| --- | --- |
| Theorems 11.2 and 15.2, especially (15.3) | Minimum predictive cut supplies the bounded-menu counterexample. The constructive modular argument with $D>pq$ supplies positive coefficients at the attained threshold; it is consumed in an actually executed continuation. Merely having a family of counterfactual predictive cuts does not implement the comparison. |
| [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `leftStep`, `rightStep`, `wordMatrix`, `unimodular_wordMatrix`, `wordMatrix_lower_right_pos` | The generators are exactly the nonnegative matrices of these $L/R$ maps. Chronological $u$ uses `wordMatrix(reverse u)`. The determinant and positive lower-right entry give the positive-domain matrix invariant. Lower-row coprimality is not a different source-response formula. |
| [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix`, and its row-descent proof | Every natural determinant-one matrix is generated. The ordinary row algorithm in Theorem 29.1 establishes finite effective realization with the required chronological reversal; no executed code extraction is inferred merely from the existential declaration. The descent is classical supporting arithmetic, with its repository adaptation attributed in [the existing HJO source note](../../../Library/PrimeForms/axiom2026unimodulardescent.md). |
| Assumption 24.1 and Theorem 24.3 | Public presentation, unchanged original target, effective stopping, and the all-integer reverse simulation are retained exactly. The positive transformations assume a correct supplied controller and appropriate menu property; they do not decide either, enumerate all homogeneous priors or cure the undecidable stopping examples of §25. |
| Theorems 6.2 and 17.3 | These supply finite mutual decoders only for the original rational source and its finite orbit. The comparisons preserve that original target despite changing the actual probe endpoint. No ambient cyclic-anchor history decoder is added. |
| Theorem 16.4 | Divisibility cofinality for nested raw and predictive towers is an antecedent. Here menus need not be chains, and both effective selection of names and execution along one actual source are required. Marginal prime valuations cannot replace the joint divisor set of an arbitrary menu. |

Classical modular inverses, floor arithmetic, subtractive Euclid and finite deterministic branch replay are supporting mathematics within these source-specific proofs. The represented-space results cited in Definition 24.2 retain their stated roles: Pauly [version 3, §§3–4](https://arxiv.org/html/1204.3763v3) supplies realizers and Sierpiński-valued open-set names; Schröder [Proposition 2.4](https://arxiv.org/html/2004.09450v1) states computability-implies-continuity for partial maps on Baire-space names. Neither supplies the sequential physical $L/R$ actions or an installed floor service. The matrix correspondences concern the actual Lean supplier statements, not new kernel verification of the ordinary menu theorems. The exact, unclipped, noiseless, pointwise finite contract here is different from the congruence or noise contracts of the Effective Resolution and Atomic Generation Acquisition volumes. No physical spacetime interpretation, resource optimality, identical final physical endpoint or identical acquired action archive is asserted.

## 追加锚（本行以下为增补区）

## 33. Exact action depth at an original endpoint under dyadic reads

**Definition 33.1 (the action coordinate and the unchanged tasks).** Retain exactly the positive-rational source, root, chronological actions and finite original-view encodings of §§6 and 17. The installed menu in this section is precisely

$$
S_2=\{2^s:s\in\mathbb N\},\qquad q_{2^s}(z)=\lfloor2^s z\rfloor.
\tag{33.1}
$$

The services are the conditionally supplied exact, noiseless, unclipped, nondisturbing services of Assumption 28.1. There is one actually mutated source. A controller is an ordinary deterministic finite program; its only source-dependent input is its finite acquired transcript. Every promised run must finish its actions, reads, finite arithmetic and finite output. No uniform bound is imposed on read count, exponent or scale magnitude, encodings, computation, retained state or output length. These remain paid coordinates. In particular the unbounded menu supplies neither an acquired infinite thread nor a source-dependent timing observation. There is no reset, copy, inverse source action, unknown original archive, unknown exact rational supplied as input, source-dependent advice or auxiliary oracle.

For public $b\ge1$, write the already defined prior (30.2) as

$$
c_b=1/b,\qquad x_{b,n}=1/b-1/n\quad(n>b),\qquad
P_b=\{c_b\}\cup\{x_{b,n}:n>b\}.
\tag{33.2}
$$

The binary target is the original endpoint bit $\sigma_b(c_b)=1$, $\sigma_b(x_{b,n})=0$. The other targets are separately the exact original rational boundary $B$, original chronological word $T$, original rooted named-incidence path $S$, original indexed prefix table $M$, and their joint tuple $(B,T,S,M)$. They are evaluated at the original cut, before any acquisition action. The mutual finite decoders of Theorems 6.2 and 17.3 are retained, including names, incidence orientation and prefix indices; none of these targets is replaced by a duration or a post-probe view.

For any one of these targets, its uniform action minimum is the least $h\in\mathbb N$ for which a correct pointwise-finite controller on all of $P_b$ uses at most $h$ actual new source actions on every original. Its endpoint action minimum imposes that bound only on the run starting at $c_b$, while retaining correctness and finite stopping on every member of $P_b$. Other runs in this second definition may use arbitrarily many actions. Local calculations with known words or rational candidates are not source actions.

**Lemma 33.2 (attained endpoint denominator and finite-branch obstruction).** For a chronological probe word $u$, put

$$
A_u=\operatorname{wordMatrix}(\operatorname{reverse}u)
 =\begin{pmatrix}a&e\\c&d\end{pmatrix},\qquad
f_u(x)=\frac{ax+e}{cx+d}.
\tag{33.3}
$$

The numerator and denominator in

$$
f_u(c_b)=\frac{a+be}{c+bd}
\tag{33.4}
$$

are positive and relatively prime. Hence this attained endpoint is on some dyadic floor grid if and only if $c+bd$ is a power of two, including $1$.

Every correct controller for $\sigma_b$ that stops finitely at $c_b$ must actually make a read at a chronological prefix $u$ for which this condition holds. The same necessity holds for each exact original view and for their joint output. It remains necessary if any fixed finite initial segment of the lower sequence $x_{b,n}$ is omitted from the prior.

Proof. The actual supplier `unimodular_wordMatrix` gives $ad-ec=1$, and `wordMatrix_lower_right_pos` gives $d\ge1$. The entries are nonnegative and $a\ge1$. Thus $P=a+be>0$, $Q=c+bd>0$, and

$$
dP-eQ=ad-ec=1.
\tag{33.5}
$$

Any common divisor of $P,Q$ divides $1$. This proves reducedness of the attained column-action fraction, rather than substituting the supplier's coprime lower-row fraction for it. Since $P,Q$ are coprime, $2^sf_u(c_b)$ is an integer for some $s\ge0$ exactly when $Q\mid2^s$, equivalently $Q$ is a power of two.

Fix the entire finite terminating run at $c_b$. List its reads as $(u_i,s_i)$, where $u_i$ is the actual chronological prefix already executed and $s_i$ is its chosen dyadic exponent. Suppose none of these reads is on an endpoint grid. Then the known rational numbers

$$
\theta_i=\{2^{s_i}f_{u_i}(c_b)\}
\tag{33.6}
$$

are all strictly positive. Here braces mean fractional part. A nonnegative determinant-one matrix with $d\ge1$ satisfies, for $0<y<x$,

$$
0<f_u(x)-f_u(y)
 =\frac{x-y}{(cx+d)(cy+d)}\le x-y.
\tag{33.7}
$$

Choose an integer $n>b$ larger than every $2^{s_i}/\theta_i$ and larger than any omitted finite initial indices. If there are no reads, any such $n$ suffices. This is an effective choice from the completed endpoint branch and $b$: all its matrices, exponents and fractional parts are finite known arithmetic. Then

$$
0<2^{s_i}\bigl(f_{u_i}(c_b)-f_{u_i}(x_{b,n})\bigr)
 \le 2^{s_i}/n<\theta_i,
\qquad
q_{2^{s_i}}(f_{u_i}(x_{b,n}))
 =q_{2^{s_i}}(f_{u_i}(c_b)).
\tag{33.8}
$$

Replay the program from $x_{b,n}$. Before any different report, deterministic local computations, requested scales and actions agree. At each listed read the prefix therefore really is $u_i$, and (33.8) gives the same report. Induction reproduces the whole finite branch, including its stopping choice and output. Name-only action labels give no additional distinction, and service timing is not an input. The endpoint bit differs, a contradiction. Thus some actual read must be on the endpoint grid. This argument uses a finite maximum only on the completed branch; no bound on the controller's other branches, read count, scales or arithmetic was assumed.

Each exact original view determines the original rational, which decides $\sigma_b$ by comparison with the known $c_b$. Composing this finite calculation after a hypothetical view acquisition adds no source action, so the same obstruction applies. The proof's choice of arbitrarily large $n$ also proves the finite-omission assertion. $\square$

**Definition 33.3 (a computable endpoint action number).** Define

$$
m(b)=\min\bigl\{|u|:u\in\{L,R\}^*,\quad
 c_u+b d_u\text{ is a power of two}\bigr\},
\tag{33.9}
$$

where $c_u,d_u$ are the lower entries of (33.3). This is a condition on an actually executable prefix for this same source, not on a combination of incompatible hypothetical continuations. A finite program computes both $m(b)$ and an attaining prefix as follows.

Start at $N=1$ and double $N$ until $N\ge b$; put $U=N-b$. The chronological word $L^U$ has matrix $\left(\begin{smallmatrix}1&0\\U&1\end{smallmatrix}\right)$, hence endpoint denominator $b+U=N$. Therefore the set in (33.9) is nonempty and

$$
0\le m(b)\le U=2^{\lceil\log_2 b\rceil}-b,
\tag{33.10}
$$

with $U=0$ at $b=1$. Enumerate chronological words in increasing length, breaking ties by a fixed $L<R$ order. Compute their matrices from the identity by left multiplication by the next generator. Test a positive integer $Q=c+bd$ for being a power of two by repeated division by $2$ until odd, accepting exactly when the remainder is $1$. The first accepted word has length $m(b)$, and the search finishes by length $U$. Given $b$ and a proposed cap $h\ge0$, enumerate only through $K=\min(h,U)$ to decide $m(b)\le h$, returning a shortest word on yes and no on exhaustion. This tests at most $2^{K+1}-1$ words, all by finite integer arithmetic. It is a genuinely finite decision, also on no instances; no unbounded existential matrix search is being used as the decision procedure.

## 34. Attainment with a complete original-target decoder

**Theorem 34.1 (one minimum for the bit and every exact original view).** For every public $b\ge1$, the uniform action minimum and the endpoint action minimum of Definition 33.1 both equal $m(b)$ for each of $\sigma_b,B,T,S,M$, and for $(B,T,S,M)$. A controller attaining the minimum uses exactly $m(b)$ source actions on every original of $P_b$, followed by reads and finite computations with no further source motion. Its endpoint run needs just one floor read. Thus the equality concerns actual acquisition of the original views, not merely separation by a potential test family.

Proof. Compute a shortest word $u$ by Definition 33.3, with matrix $A_u$, and its reduced endpoint $t=P/2^k$ from (33.4). Here $k\ge0$ and $P=a+be$. Actually execute the chronological $u$ once on the one original source, retaining its known matrix or action list. The present unknown response is $z=f_u(x)$. Read the installed port $q_{2^k}$ and obtain its complete report $Q$. Strict increase in (33.7) and the endpoint convention give

$$
Q\ge P\quad\Longleftrightarrow\quad z\ge t
 \quad\Longleftrightarrow\quad x=c_b\qquad(x\in P_b).
\tag{34.1}
$$

Indeed the report is exactly $P$ at the endpoint and at most $P-1$ at every smaller prior member. This already acquires $\sigma_b$. For an exact-view request, on this yes branch output the known original rational $c_b$ and compute the requested original view as below.

On the no branch the original is some $x_{b,n}$, with unknown finite $n>b$. Define known increasing rational thresholds at the current cut by

$$
t_j=f_u(x_{b,j}),\qquad
r_j=(t_j+t_{j+1})/2\qquad(j\ge b+1).
\tag{34.2}
$$

The actual $z=t_n$ never equals any $r_j$: $r_j$ lies strictly between two adjacent terms of the increasing sequence. There is an explicit stationary dyadic comparison with each such $r_j$. For $s=0,1,2,\ldots$, read $K_s=q_{2^s}(z)$, form the known rational endpoints

$$
\ell_s=K_s/2^s,\qquad v_s=(K_s+1)/2^s,
\qquad z\in[\ell_s,v_s),
\tag{34.3}
$$

and return below if $v_s\le r_j$, or above if $\ell_s>r_j$. Otherwise increase $s$. If $z<r_j$, eventually $v_s\le r_j$; if $z>r_j$, eventually $\ell_s>r_j$, because the interval width is $2^{-s}$ and $|z-r_j|>0$. Thus every comparison finishes finitely on the promised no branch. The program never inputs $z$ to an arithmetic operation: it computes only with the acquired integers, dyadic cells and known candidate thresholds. Nor does it require a uniform separation radius.

Starting at $j=b+1$, use this actual read loop for $r_j$. On above, increment $j$; on below, output the known original $x_{b,j}$. If the actual index is $n$, every $j<n$ has $z=t_n\ge t_{j+1}>r_j$, while $j=n$ has $z=t_j<r_j$. The first below answer therefore occurs exactly at $j=n$. There are finitely many comparisons and each finishes, so the entire decoder terminates. All these reads are made at the one attained cut after $u$; no candidate test executes a separate motion or restarts a source. The construction is also valid with a public tail starting at any $n_0>b$, by starting this loop at $j=n_0$.

Reduce the recovered original rational to its positive pair $(p,q)$. Use Definition 6.3's finite subtractive decoder: when $p<q$, peel $L$ and replace the known pair by $(p,q-p)$; when $p>q$, peel $R$ and replace it by $(p-q,q)$; equality forces $(1,1)$. The positive sum strictly decreases at each step. Reverse the peeled finite labels to obtain the original chronological word, then compute its named path and indexed prefix pairs from the root. These are ordinary calculations on the recovered original output, not inverse actions on the current source. They yield every requested exact original view and their joint tuple with no further source action. Their own arithmetic, storage and full finite output are charged.

This proves a uniform upper bound $m(b)$, also an endpoint upper bound. Conversely, on the terminating endpoint run of any correct bit controller, Lemma 33.2 forces a read after an actual prefix whose length is at least $m(b)$. Its endpoint action count is therefore at least $m(b)$. This lower bound holds even when other originals are permitted unlimited finite motion. The same lemma transfers it to each exact view and the joint target. A uniform cap is a cap at the endpoint, so all the claimed minima follow. $\square$

**Corollary 34.2 (an exact bounded-motion criterion).** For given $b,h$, acquisition on $P_b$ of any of these targets with at most $h$ actions everywhere is equivalent to acquisition with at most $h$ actions only at the endpoint, and both are equivalent to the finite arithmetic test

$$
\exists u\in\{L,R\}^{\le h}:\quad
c_u+b d_u\in\{1,2,4,8,\ldots\}.
\tag{34.4}
$$

The test and attaining original-target controller are those just constructed. The assertion does not infer acquisition from the existential test alone: (34.1)–(34.3) provide the actual one-source realization and its stopping proof. In particular $m(b)=0$ exactly when $b$ is a power of two. For such $b$ the empty prefix and $q_b$ already isolate the endpoint, after which the no-motion dyadic decoder recovers every exact original view pointwise finitely. This is not exact acquisition on the full rational carrier: the public sparse prior is essential.

Proof. The equivalences follow from Theorem 34.1 and Definition 33.3's finite decision. At length zero the matrix is the identity, so its endpoint denominator is exactly $b$. $\square$

## 35. Sharp witnesses at every action depth

**Theorem 35.1 (an exact hierarchy on the same original-view tasks).** Put

$$
b_j=4^j-j\qquad(j\ge0).
\tag{35.1}
$$

Then $m(b_j)=j$. Consequently, for each $h\ge0$, the original four-view task on the explicit decidable prior $P_{b_{h+1}}$ can be acquired with a uniform cap of $h+1$ actual source actions and cannot be acquired with a cap of $h$. This is a strict adjacent hierarchy for each of the four exact original views, their joint tuple, and the endpoint bit. Its lower bound holds even if the smaller cap is imposed only on the endpoint run. Arbitrarily fine dyadic reads, arbitrarily many finite reads and unbounded finite local computation do not remove it.

Proof. The case $j=0$ is $b_0=1$, with empty prefix. For every $j$, actually executing $L^j$ sends the endpoint to

$$
f_{L^j}(1/b_j)=1/(b_j+j)=1/4^j.
\tag{35.2}
$$

Thus $m(b_j)\le j$, with the full decoder of Theorem 34.1 available after these actions.

To prove the opposite inequality uniformly over all shorter words, let $j\ge1$, $h<j$, and $A_u=\left(\begin{smallmatrix}a&e\\c&d\end{smallmatrix}\right)$ for any chronological $u$ of length $h$. Two elementary bounds are

$$
c\le h d,\qquad 1\le d\le2^h.
\tag{35.3}
$$

For the first, evaluate the lower row arithmetically as $(0,1)$ multiplied on the right by the $h$ generators in the product for $A_u$. Right multiplication by $G_L$ changes its ratio $c/d$ to $c/d+1$; right multiplication by $G_R$ changes it to $(c/d)/(1+c/d)$. Starting at zero, the ratio after $h$ factors is at most $h$. This calculation uses the matrix product order, not a reversed actual source experiment. For the second bound, every matrix entry starts at most one, and left multiplication by a generator replaces one row by its sum with the other. The maximum entry at most doubles per step, and $d\ge1$ by the supplier invariant.

Set $\delta=jd-c$. Then

$$
0<\delta\le jd\le j2^{j-1}<4^j,
\qquad
c+b_jd=4^j d-\delta.
\tag{35.4}
$$

The strict positivity uses $c\le hd$ and $h<j$. The last strict inequality follows, for example, from $j\le2^j$. Also $b_j=4^j-j>4^j/2$ for $j\ge1$, so the candidate denominator is strictly above $4^j/2$. It is not divisible by $4^j$, since its remainder is $-\delta$ with $0<\delta<4^j$. But any power of two strictly above $4^j/2=2^{2j-1}$ is divisible by $4^j=2^{2j}$. Therefore no word of length $h<j$ gives a dyadic endpoint denominator. This is a proof for every shorter word, rather than a bounded enumeration extrapolated to all $j$.

Thus $m(b_j)\ge j$ and equality holds. Theorem 34.1 gives the stated acquisition hierarchy on the unchanged original-view tasks; allowing an extra action trivially includes every controller with the smaller cap, while this prior separates adjacent caps. $\square$

**Proposition 35.2 (the next-power all-left bound can be strictly nonoptimal).** At $b=9$, the exact value is $m(9)=4$, whereas (33.10) gives the convenient upper bound $16-9=7$.

Proof. The actually executable chronological word $LRLL$ has

$$
A_{LRLL}=G_LG_LG_RG_L
 =\begin{pmatrix}2&1\\5&3\end{pmatrix},\qquad
f_{LRLL}(1/9)=11/32.
\tag{35.5}
$$

Its denominator is dyadic. For completeness, the endpoint denominators for all shorter chronological words, with multiplicity removed separately at each length, are

| Length | Values of $c+9d$ |
| --- | --- |
| $0$ | $9$ |
| $1$ | $9,10$ |
| $2$ | $9,10,11,19$ |
| $3$ | $9,10,11,12,19,21,28,29$ |

These rows follow by left-multiplying each preceding matrix by both generators; they exhaust $1+2+4+8=15$ words. None is a power of two. Equations (33.9) and (35.5) give the exact minimum four. The word and the finite exclusion certify this one parameter; they are not the universal proof of Theorem 35.1. The reducedness argument in Lemma 33.2 is needed here too: it is the denominator of $11/32$ at the attained endpoint, not the matrix's lower-row ratio. $\square$

## 36. One decidable prior with no finite uniform action cap

**Definition 36.1 (one fixed rational presentation).** Using just the integers $b_j=4^j-j$ for $j\ge1$, specify the single prior

$$
\begin{aligned}
\mathcal Q_j&=\{1/b_j\}\cup
 \{1/b_j-1/n:n\in\mathbb Z,\ n\ge2b_j\},\\
\mathcal Q&=\bigcup_{j\ge1}\mathcal Q_j.
\end{aligned}
\tag{36.1}
$$

This is one finite source-independent code using exponentiation, rational arithmetic and integer tests. It supplies no unknown index or rational as input to the acquisition controller. Each member is the response of a unique finite original $L/R$ history by Theorem 6.2.

Membership in $\mathcal Q$ is decidable on finite rational inputs. Reject nonpositive inputs. For a positive input $y$, iterate $j=1,2,\ldots$, computing $b_j$ and $c_j=1/b_j$. Accept $y=c_j$; when $0<y<c_j$, accept exactly if $1/(c_j-y)$ is an integer at least $2b_j$. If neither condition succeeds, continue, except that as soon as $c_j<y$ reject: all later endpoints and their lower sequences are smaller. The endpoints strictly decrease to zero, so this loop halts on every positive rational input. This input convention is for the public membership decider; the acquisition program below is given only reports from its unknown original.

For effective identification of the band without source motion, use the disjoint open dyadic intervals

$$
J_j=(2^{-(2j+1)},2^{-(2j-1)})\qquad(j\ge1).
\tag{36.2}
$$

Since $4^j/2<b_j<4^j$, every member of $\mathcal Q_j$ lies in $[1/(2b_j),1/b_j]\subset J_j$. Adjacent $J_j$ share just a boundary in their closures, and no such boundary belongs to a band. Hence the actual band is unique.

**Theorem 36.2 (pointwise finite actual recovery without any uniform action bound).** On the single fixed prior $\mathcal Q$, each exact original view and their joint tuple is forward acquirable by an ordinary finite program with dyadic reads and pointwise finite stopping. No correct pointwise-finite program for any of these targets has a finite uniform bound on actual new source actions. In fact no single finite cap can bound just its action counts at all the original endpoints $1/b_j$.

Proof. Here is one actual acquisition program, including effective band selection. For stages $s=0,1,2,\ldots$, read $K_s=q_{2^s}(x)$ at the still unchanged source and compute its cell $[K_s/2^s,(K_s+1)/2^s)$. Test the finitely many $j=1,\ldots,s+1$ for the rational inequalities

$$
2^{-(2j+1)}<K_s/2^s,
\qquad
(K_s+1)/2^s<2^{-(2j-1)}.
\tag{36.3}
$$

When one succeeds, retain that $j$ and end the band loop. The entire nonempty observed cell is then inside $J_j$, so the promise forces the original into $\mathcal Q_j$. For an actual $x\in\mathcal Q_j$, its distances to both boundaries of $J_j$ are positive. Eventually the mesh is smaller than both distances and $s+1\ge j$, so (36.3) succeeds. Thus the loop stops finitely on every promised original, with no source action. Every read is a real service invocation, not a request for an unobserved exact input or an infinite list.

Now actually execute $L^j$ on that same source, which has remained unchanged throughout band selection. Equation (35.2) sends its known endpoint threshold to $1/4^j$. Read $q_{4^j}$; its report is $1$ exactly at the original endpoint and $0$ at every smaller member of $\mathcal Q_j$. On report $1$ recover $1/b_j$. On report $0$ use precisely (34.2)–(34.3), with $u=L^j$ and starting index $n_0=2b_j$. The proof there gives finitely many stationary dyadic comparisons and returns the correct original rational $1/b_j-1/n$. Apply the same finite original-word, path and prefix-table decoders as in Theorem 34.1. This is one program, containing band arithmetic, two finite loops, the known action sequence and the original-view decoder. Each run makes exactly $j$ new source actions, with finitely many reads, arithmetic steps and storage cells and a completed finite output.

For the lower bound, suppose a correct program has some uniform action cap $h$ on the endpoints, while still stopping correctly everywhere in $\mathcal Q$. Choose $j>h$ and consider its finite run at $1/b_j$. Its restriction to $\mathcal Q_j$ must distinguish this endpoint from every $1/b_j-1/n$ with $n\ge2b_j$, because exact original views distinguish unequal original rationals. Lemma 33.2 applies to this tail: a sufficiently large such $n$ replays any endpoint branch lacking an attained dyadic grid read. Theorem 35.1 excludes a dyadic endpoint after every prefix of length at most $h<j$. Thus the run cannot be correct on the tail, a contradiction. Equivalently, every correct program must use at least $j$ actions at this endpoint; the displayed program attains $j$ there. All originals in this argument belong to the same fixed prior, source law, menu and original target. $\square$

This is stronger than choosing a different $P_b$ after a proposed cap is announced: one finitely presented decidable prior and one ordinary finite-code exact acquisition task already lie beyond every finite uniform action cap. It is consistent with Theorem 34.1: for each fixed $P_b$, $m(b)$ is finite, whereas $\mathcal Q$ contains infinitely many separated tails with endpoint requirements tending to infinity. The construction does not acquire a dense full-rational prior; its bands and endpoint promises supply the needed finite stopping information. Unrestricted actual motion means no common finite cap, with each individual run still finite.

## 37. Resource boundaries and suppliers of the action theorem

**Proposition 37.1 (what the action optimum measures).** The action minima above remain valid when there are no uniform bounds on finite read count, dyadic exponent, scale magnitude, exact arithmetic or retained storage. Equality of these action minima for the bit and the exact views asserts no equality of their output, memory, read, time or service costs.

Proof. The lower bound uses only the finitely many completed reads on one terminating endpoint branch. An arbitrarily large exponent still gives a strictly positive rational fractional part in (33.6) whenever its attained endpoint is not dyadic; increasing the chosen $n$ in (33.8) defeats any finite list of such exponents. More finite computation on identical reports gives identical decisions. A hypothetical family of all dyadic tests, without a finite executed stopping certificate, is outside this argument's positive model. The attained grid read is precisely the extra distinction supplied by actual motion.

In the attaining controller on $P_b$, the precomputed word search is finite, with the finite cap (33.10). Its candidate matrices, denominator tests and loop counters are paid exact arithmetic on encoded integers. It performs exactly $m(b)$ actual actions and one initial read. On a lower point $x_{b,n}$ it then makes one finite refinement loop for each $j=b+1,\ldots,n$. If loop $j$ stops at exponent $s_j$, it uses $s_j+1$ reads when started at zero, so this implementation's total read count is

$$
1+\sum_{j=b+1}^{n}(s_j+1).
\tag{37.1}
$$

There is no common bound on these indices or read counts. Exponent $s$, its scale name $2^s$, and the complete report $K_s$ are distinct encoded quantities. For example a binary exponent name has length of order $\log(s+1)$, while explicitly writing the scale integer needs $s+1$ binary digits; whichever legal name encoding is chosen, charge the actual name and all scale construction work. Charge each full integer report, not just the final bit of a comparison. Service-internal time and workspace are paid coordinates whose quantities remain unspecified. Finite service completion is assumed; no quantitative bound on service-internal time, workspace or physical accuracy is derived.

After $m$ actions matrix entries are at most $2^m$, so the first endpoint denominator and numerator are at most $(b+1)2^m$. Computing them and writing the first dyadic scale and report is finite, but not unit-cost arithmetic. The later rational thresholds, dyadic cells, local comparisons and counters have finite widths on each terminating run; all their bit operations and peak working memory are charged. One can retain the known prefix matrix, the current candidate index, threshold, exponent and report, rather than a permanent report archive. Retaining a complete actual action/read transcript incurs its additional finite encoding and storage. Neither implementation has an archive of the unknown original history.

In the controller for $\mathcal Q$, add all band-selection reads, the band index and its arithmetic before the $j$ paid actions. Then charge the same decoder with starting index $2b_j$. Band selection has no source action, but its read count, exponents, reports and computation are not free. Finally, for a recovered reduced pair $(p,q)$ the original subtractive word decoder has at most $p+q-2$ inverse calculations on that known pair. Its word, all named incidences and all indexed prefix pairs are finite outputs whose lengths and storage must be charged in full. They can be much larger than the one-bit endpoint output even though no extra source motion is required. Thus optimizing one coordinate has not identified or optimized the whole resource vector. $\square$

**Definition 37.2 (mathematical provenance and retained limits).** The source-specific additions are the exact attained-denominator/finite-branch criterion, the action-optimal original-target decoder, the sharp family $4^j-j$, and the single fixed decidable prior with unbounded action requirements. They are `repo-derived` ordinary mathematical results with proofs above, not a worldwide priority claim. Supporting arithmetic and its supplier boundaries are as follows.

| Antecedent | Exact use and limit |
| --- | --- |
| §§6 and 17, especially Definition 6.3 and Theorems 6.2 and 17.3 | Finite decoders of the same original positive-rational boundary, literal chronology, named path and indexed prefix memory. Reconstructing these original outputs from a recovered rational adds local work but no source action. Ambient nonrational threads and the cyclic-anchor histories of §§20–23 do not acquire these decoders. |
| §§24 and 28–32 | Public prior presentations, ordinary effective stopping, complete exact floor reports, sequential one-source operation and the pointwise finite menu results. Those results provide neither the optimum (33.9) nor a uniform action bound. Theorem 15.2's equation (15.3) is earlier fixed-scale saturation arithmetic; it is not the bounded-action minimum proved here. |
| [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `leftStep`, `rightStep`, `wordMatrix`, `unimodular_wordMatrix`, `wordMatrix_lower_right_pos`, `word_node_is_reduced` | Exact nonnegative generators, recursive word product, determinant one, positive lower-right entry and coprime lower row. Actual chronological actions multiply on the left, hence use `wordMatrix(reverse u)`. The lower-row rational is not the attained response; equation (33.5) supplies the additional transformed-endpoint reducedness argument. |
| [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix` and its descent | Natural determinant-one matrices are finite words. The source's arithmetic adaptation and attribution remain those in the module and [its HJO note](../../../Library/PrimeForms/axiom2026unimodulardescent.md). The finite bounded word enumeration here computes an optimum directly and does not infer a length bound or executable controller from that existential theorem. |
| Gibbons–Lester–Bird, *Enumerating the Rationals*, [author manuscript, §§2 and 4](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/rationals.pdf) | Positive-integer subtractive Euclid, execution-path inversion, rational trees and reversal of paths support the original decoder and orientation convention. These are classical arithmetic antecedents, not an acquisition theorem about this dyadic service or its action optimum. |
| Han–Masuda–Singh–Thiel, *The $(u,v)$-Calkin–Wilf Forest*, [version 2, introduction and §5](https://arxiv.org/html/1411.1747v2) | At $u=v=1$, the root and children are exactly $1$, $z/(z+1)$ and $z+1$, with the stated column-action matrices. Its word convention reverses chronological path bits; its descendant/depth discussion concerns the rational trees. It supplies neither our installed floor ports nor original-target finite stopping or action optimality. |

These correspondences concern the cited literature conditions and actual Lean source statements. They are not fresh compilation or new kernel verification of §§33–37. The exact noiseless unclipped floor interface remains a supplied mathematical assumption, with no physical implementation or noise robustness claim. The full-rational finite acquisition obstruction of Theorem 18.3, effective-presentation obstructions in §25, and all original-versus-disturbed distinctions remain in force. There is no acquired infinite observation thread, physical spacetime theorem or completion of the continuing RRO program.

## 追加锚（本行以下为增补区）

## 38. Acquired routing strictly reduces the original-view action budget

**Definition 38.1 (one public prior and the two action contracts).** Retain the positive-rational process rooted at $1$, chronological actions $L(z)=z/(1+z)$ and $R(z)=z+1$, ORIGINAL views $B,T,S,M$ of §§6 and 17, and precisely the supplied dyadic services of Definition 33.1. Fix the single public prior

$$
c_0=\frac16,\qquad c_1=\frac23,\qquad
x_{i,n}=c_i-\frac1n\quad(i\in\{0,1\},\ n\in\mathbb Z,\ n\ge12),
\qquad P_i=\{c_i\}\cup\{x_{i,n}:n\ge12\},\qquad P=P_0\cup P_1.
\tag{38.1}
$$

This is one source-independent finite presentation: emit $c_0,c_1$, then emit $x_{0,n},x_{1,n}$ for successive integers $n\ge12$. Membership is decidable on any finitely encoded rational $y$: for each of the two $i$, accept if $y=c_i$, or if $y<c_i$ and the exactly computed $1/(c_i-y)$ is an integer at least $12$; otherwise reject. These are finitely many rational operations and integer tests. The decider's input is a candidate rational, not an extra input to the acquisition controller. Every member is positive and has exactly one original finite history by Theorem 6.2. Moreover

$$
P_0\subset[1/12,1/6],\qquad P_1\subset[7/12,2/3],\qquad
q_2(x)=i\quad(x\in P_i).
\tag{38.2}
$$

Thus an actually acquired initial $q_2$ report identifies the band, without identifying its unknown rational, endpoint status or tail index.

A record-dependent action controller may select its next physical $L/R$ action from its acquired records and local state. A preset action controller instead has one public source-independent finite word or effectively generated infinite schedule $v_1v_2\cdots$: its $k$th executed action must be $v_k$. It may pause for reads and computation or stop at any prefix, but may not skip, replace, reorder or restart letters. In BOTH classes dyadic scales, read count, finite local work and stopping are allowed to depend on all acquired reports. Both have common source-independent initialization and ordinary deterministic finite code. For $V\in\{B,T,S,M,(B,T,S,M)\}$, let $h_{\rm rec}(V)$ and $h_{\rm pre}(V)$ be their respective least uniform caps on actual new source actions among controllers that correctly output the exact ORIGINAL $V$ and stop finitely on every $x\in P$.

There is only one current source: every physical prefix is executed on it in chronological order. The exact, noiseless, unclipped, nondisturbing, finite-completing services remain a conditional mathematical grant. No reset, copy, inverse source action, unknown original archive, exact unknown input, hidden source advice, timing channel, auxiliary oracle or acquired infinite thread is supplied. Every other resource is paid and finite on each run; no uniform bound or unit-cost convention is imposed on those resource coordinates.

**Lemma 38.2 (endpoint replay and incompatible short routes).** In this prior, a correct finitely stopping acquisition of any one of the five targets must, on each endpoint run $c_i$, actually read a dyadic port at an attained dyadic endpoint. Through length three the only prefixes that can supply such a read are $LL,LLR$ for $c_0$, and $RL,RLR$ for $c_1$. In particular no prefix of length at most one suffices for either endpoint, and no single chronological chain of length at most three contains sufficient prefixes for both.

Proof. The finite-branch argument of Lemma 33.2 extends from $1/b$ to every reduced positive rational $r=p/q$. For a chronological $u$ use the actual supplier convention

$$
A_u=\operatorname{wordMatrix}(\operatorname{reverse}u)
 =\begin{pmatrix}a&e\\c&d\end{pmatrix},\qquad
f_u(r)=\frac{P_u}{Q_u},\qquad P_u=ap+eq,\quad Q_u=cp+dq.
\tag{38.3}
$$

Its nonnegative entries have $ad-ec=1$ and $d\ge1$. Both transformed coordinates are positive, and the integer identities

$$
dP_u-eQ_u=p,\qquad aQ_u-cP_u=q
\tag{38.4}
$$

show that a common divisor of $P_u,Q_u$ divides the coprime $p,q$. Thus the attained fraction is reduced, and it is dyadic exactly when $Q_u$ is a power of two, including $1$. This is transformed-column reducedness, not the distinct lower-row coprimality statement `word_node_is_reduced`.

Fix the complete finite terminating endpoint branch at $c_i$, with actual reads $(u_j,s_j)$ meaning $q_{2^{s_j}}$ after actual prefix $u_j$. Suppose that none of these executed reads is at a grid point, so that $\theta_j=\{2^{s_j}f_{u_j}(c_i)\}>0$. The determinant identity gives, for positive $y<r$,

$$
0<f_u(r)-f_u(y)=\frac{r-y}{(cr+d)(cy+d)}\le r-y.
\tag{38.5}
$$

Choose one integer $n\ge12$ strictly larger than every $2^{s_j}/\theta_j$. With no reads any $n\ge12$ suffices. Then $y=x_{i,n}>0$ and

$$
0<2^{s_j}\bigl(f_{u_j}(c_i)-f_{u_j}(x_{i,n})\bigr)
 \le 2^{s_j}/n<\theta_j.
\tag{38.6}
$$

Consequently every complete integer report on that branch is unchanged. Starting from common initialization, determinism replays all local decisions, scale requests, actual actions, report-dependent choices and the final stop and output. Induction at each actual read justifies using that same $u_j$ on the lower original; no incompatible candidate continuations are combined. Action labels reveal only the chosen names and service timing is unavailable. Yet every exact ORIGINAL view distinguishes $c_i$ from $x_{i,n}$, since its finite decoder recovers their unequal original rationals. This is a contradiction. Some executed read therefore has $2^{s_j}f_{u_j}(c_i)$ integral. This implies a dyadic attained endpoint by (38.3)–(38.4); attaining a dyadic rational without executing a sufficiently fine grid read would not alone discharge the replay obstruction. No bound on other runs, scales, read count or local work entered the argument.

Here is the complete short-prefix denominator calculation. Starting separately at the two KNOWN endpoint pairs $(1,6)$ and $(2,3)$ for this arithmetic, extend each chronological prefix using $L:(P,Q)\mapsto(P,P+Q)$ and $R:(P,Q)\mapsto(P+Q,Q)$. These are hypothetical calculations of public thresholds; an acquisition run never receives either unknown pair as input. Reducedness above makes the displayed denominators decisive.

| Chronological prefix $u$ | Reduced denominator at $c_0$ | Reduced denominator at $c_1$ |
| --- | --- | --- |
| $\varepsilon$ | $6$ | $3$ |
| $L$ | $7$ | $5$ |
| $R$ | $6$ | $3$ |
| $LL$ | $8$ | $7$ |
| $LR$ | $7$ | $5$ |
| $RL$ | $13$ | $8$ |
| $RR$ | $6$ | $3$ |
| $LLL$ | $9$ | $9$ |
| $LLR$ | $8$ | $7$ |
| $LRL$ | $15$ | $12$ |
| $LRR$ | $7$ | $5$ |
| $RLL$ | $20$ | $13$ |
| $RLR$ | $13$ | $8$ |
| $RRL$ | $19$ | $11$ |
| $RRR$ | $6$ | $3$ |

Every word of lengths zero through three occurs: start from the empty word and append both letters at each of the three levels. Testing for powers of two leaves exactly the two pairs of prefixes in the statement. The first pair starts with $L$, the second with $R$, so they cannot belong to one prefix chain. $\square$

**Theorem 38.3 (exact acquired-control and preset action prices).** On the ONE prior (38.1), with the complete opponent permissions of Definition 38.1, each exact ORIGINAL view and their joint output have

$$
\boxed{h_{\rm rec}(V)=2,\qquad h_{\rm pre}(V)=4}
\qquad\bigl(V\in\{B,T,S,M,(B,T,S,M)\}\bigr).
\tag{38.7}
$$

An attaining record-dependent controller uses the acquired band report to execute $LL$ on $P_0$ and $RL$ on $P_1$. An attaining preset schedule is $LLRL$, stopping physical motion after its first $LL$ on $P_0$ and after all four letters on $P_1$. Both complete the requested original output by finitely many stationary reads and finite calculations at their chosen attained cut.

Proof. Lemma 38.2 excludes a uniform record-dependent cap below two. For any preset cap at most three, both finitely terminating endpoint runs must have grid reads at prefixes of one common schedule's first three letters. The two required prefix sets are incompatible. Adaptive scales, arbitrarily long finite computation and early stopping do not change this chain, so the lemma excludes the entire preset opponent class with cap at most three. These lower bounds apply separately to each view and the joint output.

For the upper bounds, first ACTUALLY read $q_2$ at the original cut and retain its report $i$. In the record-dependent construction execute the chronological $u_0=LL$ or $u_1=RL$ as selected by $i$. In the preset construction the schedule is fixed to $LLRL$: execute $LL$ if $i=0$, or continue from that SAME attained cut through $RL$ if $i=1$. The initial report controls only how long this preset schedule runs, never its next letter. The public matrices and attained endpoints are

$$
A_{LL}=\begin{pmatrix}1&0\\2&1\end{pmatrix},\qquad
A_{RL}=\begin{pmatrix}1&1\\1&2\end{pmatrix},\qquad
A_{LLRL}=\begin{pmatrix}3&1\\5&2\end{pmatrix},
\qquad
f_{LL}(c_0)=\frac18,\quad
f_{RL}(c_1)=\frac58,\quad
f_{LLRL}(c_1)=\frac9{16}.
\tag{38.8}
$$

Let $u$ be the executed prefix, $z=f_u(x)$ its current unknown response, and $t=f_u(c_i)=K/D$ the corresponding known endpoint in (38.8), with $(K,D)=(1,8),(5,8)$ or $(9,16)$. Actually read $q_D(z)$. Strict increase of $f_u$ and $x\le c_i$ imply

$$
q_D(z)=K\quad\Longleftrightarrow\quad x=c_i;
\qquad x<c_i\quad\Longrightarrow\quad q_D(z)\le K-1.
\tag{38.9}
$$

On the equality branch the original rational is the known $c_i$. On the other branch it is some $x_{i,n}$, with unknown finite $n\ge12$. Here is a full stationary decoder, specializing the existing lower-tail procedure (34.2)–(34.3) without adding a source operation. From public $i,u$ and a local integer $j\ge12$, compute

$$
t_j=f_u(c_i-1/j),\qquad r_j=(t_j+t_{j+1})/2.
\tag{38.10}
$$

For this $r_j$, start $s=0$ and ACTUALLY read $k_s=q_{2^s}(z)$ at the SAME current cut. Form the known cell $[\ell_s,v_s)=[k_s/2^s,(k_s+1)/2^s)$. Return below if $v_s\le r_j$, above if $\ell_s>r_j$, and otherwise increment $s$ and read again. These finite instructions use only the complete acquired report and public rational thresholds. The strictly increasing sequence $t_j$ has no term equal to $r_j$. Hence $z=t_n\ne r_j$, and a dyadic width $2^{-s}<|z-r_j|$ suffices for the corresponding stopping inequality. Every comparison therefore finishes finitely on this promised branch, including when $z$ itself is dyadic.

Start $j=12$. On above increment $j$ and make the next stationary comparison; on below output the known original $c_i-1/j$. For $j<n$, $z=t_n\ge t_{j+1}>r_j$; at $j=n$, $z=t_j<r_j$. Thus the first below answer is exactly at $n$. The decoder performs $n-11$ comparisons, each with finitely many finite-completing reads, and returns the exact original rational. It never waits to infer equality with a nondyadic rational from endless refinement. Equality is handled by the attained grid read (38.9). Neither a candidate test nor a refinement loop re-executes $u$ or restarts from the original.

Finally reduce this recovered ORIGINAL rational to its positive pair $(p,q)$. Apply Definition 6.3: for $p<q$ record a peeled $L$ and replace the known pair by $(p,q-p)$; for $p>q$ record $R$ and replace it by $(p-q,q)$; at equality the pair is $(1,1)$. Each step decreases $p+q$, so this calculation terminates. Reverse the peeled labels to get the original chronological word $T$. Compute its prefix pairs from $(1,1)$, the root-oriented incidence path with those named edges $S$, and the table $M=((k,\operatorname{enc}(T|_k)))_{0\le k\le|T|}$, retaining the indices. The recovered rational is $B$. This is precisely the finite four-view transport of Theorems 6.2 and 17.3. Subtractions on the now known output pair are mathematical inverse calculations, not inverse physical source operations. Compute the requested single view or all four and finish its entire finite output; no more source action is needed.

The two constructions therefore stop correctly on EVERY member of $P$, including both accumulation endpoints, with action caps two and four respectively. The lower bounds already proved make both caps minimal. Their equality across targets follows also by composing the existing finite actual-image decoders after any acquired view; that composition adds paid local work and output, and zero source actions. $\square$

**Corollary 38.4 (acquired distinctions are consumed by short control).** Every successful controller of Definition 38.1 with a uniform action cap at most three must choose its first physical action to be $L$ on original $c_0$ and $R$ on original $c_1$. Therefore its actually acquired records before the first action must distinguish those two endpoint runs. The actual initial report $q_2$ supplies a sufficient routing bit. This is not a one-bit total or permanent memory optimum.

Proof. Neither endpoint can stop before acting by Lemma 38.2. Every length-at-most-three prefix beginning with $R$ misses a dyadic attained endpoint at $c_0$, and every such prefix beginning with $L$ misses one at $c_1$, by the complete table. The finite terminating endpoint branch must contain a grid read, forcing the stated first actions. With common initialization, no hidden advice and no timing input, identical acquired histories would give identical local computations, requests and first actions. Thus the two histories must differ before that choice. Any retained selector or branch of the instruction pointer carrying this distinction is part of the consumed internal control, even if its raw report is later erased. Equation (38.2) supplies that distinction by a genuine source read, without knowledge of the exact original or its index.

For the displayed implementations retain $i$, the executed prefix or its known matrix, the current phase, and then the candidate index $j$, exponent $s$, threshold and cell arithmetic and complete integer report. A controller may consume reports and discard them instead of keeping a permanent archive; keeping them costs their full encodings. On an endpoint run there are two reads, the initial $q_2$ and the attained grid read. On $x_{i,n}$, if comparison $j$ stops at exponent $s_j$, the displayed implementation makes

$$
2+\sum_{j=12}^{n}(s_j+1)
\tag{38.11}
$$

reads. These counts, exponents, scale names, full report payloads, counters, local bit arithmetic, transient and retained workspace, service work and full original outputs remain separately paid. For example, writing the explicit scale integer $2^s$ costs $s+1$ bits; using an exponent name changes the name encoding, not the need to charge it and construct the requested service call. Finite service completion gives no quantitative implementation bound. Original-word decoding takes at most $p+q-2$ subtractions on the recovered pair, and its named path and indexed table must be emitted in full. No uniform bound or optimum for any of these other coordinates follows from (38.7), and no persistent one-bit interface sufficient for all original outputs has been asserted. $\square$

**Proposition 38.5 (the finite-prior boundary).** With the same dyadic service and arbitrary finite refinement, any publicly listed finite rational prior admits acquisition of each exact ORIGINAL view and their joint output at the original cut with zero source actions. Consequently (38.7) hides no precision cap; the infinite lower sequences with their INCLUDED accumulation endpoints supply its replay obstruction.

Proof. Remove duplicate entries from a finite list. If it has at least two members, compute its positive minimum pairwise distance $\delta$. Choose $s$ by successive doubling until $2^{-s}<\delta$. Two listed rationals cannot have the same floor report $q_{2^s}$, since one such cell has width $2^{-s}$. Computing all candidate reports gives a finite public inverse table; one actual read identifies the original rational. A singleton needs no read, and the empty prior is vacuous. Apply the same finite original-output decoders. The selected scale and inverse table are computed independently of the actual source, and their sizes and work are paid. This is compatible with Theorem 13.2, which fixes a single listed prior AND one scale; it does not impose that scale on the present comparison. For (38.1), however, every finite endpoint branch without a grid read has a distinct sufficiently close included lower original replaying it, as in (38.6). Arbitrarily large but finitely many exponents do not remove that fact. This identifies the obstruction used here, without asserting that every infinite prior has a control separation. $\square$

**Definition 38.6 (antecedents and exact scope of the new consequence).** The new `repo-derived` ordinary result is the incompatible attained-grid routing on ONE fixed decidable prior, with the exact prices (38.7), the all-domain ORIGINAL-output controllers, and the consumed pre-action distinction of Corollary 38.4. It advances finite acquisition of the already mutually recoverable original boundary, chronology, named path and indexed memory by identifying a precise role for internal acquired control. It does not rediscover generic benefit from adaptivity. The mathematical antecedents and their conditions are:

| Supplier | Reuse and boundary |
| --- | --- |
| This volume, §§6 and 17; §§13 and 28–37 | Exact original four-view decoders, finite-prior/fixed-scale criterion, effective dyadic menu, same-source sequential contract, endpoint replay, attained-denominator arithmetic and stationary lower-tail decoding. Lemma 38.2 extends the reduced-endpoint calculation to $p/q$; the short-route incompatibility and its joint use on (38.1) give the new action comparison. The earlier one-endpoint optimum and hierarchy are retained, not reproved as new outcomes. |
| [Adaptive Acquired Reference Frontier, Definition 13.1, Corollary 13.9 and §16](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md#13-exact-native-acquisition-of-one-declared-future-literal) | Exact adaptive and preset literal-query prices, already allowing a fixed source-independent query list to stop early. Those reads address an original-root stationary bounded-height native tree, with no $\rho$ during acquisition, and acquire passive future predictions. Here the measured letters are actual noncommuting source mutations and the target is the ORIGINAL rational four-view output. Neither native query counts nor that joint-menu recurrence is an action-price theorem for this source. |
| [Native Adaptive Selection Fibers](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ADAPTIVE_SELECTION_FIBERS.md), [Symbolic Feedback Synthesis](RECURSIVE_RELATIONAL_OBSERVATION_SYMBOLIC_FEEDBACK_SYNTHESIS.md), [Transport Memory Completion §§31.4–31.5 and 52](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#314-有限控制载体与来源调用界) | Their native-tree writer/read, complete acquired-row or paid preparation/record contracts remain distinct. They supply neither an unknown rational input nor a free pre-action selector here. Control fields and complete accessible records must be charged under their stated scopes as well as this one. |
| [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `leftStep`, `rightStep`, `wordMatrix`, `unimodular_wordMatrix`, `wordMatrix_lower_right_pos`, `word_node_is_reduced`; [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix` | Actual source declarations fix the generators, recursive product, determinant, positive $d$, lower-row coprimality and existential matrix generation. Chronology reverses supplier words. Equations (38.3)–(38.4) prove the needed attained-column reducedness separately. The three explicit matrices in (38.8) require no general optimizer, word-length consequence or executable-code extraction from the generation theorem. Its existing HJO attribution remains as in [the source note](../../../Library/PrimeForms/axiom2026unimodulardescent.md). |
| van den Bos–Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, version 2, §4, Definitions 10–11 and Figure 3](https://arxiv.org/html/1907.11034v2) | Distinguishing test cases separate observable traces, and adaptive distinguishing graphs allow outputs to determine later tests. Figure 3's first-step state-merging obstruction is a classical comparison, not our mechanism: each rational $L/R$ map here is injective, and the wrong short route fails to hit a needed floor grid. Suspension-automaton existence or finite-state bounds are not transferred. |
| Panteleev, [*Preset Distinguishing Sequences and Diameter of Transformation Semigroups*, version 1, pp. 1–2](https://arxiv.org/pdf/1412.0034v1) | Known transition/output functions on a finite deterministic Mealy automaton and an unknown initial state define its preset distinguishing WORD. Here the rational carrier is infinite, reads are separate ports, and even the preset-action opponent may choose read scales and stopping from replies. Only the state-identification terminology is reused, not that whole-input preset model or its length bounds. |
| Gibbons–Lester–Bird, [*Enumerating the Rationals*, §§2 and 4](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/rationals.pdf); Han–Masuda–Singh–Thiel, [*The $(u,v)$-Calkin–Wilf Forest*, version 2, introduction and §5](https://arxiv.org/html/1411.1747v2) | Subtractive Euclid and its recorded inverse, Calkin–Wilf root/children, and path reversal are classical antecedents of the original decoder and matrix convention. At $u=v=1$ the child maps are exactly those used here. These sources supply neither the installed dyadic services nor this prior's original-acquisition action prices. |

These source correspondences are readings of the actual declarations and primary literature, not a new Lean compilation or kernel verification of §38. The theorem is conditional on the exact supplied service and all exclusions of Definition 38.1; it asserts no physical realization, noise tolerance, physical spacetime identification, full-rational finite acquisition, total-memory optimum or worldwide priority. The full-carrier and presentation obstructions already stated in §§18 and 25 remain. This bounded original-recovery consequence does not complete the continuing RRO programme.

## 追加锚（本行以下为增补区）

## 39. Acquired full future profiles and recovery after actual motion

### 39.1 All future words, all scales in the requested range

**Definition 39.1 (one source, full profile and actual evidence).** Retain the positive rational source, chronological $L/R$ actions and unclipped, nondisturbing floor services of Assumptions 11.1 and 18.2. Every requested positive integer scale must be supplied, lawful to use, and return its complete binary integer in finite time. Each finite action, local computation and response must complete. There is one source and epoch, with serialized acknowledgements; no reset, copy, source inverse, saved original source or unknown-source advice is supplied. Positivity is a source premise, not a fact bought by an extra unit read.

For $B\ge1$, define the common full future profile, its instantaneous part and its candidate cut set by

$$
\begin{aligned}
\mathsf P_B(y)&=\bigl(q_m(f_v(y))\bigr)_{1\le m\le B,\ v\in\{L,R\}^{<\omega}},\\
\mathsf F_B(y)&=(q_m(y))_{1\le m\le B},\\
\mathcal H_B&=\{p/q>0:\gcd(p,q)=1,\ 1\le q\le B\}.
\end{aligned}
\tag{39.1}
$$

The words include $\varepsilon$. There is no finite catalogue or word-length restriction in $\mathsf P_B$. It is a semantic family, represented below by a finite cell and a finite evaluation procedure, not by an infinite stored tuple. A prediction indexed by $v$ is not an observation of an executed $v$. The single-scale all-future class $\equiv_m$ remains that of (11.2); it must not be confused with their common refinement over every $m\le B$.

**Theorem 39.2 (complete full-profile cell and continued prediction).** Equality of $\mathsf P_B$, equality of $\mathsf F_B$ and the following no-cut condition are equivalent:

$$
0<x<y,\qquad \mathcal H_B\cap(x,y]=\varnothing.
\tag{39.2}
$$

The cells are $(0,1/B)\cap\mathbb Q$ and $[\ell,r)\cap\mathbb Q$ between successive positive cuts of $\mathcal H_B$. Every cell has finite rational endpoints with reduced denominators at most $B$. There are infinitely many cells on the whole carrier. One cell, together with $B$, suffices to evaluate every coordinate of $\mathsf P_B$ by finite exact arithmetic and to update this profile through any actual finite forward continuation.

Proof. The cut theorem 11.2 gives the cuts $\mathcal C_m$ of the entire single-scale future family. Every reduced denominator there is at most $m$, so $\bigcup_{m\le B}\mathcal C_m\subseteq\mathcal H_B$. Conversely a reduced $p/q$ with $q\le B$ is already a cut of the instantaneous $q_q$, hence belongs to $\mathcal C_q$. Thus this union equals $\mathcal H_B$. The instantaneous grids have the same union, proving both equivalences, with the right endpoint included exactly as in (11.4). Local finiteness follows by counting finitely many numerators at each of the finitely many denominators on a bounded interval. Integer cuts ensure finite upper endpoints. Distinct cuts $p/q,p'/q'$ differ by at least $1/(qq')\ge1/B^2$; this is supporting Farey arithmetic, not a new enumeration theorem.

For evaluation choose $y_0=\ell$ when $\ell>0$, and $y_0=r/2$ in the first cell. Evaluate $q_m(f_v(y_0))$ using the actual matrix convention of §6. The equivalence proves this equals the value for every possible source in the cell, for every finite $v$, not just for words in a stored list. For a new action $a$, equal profiles before it give equal profiles after it by replacing $v$ with the chronological concatenation $av$. Consequently the cell containing $f_a(y_0)$ is the updated full-profile cell. This proves continued use and finite evaluation, without executing a prediction or acquiring a literal original history. $\square$

### 39.2 Two genuine reads at polynomial raw scales

**Theorem 39.3 (acquired full profile at an unchanged attained cut).** For every $B\ge1$, a finite deterministic program acquires the full $\mathsf P_B(z)$ of an unrestricted positive rational current source $z$ with at most two actual replies, zero actions, first scale $D=B^2$ and, if needed, second scale at most $B$. No original-denominator bound is assumed. If existing actual evidence already determines one of these replies, the program derives it and omits that read.

Proof. Obtain the actual reply $r=q_D(z)$, or derive that same integer from retained evidence. Its exact raw cell is

$$
J_D(r)=\begin{cases}(0,1/D),&r=0,\\\left[r/D,(r+1)/D\right),&r>0.\end{cases}
\tag{39.3}
$$

There is at most one distinct $\mathcal H_B$ cut strictly inside this interval: two interior cuts would be separated by less than $1/D=1/B^2$. For each denominator $s=1,\ldots,B$, compute the least numerator $j$ with $j/s>r/D$ and test $j/s<(r+1)/D$. This is one integer division and comparison per denominator; repetitions name the same cut. A cut at the lower endpoint is already owned by the cell, and the upper endpoint is excluded.

If there is no interior cut, no further read is necessary. Otherwise write that cut as $t=p/s$ with $s\le B$ (reduction is optional), obtain the genuine reply $h=q_s(z)$ and decide $z\ge t$ by $h\ge p$. Intersect (39.3) with $[t,\infty)$ or $(0,t)$ accordingly. This is a genuine comparison at the unchanged cut, not a hypothetical continuation. If prior evidence already settles its side, omit it. Select the included positive lower endpoint of the resulting interval, or an interior rational when its lower endpoint is zero. At most one cut was crossed, so this representative has exactly the actual full profile by Theorem 39.2.

For completeness, the exact containing cell is computed with $B$ further local divisions. At representative $y_0$, put $j_s=\lfloor sy_0\rfloor$. Its lower endpoint is the maximum of $0$ and $j_s/s$ over $s\le B$, and its upper endpoint is the minimum of $(j_s+1)/s$. Reduce only these selected endpoints if desired. This produces the entire finite representation, including all future words. In particular

$$
q_1(z)=\lfloor r/D\rfloor
\tag{39.4}
$$

is derived from the first reply. For $B=1$, $D=1$, there is no interior integer cut and exactly this one read suffices unless already earned. The zero report means $(0,1)$, whose upper endpoint is finite and excluded. The construction uses only finitely many binary arithmetic operations and the supplied finite-completing services. $\square$

The two-read result does not contradict the one-read divisibility condition of Theorem 15.2. Its second scale is chosen after an actual first reply; it uses the single unresolved local cut rather than a global LCM. The numerical raw scale $B^2$, as well as its binary name, is polynomially bounded.

### 39.3 The actual original/current recovery square

**Definition 39.4 (earned unit slice and authentic prefix).** An actual original reply $q_1(x)=k$, or a derived value from an actually acquired original archive, earns

$$
I_k=\begin{cases}(0,1),&k=0,\\\left[k,k+1\right),&k\ge1.\end{cases}
\qquad k=\lfloor x\rfloor\ge0.
\tag{39.5}
$$

Let $u$ be the authentic actually executed chronological prefix, with

$$
A_u=\begin{pmatrix}a&b\\c&d\end{pmatrix},\quad
ad-bc=1,\quad a,d\ge1,\quad b,c\ge0,\qquad
z=f_u(x)=\frac{ax+b}{cx+d}.
\tag{39.6}
$$

The square compares the original full profile $\mathsf P_B(x)$ and the current full profile $\mathsf P_C(z)$ on this same slice and actual prefix. The current profile must come from actual current replies, for example Theorem 39.3, or be derived from already acquired evidence. The square's upper map is the real action $u$; mathematical inverse arithmetic below is not a source operation.

**Theorem 39.5 (both factor directions and sharp slice threshold, including zero).** For every $k\ge0$ and $B\ge2$, the current full profile at resolution $C\ge1$ determines the original full profile at resolution $B$ on $I_k$ if and only if

$$
f_u\bigl(\mathcal H_B\cap(k,k+1)\bigr)\subseteq\mathcal H_C
\quad\Longleftrightarrow\quad
C\ge C_*:=B\bigl(c(k+1)+d\bigr)-c.
\tag{39.7}
$$

The reverse factor holds if and only if

$$
f_u^{-1}\bigl(\mathcal H_C\cap f_u((k,k+1))\bigr)
 \subseteq\mathcal H_B.
\tag{39.8}
$$

Mutual recovery holds precisely when the two interior cut sets agree after transport. A current profile with extra cuts can recover the original profile without being recoverable from it. For $B=1$, the original full profile is already known from $k$, with no current read; the reverse factor still requires (39.8).

Proof. By Theorem 39.2 these are exactly the respective half-open interval partitions. A factor from current to original exists precisely when every original interior cut survives in the current partition. Necessity follows by choosing two rational points on opposite sides of a missing cut within one current cell; sufficiency follows because each current cell then lies in one original cell. The same argument with roles reversed gives (39.8). It proves both directions, with cuts at the slice's endpoints irrelevant because the domain is already restricted to that slice.

For the sharp value, any original cut can be written reduced as $j/m$ with $m\le B$ and $mk<j<m(k+1)$. Its image is

$$
f_u(j/m)=\frac{aj+bm}{cj+dm},\qquad
cj+dm\le m\bigl(c(k+1)+d\bigr)-c\le C_*.
\tag{39.9}
$$

This image is reduced: a common divisor of its two displayed entries divides $j,m$ after applying the integer inverse matrix. This is transformed-column reducedness, not merely lower-row coprimality. Thus $C\ge C_*$ suffices. The last $B$-grid cut

$$
t_*=k+1-1/B=\frac{B(k+1)-1}{B}
\tag{39.10}
$$

is positive even for $k=0$, belongs strictly to the slice, and is reduced. Its image has reduced denominator exactly $C_*$. If $C<C_*$ that image is not in $\mathcal H_C$. Local finiteness gives rationals $x^-<t_*<x^+$ in the same $I_k$ with no current cut between their images. They have identical current full profiles and different original full profiles. This is a strict-below-threshold witness on the declared slice. For $c=0$, determinant one forces $a=d=1$, so $C_*=B$ and the same witness works. For $B=1$ there are no interior integer cuts in $I_k$, proving its separate statement. $\square$

This is a sharp factor condition given only the declared slice and prefix. It is not an acquisition-cost optimum when additional old evidence is retained. The lower endpoint $0$ is always excluded; it causes no missing case in (39.7).

### 39.4 Acquired original-profile upgrades from the actual moving cut

**Definition 39.6 (earned localization and exact preimages).** A bounded original interval $I$ is earned when actual replies at authentic cuts, or an actually acquired earlier archive, imply $x\in I$. Write its finite endpoints as $0\le\alpha<\beta<\infty$, with lower endpoint included when positive and upper endpoint excluded. Put $U=\lceil\beta\rceil\ge1$. A unit slice or a previously acquired full-profile cell already supplies this localization; no new bootstrap read is charged in that case.

For clarity, solving a current threshold $f_u(t)=j/m$ gives

$$
t=\frac{dj-bm}{am-cj}
\quad\text{when this lies in }(0,\infty).
\tag{39.11}
$$

Its displayed denominator is $am-cj$, not $cj+dm$. The latter is the forward denominator in (39.9). For reduced $j/m$ and a positive preimage both entries in (39.11) are positive and coprime, by the inverse determinant-one argument. Endpoint preimages of raw cells are clipped to the actual image $f_u((0,\infty))$ before inversion; an endpoint outside that image is replaced by the corresponding original endpoint $0$ or $\infty$.

**Theorem 39.7 (two-reply upgrades, polynomial raw scale and attained linear scan).** At any authentic attained prefix $u$, from an earned bounded $I$ and requested $B\ge1$, the controller acquires the original full $\mathsf P_B(x)$ with zero additional actions and at most two genuine current replies. A sufficient explicit raw-scale budget is

$$
T=cU+d,\qquad Q=BT,\qquad D=Q^2;
\tag{39.12}
$$

the optional second scale is at most $Q$. The decoder uses $O(B)$ rational divisions/comparisons and a constant number of gcd computations, with bit costs specified in Proposition 39.10. Its loop runs over original denominators $1,\ldots,B$, not every current denominator up to $Q$. Existing earned evidence is used before either paid read.

Proof. Every original target cut $j/m$ strictly inside $I$ has $m\le B$, $0<j<mU$ and transported reduced denominator

$$
s=cj+dm\le B(cU+d)=Q.
\tag{39.13}
$$

Their distinct images are separated by at least $1/Q^2$. Obtain $r=q_D(z)$ at the actual current cut, unless retained evidence already determines that exact value. Intersect $I$ with the preimage of its actual half-open cell to obtain $J$, which contains the actual $x$. This computation uses (39.11) and image clipping. The interior of $f_u(J)$ lies in one raw interval of width $1/Q^2$, so $J$ contains at most one distinct original target cut strictly in its interior.

To find it, for each $m\le B$ compute the least integer $j$ with $j/m>\inf J$, and test $j/m<\sup J$. If it passes, it is positive and there cannot be a second numerator at that denominator: that would give two distinct target images inside the raw cell. Repeated fractions across denominators identify the same cut. If no cut is found, the first reply already decides the full target. If a cut $t=j/m$ is found, compute

$$
f_u(t)=p/s,\qquad p=aj+bm,\quad s=cj+dm\le Q.
\tag{39.14}
$$

One actual current reply $h=q_s(z)$ decides $x\ge t$ exactly by $h\ge p$. Reduction can only lower the second scale; alternatively use the displayed unreduced $s$, which also works. Restrict $J$ to that side and compute the original full-profile cell by the $B$-division procedure in Theorem 39.3. This proves the promised finite acquisition and endpoint ownership.

Before either read, intersect with all retained actual constraints. If this already makes the target constant, answer without reading. If it makes the proposed current reply constant, derive that reply; its value is not relabelled as a new observation. There is no separate $q_1(z)$ request. Previously earned original $k$ is retained or derived from the original interval; no assertion that an unperformed current unit read took place is needed. All comparisons use current $z$, while all retained constraints refer to the same original $x$ through authentic matrices. Repeated, skipped and noncoprime requested scales cause no divisibility restriction, because the target range is every $m\le B$. $\square$

**Proposition 39.8 (pointwise entrance after contraction without an old source record).** If initialization occurs after an authentic prefix $u$ with no earlier source-dependent record, it need not have a bounded original interval yet. There is nevertheless a pointwise finite zero-action entrance procedure. For $c=0$ the translation formula gives a bounded original interval from one actual $q_1(z)$. For $c>0$, request $q_{2^h}(z)$ for $h=0,1,\ldots$ until the acquired raw upper endpoint is strictly below $a/c$. Clip its lower endpoint to $b/d$, invert, and obtain a bounded earned $I$. Then Theorem 39.7 applies. With

$$
\delta=a/c-z=\frac1{c(cx+d)},\qquad
h_* =\max\bigl(0,\lceil\log_2(2/\delta)\rceil\bigr),
\tag{39.15}
$$

at most $h_*+1$ entrance replies suffice. This is analysis of the actual run, not $x$ or $\delta$ supplied to the program.

Proof. At scale $D$, the raw upper endpoint is at most $z+1/D$. When $D\ge2/\delta$, it is strictly below $a/c$, so the inverse upper endpoint is finite. The attained $z$ is strictly inside $(b/d,a/c)$ and positive; the clipped lower preimage is either $0$ or a finite nonnegative rational. This earns the interval from actual replies. The dyadic test is an exact rational comparison using known $a,c$; it does not require knowing $\delta$. Translation has no finite upper asymptote, so its inverse of a finite current raw cell is bounded after positivity clipping. If an earlier archive already supplied $I$, this entire entrance phase is omitted. No uniform entrance cap follows. $\square$

### 39.5 Sufficient retained relations and one continuing controller

**Definition 39.9 (joint evidence interval and authentic cut indices).** Retain the source/epoch binding, the serialized actual action/acknowledgement sequence and the actual read records $(t_i,D_i,r_i)$, where $t_i$ is an authentic position in that sequence and $r_i=q_{D_i}(f_{u_{t_i}}(x))$. Authenticity assumes faithful recording and exclusive serialization, not cryptographic protection against a malicious recorder. The semantic source-dependent state can be retained as just

$$
K=(0,\infty)\cap\bigcap_i f_{u_{t_i}}^{-1}(J_{D_i}(r_i)).
\tag{39.16}
$$

This is one interval with rational endpoints, possibly unbounded before entrance. A derived full-profile cell, original band and floor tuple are computed from $K$ when needed. They need not be separately retained as stage archives. A known current matrix is updated by left multiplication on each acknowledged letter; matrices at older authentic cuts can be recomputed from the recorded sequence. Source-blind requests or choices are allowed to depend on earlier exposed data; extra source-dependent request parameters would be additional evidence and must be declared as such.

**Theorem 39.10 (sufficiency, continued use and exact prediction boundary).** The state (39.16), the authentic cut indices and the installed finite arithmetic suffice for original, current and authentically recorded-cut predictions. At a cut $t$, the full resolution-$C$ profile is determined exactly when

$$
f_{u_t}^{-1}(\mathcal H_C)\cap\operatorname{int}K=\varnothing.
\tag{39.17}
$$

For a single prediction $q_m(f_v(f_{u_t}(x)))$, replace that cut set by the preimages of its instantaneous $m$-grid. If $K$ lies in an original $\mathsf P_B$ cell, every original/current/recorded-cut prediction at $m\le B$ and every finite future word is determined, and remains so through further genuine forward actions. Unknown later original resolutions can be acquired by Theorem 39.7 using this same state.

Proof. Each actual read contributes exactly its interval constraint, because every matrix map is strictly increasing. Their intersection is nonempty on the actual run, with positive lower endpoint included and finite upper endpoint excluded. The source-dependent reports, together with source-independent choices and acknowledged actions, impose precisely (39.16); replay on another $y\in K$ gives the same deterministic branch. Thus the target can be computed from these data if and only if it is constant on $K$. A target cut strictly inside $K$ gives two rational realizations with different values; absence of such cuts gives constancy with correct endpoint ownership. Theorem 39.2 proves (39.17) for all continuations simultaneously. The same threshold argument proves the single-coordinate version.

A representative in $K$ therefore computes every permitted prediction. If $K$ lies in one original $\mathsf P_B$ cell, its forward images, including those at each authentic past cut and any continuation from it, have equal $\mathsf P_B$ by forward congruence. On an actual new action update the authentic word/matrix; on an actual new reply intersect its preimage into $K$. Neither update loses a previously established prediction. At an original-precision upgrade, the new $K$ lies in a cell of the finer requested common profile; old covered ranges restrict consistently by the same actual $x$.

Keeping $K$ preserves the entire joint kernel of the numerical evidence in two endpoints. This is a sufficient semantic compression, with no claim of globally minimal binary coding. Authentic provenance still needs the actual action/read record: an interval does not say which observations occurred. Conversely that record permits recomputing $K$, so its endpoints can be a working cache rather than a second source of truth. Predicted values at authentic old cuts remain predictions attached to those cuts; they are actual past observations only where a corresponding read record exists. A fabricated continuation cannot become an authentic cut merely because its matrix can be evaluated. $\square$

**Theorem 39.11 (bounded-overshoot frontiers for unknown original requests).** There is one nonanticipating controller for successive requested original precisions $M_1,M_2,\ldots\ge1$, with arbitrary finite genuine forward continuations between completed requests. It serializes each upgrade and uses Definition 39.9's single boundary. Use the public frontiers

$$
b_0=1,\quad b_1=2,\quad b_{j+1}=b_j^2\ (j\ge1),\qquad
b_j=2^{2^{j-1}}\ (j\ge1).
\tag{39.18}
$$

On a miss choose the least frontier $b_j\ge M_i$, skip unneeded intervening frontiers, and run Theorem 39.3 at an unchanged original start or Theorem 39.7 at the attained moving cut. A hit is answered from the retained boundary with no paid read. Let $M=\max_{i\le n}M_i$, and let $J$ count frontier acquisitions through that completed finite request prefix. Including a possible acquisition at $b_0$,

$$
\begin{aligned}
J&\le 2+\left\lceil\log_2\log_2(\max(2,M))\right\rceil,\\
b_{\rm final}&\le\max(2,M^2),\\
R_{\rm paid}&\le R_{\rm start}+E+2J.
\end{aligned}
\tag{39.19}
$$

Here $E$ is the genuine entrance cost only when Proposition 39.8 is needed. The count includes all earlier frontier acquisitions by this same controller in $J$. If accounting begins with an already acquired archive, $R_{\rm start}$ charges its actual paid evidence since binding; it is zero when starting at the original cut or using the separate post-prefix entrance. This starting evidence is reused without paying to acquire it again. No intermediate frontier is paid merely to reach a later one. All upgrades use zero extra source actions. The controller additionally retains whatever genuine continuations the user actually performs.

Proof. At each miss the chosen frontier exceeds the already installed one. For $M>1$ the least covering frontier is strictly below $M^2$ unless $M$ itself is a frontier, in which case it equals $M$; $M=1$ is separate. The indices in (39.18) give the first bound. Acquisition gives the whole original common profile, so every smaller request is answered regardless of repetition, gaps or common factors, and further actions do not invalidate it by Theorem 39.10. If extra earlier evidence already determines the selected frontier, compute it without reading. This can only reduce paid replies. No later request or continuation was used to choose an earlier scale. The two acquisition theorems and the separately charged entrance prove the last inequality. The original denominator remains unrestricted. $\square$

### 39.6 Binary payload, attained work and retention

**Proposition 39.12 (finite-prefix resource vector for that same controller).** Use $\lambda(n)=1+\lceil\log_2(n+1)\rceil$ for nonnegative integer widths, fixed binary delimiters, and schoolbook exact arithmetic. After entrance choose its earned interval as a fixed enclosing $I$ with $U=\lceil\sup I\rceil$, even as the working $K$ shrinks. For a unit slice, $U=k+1$, so source magnitude is explicitly charged. At acquisition $i$ let $B_i$ be its chosen frontier, let $a_i,b_i,c_i,d_i$ be the actual attained matrix entries, and put

$$
\begin{aligned}
T_i&=c_iU+d_i,& V_i&=a_iU+b_i+1,\\
Q_i&=B_iT_i,& \mu_i&=\lambda(\max(a_i,b_i,c_i,d_i)),\\
W_i&=16\bigl(e_i+\lambda(B_i)+\lambda(U)+\mu_i+1\bigr).
\end{aligned}
\tag{39.20}
$$

Here $e_i$ bounds the binary widths of the endpoints of the working earned $K$ before that acquisition (use $1$ at a fresh unchanged original start). At that fresh start use $Q_i=B_i$, first obtain the band from its actual reply, and use $U=\lfloor x\rfloor+1$ in the ensuing analysis. The constants in $W_i$ cover the finite products, divisions, representative and endpoint computations below. In particular they are independent of the unknown reduced source denominator.

The raw scales and acquired payloads obey

$$
D_i\le Q_i^2,\quad s_i\le Q_i,\qquad
0\le r_i<D_iV_i,\quad 0\le h_i<s_iV_i.
\tag{39.21}
$$

The total binary lengths of the two scale names and two actual integer replies at this upgrade, omitting any unneeded reads, are at most

$$
12\bigl(1+\log_2(B_i+1)+\log_2(T_i+1)+\log_2(V_i+1)\bigr).
\tag{39.22}
$$

Let $\mu_{\max}$ be the maximum actual matrix width through the finite prefix. If $P_{\rm start}$ is the actual binary payload of starting evidence charged by $R_{\rm start}$ and $P_{\rm ent}$ is the actual sum of entrance scale-name and reply lengths, the cumulative paid binary payload is

$$
P_{\rm paid}=O\!\left(P_{\rm start}+P_{\rm ent}+\log(M+2)
       +J\bigl(\mu_{\max}+\log(U+1)+1\bigr)\right).
\tag{39.23}
$$

An explicit attained local bit-work bound for the acquisitions is

$$
O\!\left(\sum_{i=1}^{J}\bigl(B_iW_i^2+W_i^3\bigr)\right).
\tag{39.24}
$$

Add entrance processing, all received request-name bits, actual matrix-update work, output work and provenance handling as described in the proof. These are different coordinates from paid reply count, full-profile resolution, raw scale, source-service costs and rights/backing.

Proof. Since $0<x<U$ or $x\le U$ suffices for the bound and $cx+d\ge1$, the actual current value satisfies $0<z<V_i$. This proves (39.21) from the actual floor replies; original magnitude has not disappeared when the source moves. The two scales have logarithms at most $2\log Q_i$ and $\log Q_i$; the two replies have logarithms at most these plus $\log V_i$. The width convention then proves the conservative constant (39.22). On the sparse subsequence of acquired frontiers, the positive numbers $\log_2 B_i$ grow by at least a factor two, apart from the initial $1$ frontier. Their sum is at most $2\log_2 b_{\rm final}$. Also $T_i+1,V_i+1\le 3\cdot2^{\mu_i}(U+1)$. Combining these bounds with (39.19) proves (39.23). Entrance has its actual extra payload; at dyadic exponent $h$ it is $O(h+\lambda(a+b+c+d)+1)$ bits per reply, using $z<a/c\le a$ when $c>0$. Its local scan and arithmetic are charged through the attained final exponent, not hidden in $J$.

For (39.24), compute (39.12), the two inverse endpoints of the first raw cell, their intersection with $K$, the possible transported cut, and the final representative. Each has only a fixed number of products and rational operations on input integers of the widths included in $W_i$. For example an inverse raw endpoint is $(d_ir_i-b_iD_i)/(a_iD_i-c_ir_i)$ before clipping. This also shows why the endpoint formula (39.11) and the forward denominator (39.14) cannot be interchanged. Cross-multiplication compares endpoints without enumerating intervening numerators. The scan for the unique interior cut takes one division and a constant number of comparisons per original denominator. The containing original-cell scan takes another such pass. Arithmetic on $W_i$-bit integers costs $O(W_i^2)$ per division/product. Only a constant number of selected fractions need reduction; Euclid uses $O(W_i)$ such steps, giving the conservative $O(W_i^3)$ term. No loop over all $1,\ldots,Q_i$ or over an LCM is present. The stated $O(B_i)$ scan is therefore attained by this decoder.

Let $H$ be the number of actual post-binding action letters, $R$ the total actual reads including entrance, and $A_{\rm ack}$ the actual acknowledgement/binding encoding size. Updating the current matrix by a generator costs $O(\mu)$ bit work per letter and four integers of $O(\mu)$ space. Each entry is at most $2^H$, but using the measured actual $\mu$ avoids identifying action count with matrix width. Complete provenance can be retained in

$$
O\bigl(H+P_{\rm paid}+R\lambda(H+1)+A_{\rm ack}\bigr)
\tag{39.25}
$$

bits, plus retained request names when they have a consumer. Store the original interval endpoints and current matrix as working state with $O(e+\mu+\lambda(B)+\lambda(U))$ bits, plus arithmetic workspace $O(W)$ and counters; selected endpoints are reduced to keep these widths literal. The next acquisition's $e_i$ charges their actual size. No separate full stage archives or $B_i$-entry tuples are required. Reports kept for provenance remain actual rows; derived floor values have no second paid-evidence status. Processing/encoding these rows costs at least their lengths and is added to (39.24).

If a consumer asks for all instantaneous values through precision $m$, emit them by $m$ exact divisions at a representative, costing $O(mW^2)$ plus their output length. A word prediction at an authentic cut $t$ and continuation $v$ uses the recorded $u_t$ or its computed matrix. Replaying its $|u_t|+|v|$ letters and evaluating at a representative costs $O((|u_t|+|v|+m)\widehat W^2)$ when all $m$ coordinates are emitted, where $\widehat W$ includes that composed matrix, representative and output operand widths. Matrix entries grow by at most doubling per letter. A full-profile answer can instead emit only $B$ and the two cell endpoints; the infinitely many coordinates are available on demand, not emitted in finite time. Charge each received request's entire binary encoding, each chosen finite prediction word, all emitted bits and any replay used to reconstruct an old matrix. Even a hit has request and output work. Entrance rational inversion takes $O(W_{\rm ent}^3)$ per read as a conservative bound, and all its actual payload and acknowledgements enter (39.25).

The installed source must complete every requested service, but no law for its internal time, storage, price or physical backing has been assumed. Those resources and lawful scale access remain separate premises/costs. Equations (39.21)–(39.24) assert neither movement-independent stationary cost nor a worldwide optimum, tariff law, competitive ratio or dominance over a construction with a different resource vector. $\square$

### 39.7 Exact obstructions without earlier original information

**Proposition 39.13 (a fixed finite current profile loses unbounded original unit information).** For every authentic prefix with $c>0$ and finite $C$, the current full $\mathsf P_C(f_u(x))$ fails to recover even the original $q_1(x)$ on the unrestricted positive carrier. In particular it cannot recover the original rational or word. Pure translations have the different exact law

$$
c=0\ \Longrightarrow\ u=R^b,\ a=d=1,\qquad
q_m(f_u(x))=q_m(x)+mb,
\tag{39.26}
$$

so every original profile through $C$ is recoverable from the corresponding current one and conversely.

Proof. If $c>0$, then

$$
f_u(x)=a/c-\frac1{c(cx+d)}.
\tag{39.27}
$$

Whenever $cx+d>C$, every $m\le C$ has

$$
q_m(f_u(x))=\lceil ma/c\rceil-1.
\tag{39.28}
$$

If $ma/c$ is an integer the subtracted positive amount is less than $1$; otherwise its fractional part is at least $1/c$ while the subtracted amount is less than $1/c$. This proves (39.28) in both cases. Choose an integer $K>C+d+1$, and the two actual originals $x=K+1/3$, $y=K+4/3$. Both satisfy that tail condition, have identical instantaneous and hence full current profiles, but have original unit indices $K$ and $K+1$. This supplies the missing $q_1$ obstruction directly. For the explicit real action $u=L$, their current reports are $m-1$ for every $m\le C$. Both originals are actual reachable rational sources by Theorem 6.2. For $c=0$, the determinant forces $a=d=1$ and the source law is $x\mapsto x+b$; a word containing $L$ has positive lower-left entry, so its authentic word consists only of $R$. The integer floor identity proves both profile factors in (39.26). Earned localization or old retained information changes this global question exactly through (39.7) and (39.17). $\square$

**Theorem 39.14 (no uniform finite read cap, even with further forward actions).** Fix any authentic starting prefix $u$ with $c>0$. A deterministic controller has no source-dependent record from before that cut. Allow arbitrary finite further forward actions, adaptive current scales and local finite computation on the same source. If it terminates correctly for every positive rational original, no uniform finite bound on its number of current replies can recover unbounded original $q_1$. Pointwise finite recovery remains possible by Proposition 39.8 and Theorem 39.7 with $B=1$.

Proof. Assume a cap $N$. For every possible further finite action prefix $v$, the composite matrix $A_vA_u$ still has lower-left entry $c'>0$: its lower row is a nonnegative row with positive lower-right entry, so $c'=\gamma a+\delta c\ge c$. Its attained response approaches $a'/c'$ strictly from below as the original $x\to\infty$. At a requested scale $D$, feed the tail response

$$
\rho(D,A_vA_u)=\lceil Da'/c'\rceil-1.
\tag{39.29}
$$

Every finite sequence of these responses is realized by all sufficiently large rational originals, since the finitely many maps/scales on that deterministic branch each stabilize to this response. Source-independent action acknowledgements also agree.

Each phase between replies on this tail branch must finish its local computation and finite actions, and either stop or issue another read. If a phase instead continued forever without a new reply, the finite earlier tail prefix would be realized by every sufficiently large actual original, giving a nonterminating actual run and contradicting the pointwise completion premise. After at most $N$ replies the branch must stop: a further read would be realized by a sufficiently large actual source and violate the uniform cap. The completed tail branch is finite and therefore realized by every rational original beyond some finite $X$. Choose two such originals with different unit indices. Their entire actual transcripts, decisions, further actions and output coincide, so that output cannot recover both unit indices. This contradicts correctness. The argument covers every $c>0$ and any finite forward action scope; it does not infer $q_1$ failure merely from rational noninjectivity. Earlier source-dependent records or earned bounded localization remove the tail premise; pure translations satisfy (39.26). $\square$

### 39.8 The four expressions, suppliers and finite scope

**Proposition 39.15 (finite relational recovery of the four expressions).** Let the original unknown chronological word be $w$, with rational boundary $x=B(w)$, rooted named-incidence path $S(w)$ and indexed prefix-memory table $M(w)$ as in §§6 and 17. Quotient each of these four expressions by equality of the original $\mathsf P_B(x)$. On their actual images the four quotients recover each other, and their common finite description is the acquired $\mathcal H_B$ cell. Its boundary is the full prediction rule; chronological continuations act on its cells; authentic cut indices relate those predictions to the recorded chronology and memory.

Proof. The exact correspondences of Theorems 6.2 and 17.3 send each exact expression to the same original $x$. Pulling back equality of its cell therefore gives the same quotient on all four actual images. Each quotient label gives the cell and conversely, proving finite-resolution mutual recovery. Theorem 39.2 supplies the complete future evaluator; Theorem 39.10 supplies authentic-cut prediction and synchronized actual continuation, and Theorem 39.7 supplies later finer original cells. This connects space as the rooted named path, time as its ordered actions, boundary as the response rule, and memory as the indexed record only at this declared observational quotient. It does not recover the literal unknown path, original action count or every original prefix row. Each finite cell still contains infinitely many rationals and arbitrarily deep unknown words, by Corollary 11.3 or directly by Theorem 6.2 and finiteness of bounded-length word sets. Actual post-binding events are known because recorded, not because the finite profile reconstructs unknown earlier events. No ambient physical spacetime identification is implied. $\square$

**Definition 39.16 (source correspondence and exact limits).** The source-specific synthesis here is the acquired common all-future profile, the adaptive polynomial-raw-scale construction, its moving-cut earned-interval decoder, the sharp two-direction slice factors, the continuing sufficient boundary and the same-controller resource and obstruction statements. The cut/congruence and one-read LCM results in §§11–12 and 15 are reused, not counted as new proofs. [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean) supplies `leftStep`, `rightStep`, `wordMatrix`, `unimodular_wordMatrix` and `wordMatrix_lower_right_pos`; [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean) supplies `unimodular_iff_wordMatrix`. Chronological $u$ uses `wordMatrix(reverse u)`. The transformed-column coprimality argument is given explicitly in (39.9), without attributing it to lower-row coprimality. [RationalRouting/Acquisition](../../../D5/S3/Observer/RationalRouting/Acquisition.lean) has its distinct two-band actual-completion contract; it does not supply this unrestricted full-profile archive. The authentic original/current/past-cut architecture in [Arithmetic Acquisition Return, §§13–16](RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_ACQUISITION_RETURN.md) is an analogue; neither its gcd/CRT ports nor its payment rule is used.

The supporting Farey arithmetic corresponds to Glasby, [*Enumerating the rationals from left to right*, arXiv:1011.2823v1](https://arxiv.org/abs/1011.2823v1), introduction and Theorem 3. Actual adaptive experiment terminology corresponds to van den Bos and Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2](https://arxiv.org/abs/1907.11034v2), §4, Definitions 10–11; a semantic test family alone is not an executed adaptive experiment. Chrobak, Kenyon, Noga and Young, [*Incremental Medians via Online Bidding*, arXiv:cs/0504103v3](https://arxiv.org/abs/cs/0504103v3), Theorems 1–2, concerns bidding with sum-of-bids payment and its deterministic/randomized competitive ratios. Only the need to declare the payment coordinate is compared here; no bidding tariff, ratio or optimality conclusion transfers to (39.19)–(39.24). These are primary-source correspondences and repository-derived prose proofs, with no claim of worldwide priority or new Lean verification.

All results retain one actual source/epoch, authentic serialized acknowledgements, exact positive source laws, finite local programs and the declared unclipped finite-completing floor services at every scale actually requested. Finite profile, raw scale, binary payload, local work, actual source service, action rights and physical backing remain distinct. The finite-information and literal-history boundaries of §§5, 16–18 remain in force. This local increment supplies a finite-resolution relation boundary and its recovery conditions; it does not complete the long-horizon RRO objective.

## 追加锚（本行以下为增补区）

## 40. Native pair actions cannot compile into fixed rooted rational words

### 40.1 Two action systems and one actual source

**Definition 40.1 (composition interface and fixed-word compatibility).**
Let $V=\mathbb N\times\mathbb N_{>0}$ and distinguish the pair actions
from the rooted actions by their typefaces:

$$
\mathsf R(a,b)=(b,a+b),\qquad \mathsf G(a,b)=(a+1,b),
\qquad L(x)=\frac{x}{1+x},\quad R(x)=x+1.
\tag{40.1}
$$

All words are finite and chronological. Write $\operatorname{Run}(W,v)$
for the pair action and $E(w,x)$ for the rooted action, so
$E(uv,x)=E(v,E(u,x))$ and the empty word acts identically. For a fixed
$v_0\in V$, put

$$
O(v_0)=\{\operatorname{Run}(W,v_0):W\in\{\mathsf R,\mathsf G\}^*\}.
\tag{40.2}
$$

A fixed-word compatible representation on this orbit consists of a map
$\iota:O(v_0)\to\mathbb Q_{>0}$ and two words
$u,w\in\{L,R\}^*$ satisfying, for every $v\in O(v_0)$,

$$
\iota(\mathsf Gv)=E(u,\iota(v)),\qquad
\iota(\mathsf Rv)=E(w,\iota(v)).
\tag{40.3}
$$

The words are fixed independently of the running composition, native
tree, history, occurrence and response. They may even be selected
separately for each fixed $v_0$; the obstruction below still applies.
No injectivity, computability or acquisition premise is imposed on
$\iota$. Empty compiled words are allowed.

The native interpretation is [LAB Arithmetic Growth, Definitions 9.1,
9.3 and Theorems 9.4, 12.2](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md):
fix one actual attained source $t_0\in\mathcal D_+$, with composition
$v_0=v(t_0)$, its authentic root binding, current exclusive rights,
ancestral tapes and sufficient finite material. A logical promotion
$P_p$ changes an alpha leaf to beta; a split $S_p$ changes beta to
$\langle\beta,\alpha\rangle$. Whole-frontier $\mathsf R$ acquires the
entry leaf list and promotes its alpha leaves and splits its beta
leaves, without editing newly born leaves again. The macro $\mathsf G$
splits the acquired current leftmost beta. It realizes the composition
effect of alpha graft, without being a literal root graft. Both macros
consume their actual replies and return before the next macro.

For every chronological $W$, these same-source procedures give

$$
v(F_W(t_0))=\operatorname{Run}(W,v_0).
\tag{40.4}
$$

Every prefix stays beta-positive. Thus the orbit in (40.2) is realized
on this one source, without importing another initialization or granting
an inverse, reset or new primitive. In particular $\mathsf R$ is neither
a single-leaf promotion nor the rooted translation $R$. A representation
in (40.3) depends only on composition; a representation of full native
trees or histories is a different domain.

### 40.2 The action obstruction on every attained orbit

**Theorem 40.2 (only the constant rational representation is compatible).**
For every $v_0\in V$, every representation (40.3) has
$u=w=\varepsilon$ and $\iota$ constant on $O(v_0)$. Conversely every
positive rational constant and these empty words satisfy (40.3).
On the whole domain $V$, the maps intertwining both actions with fixed
rooted words are exactly the constant maps with both words empty.

Proof. First use the evaluation freeness actually needed here. For any
$x\in\mathbb Q_{>0}$, Theorem 6.2 gives a unique word $d_x$ from root
$1$ to $x$. If $E(s,x)=E(t,x)$, then
$E(d_xs,1)=E(d_xt,1)$, whence $d_xs=d_xt$ by that theorem, and $s=t$
by cancellation of the identical prefix. This is freeness of evaluation
at each rational anchor, not an inference from matrix generation.

Let $\Phi$ replace every $\mathsf G$ by $u$ and every $\mathsf R$ by
$w$, preserving concatenation. Induction on word length using (40.3)
gives

$$
\iota(\operatorname{Run}(W,v))=E(\Phi(W),\iota(v))
\quad(v\in O(v_0)).
\tag{40.5}
$$

The pair actions have the following equality at every $(a,b)\in V$:

$$
\begin{aligned}
\operatorname{Run}(\mathsf G\mathsf R\mathsf R,(a,b))
 &= (a+b+1,a+2b+1)\\
 &=\operatorname{Run}(\mathsf R\mathsf G\mathsf R\mathsf G,(a,b)).
\end{aligned}
\tag{40.6}
$$

Apply (40.5) at $v_0$. Rational-anchor freeness gives the literal word
identity $uww=wuwu$. Taking lengths gives
$|u|+2|w|=2|u|+2|w|$, so $u=\varepsilon$.
For this same $v_0=(a,b)$ there is a second legal pair equality:

$$
\begin{aligned}
\operatorname{Run}(\mathsf R^3,(a,b))
 &=(a+2b,2a+3b)\\
 &=\operatorname{Run}
   (\mathsf R\mathsf G^{a+b}\mathsf R\mathsf G^b,(a,b)).
\end{aligned}
\tag{40.7}
$$

Indeed after the first replacement and $a+b$ graft-effects the pair is
$(a+2b,a+b)$; replacement followed by $b$ graft-effects gives the
displayed result. Every prefix is in $V$. With $u$ empty, (40.5) and
freeness now give $www=ww$, so $3|w|=2|w|$ and $w=\varepsilon$.
The state-dependent exponents in this equality are witnesses in the
native process, not a state-dependent choice of compiled word.
Equation (40.5) then makes $\iota$ constant on its entire orbit. The
converse follows from the empty-word law.

For a representation on all of $V$, restricting to any orbit first
forces the two words empty. Graft invariance gives
$\iota(a,b)=f(b)$ with $f(b)=\iota(0,b)$. Replacement invariance gives
$f(a+b)=f(b)$ for all $a\ge0,b\ge1$. Taking $b=1$ proves that $f$,
and hence $\iota$, is constant on $V$. $\square$

**Proposition 40.3 (exact-rational and static-coding boundaries).**
The empty-word conclusion fails for a positive-real codomain. Also an
injective coding of pair states into positive rationals need not satisfy
(40.3), even when all codes are positive integers.

Proof. Put $\varphi=(1+\sqrt5)/2$ and let $\iota$ be the constant
$\varphi$. The nonempty chronological word $LR$ acts by
$x\mapsto(1+2x)/(1+x)$ and fixes $\varphi$, since
$\varphi^2=\varphi+1$. Thus $u=w=LR$ satisfies the real version of
(40.3). This example refutes the claim that both words must be empty
over all positive reals; it asserts no nonconstant real representation.
For every real anchor whose evaluation map is free, the proof of
Theorem 40.2 still works. Section 20 distinguishes such anchors from
cyclic quadratic anchors.

For a static injective code take $j(a,b)=2^a(2b-1)$. The power of two
and odd factor uniquely recover $a,b$. If this code admitted fixed
compiled words on $V$, the two successors of $(0,1)$ both have code
$2$, while its code is $1$. The unique rooted word taking $1$ to $2$
is $R$, forcing $u=w=R$. But $j(0,2)=3$ and
$j(\mathsf R(0,2))=j(2,2)=12$, whereas $R(3)=4$.
The code is injective and fails the action condition. The same logical
distinction applies to the injective syntax code of
[FARG §9](FIBONACCI_ATOMIC_RELATION_GENERATION.md): unique parsing
does not establish (40.3). Neither construction acquires a code from an
opaque source or supplies a right to act on it. $\square$

### 40.3 A native family with an exact retention requirement

**Definition 40.4 (literal block target and retained interface).** Fix
the same actual $t_0$, a public integer $n\ge0$, and the two blocks

$$
A=\mathsf G\mathsf R\mathsf R,\qquad
B=\mathsf R\mathsf G\mathsf R\mathsf G,\qquad
F(a,b)=(a+b+1,a+2b+1).
\tag{40.8}
$$

For $\sigma\in\{0,1\}^n$, let $W_\sigma$ concatenate $A$ for a zero
and $B$ for a one. Execute each macro by Definition 40.1 on that very
source. The recovery target is the literal ordered macro-name word
$W_\sigma$, equivalently $\sigma$. It is not the full addressed
primitive trace, tree, tape, allocation history or physical duration.

At the completed block cuts expose only the exact composition archive
$Q_n=(v_0,v_1,\ldots,v_n)$. A retained record $Z(\sigma)$ is allowed in
addition. A decoder receives $n$, the fixed source contract, $Q_n$ and
$Z$, and must recover the target for every $\sigma$. Every further
history-dependent discriminator available to it belongs to $Z$:
retained requests, within-block readings, tree/tape access, lengths,
timers, reference identities, dictionaries and external records are not
unaccounted side information. The actual source and its tapes still
exist; this restriction specifies the recovery interface, without
asserting that those objects have equal values or have been erased.
The archive is a mathematical view, not a new LAB reading primitive.
If $v_0$ is actually acquired by a lawful paid frontier traversal, its
rows follow by $F^j$; acquisition, maintenance and materialization of
these values are separately charged.

**Theorem 40.5 (sharp retention on the equal-composition block family).**
All $2^n$ histories of Definition 40.4 are legal on the fixed source,
have pair $F^j(v_0)$ after block $j$, and give the same $Q_n$. Their
literal macro words are pairwise distinct. Exact recovery through the
declared interface holds precisely when $Z$ is injective on this family.
Consequently at least $2^n$ record values are necessary, and an
$n$-bit fixed-width payload is both necessary and sufficient, with
$n$ public. This bound remains valid after adding the complete pair
continuation profile, or a deterministic pair-only future experiment
whose initial state and choices use only the declared retained inputs.

Proof. Beta positivity and (40.4) make every finite choice legal. Equation
(40.6) gives the same map $F$ for either block. Induction on $j$ proves
the asserted archive equality. The block words are a prefix code:
their first letters differ, and neither is empty. Reading that first
letter determines the next block and its length; removing it and
inducting recovers $\sigma$ uniquely. Thus the target has exactly
$2^n$ values on a single common archive fiber.

If two distinct choices have the same $Z$, the decoder has identical
inputs and cannot return both targets. Conversely an injective $Z$
has an inverse on its finite actual image and determines the target.
A fixed-width $b$-bit payload has at most $2^b$ values, forcing $b\ge n$.
Retaining the actual block-choice bit at each block supplies $n$ bits
and decodes by the fixed two-block rule. This is an online record of
known issued choices, not acquisition of an unknown earlier word.
For $n=0$ the family is a singleton and the required payload is zero.

At the last block every run has the same exact pair. Any common
continuation therefore has the same subsequent pairs by induction on
its letters. A deterministic adaptive pair experiment makes the same
choices after the same replies, so it also cannot separate this fiber.
This includes every pair residue, quantity and terminal gcd derived
from those pairs. Native non-pair observations are outside this claim.

For entry $v_0=(a_0,b_0)$ and final $(a_n,b_n)=F^n(v_0)$, LAB's exact
count law further gives the same successful promotion and split totals
on all these histories:

$$
p=b_n-b_0,\qquad s=a_n+b_n-a_0-b_0.
\tag{40.9}
$$

Revealing just these two totals adds no distinction. The records may
instead be carried by native source features, when accessible and
counted in $Z$; the information bound does not demand a separately
allocated auxiliary $n$-bit device. Code, framing when $n$ is not public,
actual records, workspace and source backing remain additional costs.
$\square$

**Proposition 40.6 (sharp change when macro length is exposed).** If,
in addition to public $n$ and $Q_n$, the decoder receives the actual
number $\ell$ of macro calls, then $\ell=3n+r$, where $r$ is the number
of $B$ blocks. For each fixed $0\le r\le n$, exact recovery requires
and permits $\binom nr$ record values, equivalently a fixed-width
payload of $\lceil\log_2\binom nr\rceil$ bits. A common width for all
$r$ is sharply
$\lceil\log_2\binom n{\lfloor n/2\rfloor}\rceil$.

Proof. The two block lengths are three and four, so $\ell$ determines
$r$. There are exactly $\binom nr$ binary choices of that weight, all
with the same exposed archive and length, and their targets are
distinct. The preceding injectivity argument gives the lower bound.
For the upper bound index the weight-$r$ words in lexicographic order
and retain the index. Fixed public $n,r$ supply a finite decoder. The
ratio of consecutive binomial coefficients is $(n-r)/(r+1)$, placing
the maximum at the central coefficient. This is an information
capacity statement; it grants neither free ranking work nor free
storage or acquisition of the exposed length. $\square$

### 40.4 Separating the actual trees and the supplier scopes

**Proposition 40.7 (a concrete native separation inside the common fiber).**
Take the attained beta source $t_0=\beta$, obtained from the installed
alpha root by its legal root promotion. The blocks $A,B$ give
composition $(2,3)$ but different actual logical trees, primitive
traces and addressed work:

$$
\begin{aligned}
F_A(\beta)
 &=\langle\langle\langle\beta,\alpha\rangle,\beta\rangle,
                  \langle\beta,\alpha\rangle\rangle,\\
F_B(\beta)
 &=\langle\langle\langle\langle\beta,\alpha\rangle,\alpha\rangle,
                  \beta\rangle,\beta\rangle.
\end{aligned}
\tag{40.10}
$$

Proof. Apply whole-frontier replacement and the leftmost-beta split
literally at each step. In the left-first entry order of LAB Definition
9.3, their successful primitive words, with $\varepsilon$ the root
address, are respectively

$$
\begin{aligned}
A:&\quad S_\varepsilon\ S_L\ P_R\ S_{LL}\ P_{LR}\ S_R,\\
B:&\quad S_\varepsilon\ S_L\ S_{LL}\ P_{LR}\ P_R\ S_{LLL}.
\end{aligned}
\tag{40.11}
$$

Each listed address is a leaf of the required type when edited, and
the resulting trees are (40.10). Both have two alpha and three beta
leaves, two promotions and four splits. The original legal read
Tag at address $R$ returns branch in the first and beta in the second.
The sums of successful-event address depths are respectively seven
and nine, so even their addressed-work coordinate is different. The
authentic root binding and current rights are retained through both
runs; their replies and source records are not identified by pair
equality. These are two alternative legal continuations of one fixed
source, without a reset or a simultaneously available duplicate.
$\square$

**Definition 40.8 (mathematical suppliers and limits of the bridge).**
The cross-interface obstruction of Theorem 40.2 and its same-source
block-retention consequence are `repo-derived` deductions. The pair
laws, the identity $M^2=M+I$, pair residue recovery and finite-profile
sufficiency are reused suppliers, not new results of this section.
[GraftAffineClosure](../../../D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean)
supplies `step`, `run`, the alpha composition $(1,0)$ and the affine
laws within `result`. Its false/true convention is replacement/graft;
the named words here require no Boolean conversion. Its arithmetic
graft is identified only with the composition effect of the LAB split,
not with a native root-graft permission.

[WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean)
supplies `leftStep`, `rightStep`, `wordMatrix` and
`unimodular_wordMatrix`. For chronological $w$ the column matrix is
`wordMatrix(reverse w)`, as in §6.
[UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean)
supplies matrix generation; it supplies no substitute for rational
evaluation freeness. That freeness is the explicitly applied rooted
uniqueness of §6, also consistent with the free-anchor result of §20.

The supporting rational enumeration is `literature-attested` in Calkin
and Wilf, [*Recounting the Rationals*, pp. 360–363,
DOI:10.1080/00029890.2000.12005205](https://doi.org/10.1080/00029890.2000.12005205):
the root is $1/1$, and the children of $p/q$ are $p/(p+q)$ and
$(p+q)/q$. These rules and unique enumeration are also stated in Glasby,
[*Enumerating the rationals from left to right*, introduction, pp. 1–2,
arXiv:1011.2823v1](https://arxiv.org/abs/1011.2823v1). They supply the
positive-rational tree, not a LAB compiler. The retention proof uses
elementary finite counting; its equiprobable interpretation is the
classical logarithmic measure for $N$ equally likely messages in
Shannon, [*A Mathematical Theory of Communication*, introduction,
DOI:10.1002/j.1538-7305.1948.tb01338.x](https://doi.org/10.1002/j.1538-7305.1948.tb01338.x).
No channel-coding, error, thermodynamic or worldwide originality claim
follows from these deductions.

Section 39's interval $K$ and full profiles refer to the declared
rooted source and its authentic action/read sequence. They do not
turn a composition code into (40.3), or recover the missing block
choices in Definition 40.4. State-dependent words, signed or inverse
actions, history-aware representations, other source domains and
other codomains are outside Theorem 40.2. The retention bounds concern
only the stated finite family and exposed channels, not all native
history fibers or minimum whole-installation memory. Finite mathematical
existence, actual paid acquisition, lawful references, completion,
resource costs and physical realization remain separate obligations.

## 追加锚（本行以下为增补区）

## 41. Complete fixed-source macro-history fibres and causal recovery

### 41.1 Any attained beta-positive native source

**Definition 41.1 (source, chronological words and exact fibres).** Retain
§40's one actual source/epoch, authentic root binding, current exclusive
rights, ancestral tapes and sufficient finite material for each stated
finite run. Fix any attained $t_0\in\mathcal D_+$ of LAB §§9.1–9.4, with
composition $v=v(t_0)=(a,b)$, where $a\ge0$ and $b>0$. Here
$\mathcal D_+=\mathcal D\setminus\{\alpha\}$ is the native **tree** domain,
not a set of pairs. Use the distinct pair domain

$$
\mathcal Q_+=\mathbb N_0\times\mathbb N_{>0},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad e=\binom10,
\qquad F(u)=Mu,\quad G(u)=u+e.
\tag{41.1}
$$

Pairs and their column vectors are identified only for this arithmetic.
The actual macros realizing $F$ and $G$ are respectively LAB Definition
9.3's whole-frontier $\mathsf R$ and current leftmost-beta $\mathsf G$.
At an $F$ call, acquire the finite current logical frontier in left-first
order, seal that entry list, promote each entry-alpha and split each
entry-beta exactly once. At a $G$ call, acquire the current leftmost beta
path/reference and split that leaf. Each inner call consumes its complete
reply, acknowledgement and real return. New leaves do not reenter an
old frontier list. These procedures supply actual operands and guards;
pair notation supplies neither a source reference nor permission.

All words are chronological from left to right:

$$
\operatorname{Run}(\varepsilon,u)=u,\qquad
\operatorname{Run}(hF,u)=F(\operatorname{Run}(h,u)),\qquad
\operatorname{Run}(hG,u)=G(\operatorname{Run}(h,u)).
\tag{41.2}
$$

LAB Theorems 9.4 and 12.2 give $t_h\in\mathcal D_+$ and
$v(t_h)=\operatorname{Run}(h,v)$ at every completed prefix, for every
finite word admitted with the stated sufficient resources. All
continuations refer to this same bound source; alternatives do not
supply simultaneous copies, a reset, an inverse edit or another
initialization. Resource sufficiency is quantified per finite run,
not by one fixed finite arena that holds every unbounded history.

For an integer pair $q=(A,B)$ and $k\in\mathbb Z$, put

$$
\begin{aligned}
\mathcal W_v^{(k)}(q)
 &=\{h\in\{F,G\}^*:|h|_F=k,\ \operatorname{Run}(h,v)=q\},\\
\mathcal W_v(q)&=\mathop{\dot\bigcup}_{k\ge0}\mathcal W_v^{(k)}(q),
&N_v^{(k)}(q)&=|\mathcal W_v^{(k)}(q)|,\quad
N_v(q)=|\mathcal W_v(q)|.
\end{aligned}
\tag{41.3}
$$

For $q\notin\mathcal Q_+$ or $k<0$ the corresponding set is empty and
its count is zero. Histories consist of successfully completed macros;
the empty word is included. The source parameter is always $v$, never
an unannounced eventual endpoint. Different native trees of composition
$v$ have the same macro-word dictionaries under this legality contract;
their actual trees, bindings and tapes are not thereby identified.

### 41.2 Complete affine-action and run-multiplicity classification

**Theorem 41.2 (all chronological runs at every fixed replacement count).**
Let $f_0=0,f_1=1,f_{j+2}=f_{j+1}+f_j$, and write

$$
u_0=e=(1,0),\qquad
u_j=M^je=(f_{j-1},f_j)\quad(j\ge1).
\tag{41.4}
$$

For each $k\ge0$, every finite chronological word with exactly $k$
letters $F$ has a unique form

$$
h=G^{n_k}F G^{n_{k-1}}F\cdots F G^{n_0},\qquad
(n_0,\ldots,n_k)\in\mathbb N_0^{k+1}.
\tag{41.5}
$$

Thus $n_j$ is the number of $G$ letters in the unique run with exactly
$j$ later $F$ letters; zero runs are retained. For $k=0$, (41.5) means
just $G^{n_0}$. This is a bijection of literal words with the displayed
nonnegative vectors, and its affine action is

$$
\operatorname{Run}(h,u)=M^ku+\tau(h),\qquad
\tau(h)=\sum_{j=0}^k n_j u_j
\quad(u\in\mathcal Q_+).
\tag{41.6}
$$

Two words induce the same affine map on the **whole pair domain**
$\mathcal Q_+$ if and only if their $k$ and $\tau$ agree. The complete
number of literal words in the affine-action class $(k,(x,y))$, for
integer $x,y$, is

$$
P_k(x,y)=
\#\left\{(n_0,\ldots,n_k)\in\mathbb N_0^{k+1}:
                  \sum_{j=0}^k n_j u_j=(x,y)\right\}.
\tag{41.7}
$$

Define $P_k(x,y)=0$ if $k<0$, $x<0$ or $y<0$. On $x,y\ge0$ its complete
boundary cases are

$$
P_0(x,y)=\mathbf1_{\{y=0\}},\qquad
P_1(x,y)=1,\qquad P_2(x,y)=1+\min(x,y).
\tag{41.8}
$$

For every $k\ge2$ an explicit finite count, with no unspecified normal
form choices, is

$$
P_k(x,y)=
\sum_{n_2=0}^{x+y}\cdots\sum_{n_k=0}^{x+y}
\mathbf1_{\{\sum_{j=2}^k f_{j-1}n_j\le x\}}
\mathbf1_{\{\sum_{j=2}^k f_jn_j\le y\}}
\quad(x,y\ge0).
\tag{41.9}
$$

Equivalently, for $k\ge1$ and $x,y\ge0$,

$$
\begin{aligned}
P_k(x,y)&=\sum_{m=0}^{x+y}
 P_{k-1}(x-mu_{k,1},y-mu_{k,2}),\\
\sum_{x,y\ge0}P_k(x,y)X^xY^y
 &=\prod_{j=0}^k(1-X^{u_{j,1}}Y^{u_{j,2}})^{-1}.
\end{aligned}
\tag{41.10}
$$

These are counts of all run multiplicities, not only binary digits or
one chosen family of words.

Proof. Cut a word at each occurrence of $F$. This gives precisely the
$k+1$ runs of $G$ in (41.5), including empty runs, and reassembly is the
inverse. Each $G$ adds $e$; each later $F$ multiplies that contribution
by $M$. There are exactly $j$ such later multiplications for the run
$n_j$, proving (41.6). This specializes the existing chronological
affine-word supplier of `GraftAffineClosure`; induction using $M$ gives
(41.4). No new native graft operation is inferred from that supplier.

For completeness of the action classification, suppose
$M^ku+\tau=M^\ell u+\sigma$ for every $u\in\mathcal Q_+$. Compare its
values at $(0,1),(1,1),(0,2)$. Subtraction gives equality of both matrix
columns, hence $M^k=M^\ell$, and then $\tau=\sigma$. These powers are
distinct: $M^j(1,1)$ stays beta-positive and its coordinate sum strictly
increases at every step. Thus $M^k=M^\ell$ forces $k=\ell$. The converse
is immediate from (41.6). This is equality of maps, not conjugacy under
a change of coordinates.

Every $u_j$ has nonnegative integer coordinates with positive sum. For
fixed $(x,y)\ge0$, each admissible $n_j$ is at most $x+y$, so (41.7) is
finite. Since $u_0=(1,0)$ and $u_1=(0,1)$, any chosen $n_2,\ldots,n_k$
forces

$$
n_0=x-\sum_{j=2}^k f_{j-1}n_j,\qquad
n_1=y-\sum_{j=2}^k f_jn_j.
$$

These two residuals are nonnegative exactly under (41.9)'s inequalities.
This proves that count, including all tuples and excluding all invalid
ones. At $k=0$ only $n_0=x,y=0$ is possible; at $k=1$ the tuple is
$(x,y)$. At $k=2$, $n_2$ ranges from zero through $\min(x,y)$, giving
(41.8). In particular this last action class consists exactly of
$G^j F G^{y-j} F G^{x-j}$ for those $j$. Grouping (41.7) by $n_k=m$
proves the finite sum in (41.10); expanding each geometric series
proves its coefficient identity. Nonzero generator sums make every
coefficient finite. Negative residuals and out-of-domain indices give
zero throughout. $\square$

**Theorem 41.3 (complete fixed-source endpoint fibres).** For every fixed
attained source $t_0$ of Definition 41.1, every $q\in\mathcal Q_+$ and
every $k\ge0$,

$$
\begin{aligned}
\mathcal W_v^{(k)}(q)&\ \longleftrightarrow\
 \left\{n\in\mathbb N_0^{k+1}:
          \sum_{j=0}^k n_j u_j=q-M^kv\right\}\quad(k\ge0),\\
N_v^{(k)}(q)&=P_k\bigl((q-M^kv)_1,(q-M^kv)_2\bigr).
\end{aligned}
\tag{41.11}
$$

Subtraction here is in $\mathbb Z^2$, so negative residuals invoke the
zero convention. Put $s_0=a+b$ and $\Delta=A+B-s_0$. If $\Delta<0$ then
$N_v(q)=0$; otherwise the **full** endpoint count is

$$
N_v(A,B)=\sum_{k=0}^{\Delta}
 P_k\bigl(A-(M^kv)_1,B-(M^kv)_2\bigr).
\tag{41.12}
$$

In particular $\mathcal W_v(v)=\{\varepsilon\}$, while every other
endpoint of potential at most $s_0$ has empty fibre. At higher potential
and for $k\ge0$, the exact last-letter recurrence is

$$
\begin{aligned}
\mathcal W_v^{(k)}(A,B)
 &=\{hF:h\in\mathcal W_v^{(k-1)}(B-A,A)\}
       \ \dot\cup\
   \{hG:h\in\mathcal W_v^{(k)}(A-1,B)\},\\
N_v^{(k)}(A,B)
 &=\mathbf1_{\{1\le A\le B\}}N_v^{(k-1)}(B-A,A)
   +\mathbf1_{\{A\ge1\}}N_v^{(k)}(A-1,B).
\end{aligned}
\tag{41.13}
$$

The first set in (41.13) is omitted unless $1\le A\le B$, and the
second unless $A\ge1$. Its bases, also for total counts, are

$$
N_v^{(k)}(v)=\mathbf1_{\{k=0\}},\qquad
N_v^{(k)}(A,B)=0\quad(A+B\le s_0,\ (A,B)\ne v).
\tag{41.14}
$$

The invalid-endpoint and negative-$k$ conventions of Definition 41.1
apply before these formulas. Summing (41.13) over $k$ gives the same
recurrence for $N_v$, with source base one. Higher-potential unreachable
endpoints receive zero; no additional base history is inserted there.

Proof. The bijection (41.5) and exact action (41.6) give (41.11) in both
directions. Every resulting finite word has its legal same-source
native realization under Definition 41.1's resource premises. There is
no restriction to selected blocks, and no shape assumption on $t_0$
beyond membership in $\mathcal D_+$.

For $s(A,B)=A+B$, a forward $F$ increases $s$ by the current beta count,
which is at least one; a $G$ increases it by one. Every history ending
at $q$ therefore has length at most $\Delta$, and in particular
$k\le\Delta$. The empty word alone has potential $s_0$ and ends at $v$.
This proves finiteness, (41.12) and (41.14), including $\Delta=0$.

Any nonempty word has one last letter. Solving $F(x,y)=(A,B)$ gives
$(x,y)=(B-A,A)$, which belongs to $\mathcal Q_+$ exactly when
$1\le A\le B$. Solving $G(x,y)=(A,B)$ gives $(A-1,B)$, valid exactly
when $A\ge1$ for a valid target. Each last-letter class is in bijection
with its predecessor fibre. The classes are disjoint as literal words,
even when their native edits or endpoints coincide. Their predecessor
potentials are respectively $B$ and $A+B-1$, both strictly below
$A+B$ on the permitted branches. Induction from (41.14), with zeros
below the source and outside the pair domain, proves (41.13) and shows
that it counts exactly the same complete fibres as (41.12). $\square$

At one fixed source, equality of endpoints means only
$M^kv+\tau=M^\ell v+\sigma$. It need not force $k=\ell$. If $k=\ell$,
it does force $\tau=\sigma$ and hence equality of the whole affine pair
actions; neither conclusion identifies the corresponding native tree
actions. These distinctions are witnessed next.

### 41.3 Beta examples, native trees and primitive traces

**Proposition 41.4 (complete small fibres and their distinct meanings).**
Take the concrete attained source $t_0=\beta$, obtained by the legal root
promotion from the installed alpha, so $v=(0,1)$. Its complete fibres are

$$
\begin{array}{c|c|c|c|c|c|c}
q&k=0&k=1&k=2&k=3&k\ge4&N_{(0,1)}(q)\\ \hline
(0,1)&\{\varepsilon\}&\varnothing&\varnothing&\varnothing&\varnothing&1\\
(1,1)&\{G\}&\{F\}&\varnothing&\varnothing&\varnothing&2\\
(2,3)&\varnothing&\{GGFG\}&\{GFF,FGFG\}&\{FFF\}&\varnothing&4
\end{array}
\tag{41.15}
$$

In particular $\mathcal W_{(0,1)}(2,3)=\{GGFG,FGFG,GFF,FFF\}$.
For the two words at $(1,1)$ the actual tree is

$$
t_F=t_G=\langle\beta,\alpha\rangle,
\qquad\text{successful primitive trace } S_\varepsilon.
\tag{41.16}
$$

For the four words at $(2,3)$, with $\varepsilon$ the root address, the
actual results and successful primitive edits are

$$
\begin{array}{c|c|l}
\text{macro word}&\text{logical tree}&\text{chronological primitive edits}\\ \hline
GGFG,\ FGFG
 &\langle\langle\langle\langle\beta,\alpha\rangle,\alpha\rangle,
       \beta\rangle,\beta\rangle
 &S_\varepsilon\ S_L\ S_{LL}\ P_{LR}\ P_R\ S_{LLL}\\
GFF,\ FFF
 &\langle\langle\langle\beta,\alpha\rangle,\beta\rangle,
       \langle\beta,\alpha\rangle\rangle
 &S_\varepsilon\ S_L\ P_R\ S_{LL}\ P_{LR}\ S_R
\end{array}
\tag{41.17}
$$

The first tree is the four-branch left comb. Both trees have two alpha
and three beta leaves. The words $GFF$ and $FGFG$ have the same affine
pair action on every $u\in\mathcal Q_+$, namely $M^2u+(1,1)$, yet give
the two different trees in (41.17). Thus affine-action equality does
not imply equality of native tree actions. Conversely (41.16) equates
native results and primitive traces on beta for $F$ and $G$, whose
whole-domain affine actions are different.

Proof. In (41.11), $M^0v=(0,1)$, $Mv=(1,1)$,
$M^2v=(1,2)$ and $M^3v=(2,3)$. At $(2,3)$, $k=0$ has residual
$(2,2)$ and $P_0=0$; $k=1$ has residual $(1,2)$ and unique word
$G^2FG$; $k=2$ has residual $(1,1)$ and the two words $FGFG,GFF$;
$k=3$ has zero residual and word $FFF$. At $k=4$ the unshifted endpoint
is $(3,5)$, with sum eight exceeding five; subsequent sums increase.
All their residuals therefore give zero. The other two rows follow
from the source base and the $k=0,1$ cases of the same formulas.

For the native calculations, a beta split replaces its leaf by
$\langle\beta,\alpha\rangle$ and a promotion replaces alpha by beta.
At each $F$, list the old leaves left first and edit exactly that list;
at each $G$, edit the leftmost beta. From beta, the first $F$ or $G$
is the single split at $\varepsilon$. Successively applying these
rules gives exactly the enabled addresses, types and trees in
(41.16)–(41.17). For example $GGF$ gives
$\langle\langle\langle\beta,\alpha\rangle,\beta\rangle,\beta\rangle$;
its final $G$ splits the leaf at $LLL$, producing the four-branch comb.
In (41.6), $GFF$ has translation $u_2$ and $FGFG$ has translation
$u_1+u_0=u_2$, with two $F$ letters in both. The two displayed trees
are different ordered terms, so the stated native-action distinction
follows. $\square$

The selected §40 block family uses only $GFF$ and $FGFG$; it is a proper
subset of (41.15)'s complete fibre. The initial composition $(0,1)$
itself forces the singleton beta **logical** tree in nonempty ordered
binary syntax: the total leaf count is one, so a branch is impossible.
That fact does not acquire its authentic binding, rights or earlier
records. For general count pairs, even attained native trees need not
have unique shape, as (41.17) shows for $(2,3)$.

Literal macro words, successful primitive edit traces, actual logical
trees, affine pair actions, count endpoints and full native tapes are
separate objects and equality relations. A primitive trace includes
addresses and $P/S$ names; it does not include the macro grouping.
The complete frontier acquisition in $F$ and the leftmost-path
acquisition in $G$ have their own references, traversal lists, read
traffic, acknowledgement frames and work storage. Neither a shared
endpoint nor a shared successful primitive trace proves equality of
those full records, physical runtime bytes, elapsed time or completion
schedule. Primitive-event counts are work coordinates, not a clock.
Recovering macro grouping from primitive expansion alone is a different
parsing problem, not a premise of the following decoder.

### 41.4 Causal current-endpoint ranks and exact two-sided recovery

**Definition 41.5 (source-relative order, retained information and costs).**
Fix the supplied source parameter $v$ throughout. At $v$ the sole word
$\varepsilon$ has rank zero. At every other reachable endpoint $q$,
order all words ending in $F$ first, by predecessor order, then all
words ending in $G$, by predecessor order. Empty blocks are skipped.
Write

$$
C_F^v(A,B)=
\begin{cases}N_v(B-A,A),&1\le A\le B,\\0,&\text{otherwise},\end{cases}
\qquad(q=(A,B)\in\mathcal Q_+).
\tag{41.18}
$$

For invalid endpoints take $C_F^v=0$. With zero-based fibre rank
$\operatorname{rk}^v_q$, retain at every completed prefix

$$
Z_v(h)=\bigl(q,r(h)\bigr),\qquad
q=\operatorname{Run}(h,v),\quad r(h)=\operatorname{rk}^v_q(h).
\tag{41.19}
$$

The conditional recovery interface supplies the fixed source parameter
and current **exact** endpoint. For an actual realization, initially
acquire $v$ by a lawful paid source traversal if it has not already been
earned. Subsequently maintain its exact binary counts from the completed
macro and (41.1), or reacquire them by a paid traversal. Neither option
is a free exact counter or a free source-tree oracle. A modular pair
field alone is not this exact endpoint. Back all integer fields,
rank growth and arithmetic workspace by sufficient lawful finite work
material for the actual finite run, and complete each count/rank
transaction before declaring its prefix record available. This is an
additional record contract, not a new source edit or a claim that a
fixed existing field has unlimited width.

The lower bound below conditions only on $v$ and $q$. If the decoder
uses additional history-dependent macro labels, primitive addresses,
source-tree information, tapes, request records, timers or external
acknowledgements, those distinctions must be included in its record
or explicitly supplied as additional side information, changing the
conditional fibre. The actual source is bound and lawful throughout;
its entire tree and archive are not freely readable decoder inputs.

**Theorem 41.6 (all-prefix causal bijection and sharp payload).** For
any source of Definition 41.1, initialize $Z_v(\varepsilon)=(v,0)$.
If $h$ currently ends at $(A,B)$, its causal rank updates are

$$
\begin{aligned}
r(hF)&=r(h),\\
r(hG)&=r(h)+C_F^v(A+1,B),\\
C_F^v(A+1,B)&=
\begin{cases}N_v(B-A-1,A+1),&1\le A+1\le B,\\
0,&\text{otherwise}.
\end{cases}
\end{aligned}
\tag{41.20}
$$

Only the completed prefix, its current endpoint and the next actual
completed macro enter this update. No final endpoint, final length or
future word is supplied. At every completed prefix, $Z_v$ has the exact
inverse $D_v$ on

$$
\mathcal I_v=\{(q,r):q\in\mathcal Q_+,\quad 0\le r<N_v(q)\}.
\tag{41.21}
$$

For $(q,r)\in\mathcal I_v$, set $D_v(v,0)=\varepsilon$. For $q\ne v$,
put $C=C_F^v(A,B)$ and define

$$
D_v(A,B,r)=
\begin{cases}
D_v(B-A,A,r)F,&r<C,\\
D_v(A-1,B,r-C)G,&r\ge C.
\end{cases}
\tag{41.22}
$$

The first branch necessarily has $1\le A\le B$; the second necessarily
has $A\ge1$ and a nonempty $G$ block. Inputs outside $\mathcal I_v$ are
rejected, with no fabricated default history. The two inverse laws are

$$
D_v(Z_v(h))=h,\qquad
Z_v(D_v(q,r))=(q,r)\quad((q,r)\in\mathcal I_v).
\tag{41.23}
$$

For every **nonempty** endpoint fibre, the least number of supplementary
payload values permitting exact recovery when $v,q$ are supplied is
$N_v(q)$. Its fixed-fibre binary width is

$$
b_v(q)=\left\lceil\log_2N_v(q)\right\rceil
\qquad(N_v(q)\ge1).
\tag{41.24}
$$

If $k$ is also supplied, the corresponding number is $N_v^{(k)}(q)$
and its width is $\lceil\log_2N_v^{(k)}(q)\rceil$ only when that count
is positive. Empty fibres admit no valid rank and no logarithmic width
claim. These are conditional payload minima, not optimal total
physical memory.

Proof. Theorem 41.3 partitions every nonbase dictionary into the two
last-letter blocks, of sizes $C_F^v(A,B)$ and
$\mathbf1_{\{A\ge1\}}N_v(A-1,B)$. This is the concrete block partition
needed for the classical enumerative ranking and inverse of Cover,
*Enumerative Source Encoding*, §I Propositions 1–2 and inverse algorithm;
the generic enumeration principle is reused here.

Appending $F$ sends the whole old dictionary bijectively onto the first
block at the new endpoint, without changing its internal rank.
Appending $G$ sends it onto the second block, so add the full first
block at $(A+1,B)$. Its $F$ predecessor is $(B-A-1,A+1)$ exactly under
(41.20)'s condition. Neither successor can be the source base, since
potential increases. This proves initialization and the updates,
including source pairs with $a=0$ and all zero-offset cases.

On a valid nonbase input, $0\le r<N_v(q)$ selects precisely one nonempty
block interval. If $r<C$, (41.13) gives a valid $F$ predecessor and the
same in-range predecessor rank. Otherwise it gives a valid $G$
predecessor and rank $r-C$ in its range. Each step decreases endpoint
potential as in Theorem 41.3. It cannot stop at a lower-potential or
unreachable cell, since such cells have no valid ranks. Thus it ends
at the unique base $(v,0)$. Induction on this decreasing potential
proves both laws in (41.23), not only decoding of the encoder's outputs.
Every realized prefix uses exactly that dictionary and those updates;
no future endpoint participates.

For the lower bound, fix $v,q$ with $N_v(q)>0$. If two distinct words
in its dictionary have the same supplementary payload, the decoder
receives identical inputs and cannot return both. Hence at least
$N_v(q)$ values are necessary. The rank bijection gives exactly that
many. Applying the same injection argument within a nonempty fixed-$k$
dictionary gives the conditional version. A fixed-width binary field
with $d$ bits has $2^d$ values, yielding (41.24), with zero bits for a
singleton. No distribution or physical storage optimality is used.
$\square$

At beta's $(2,3)$ endpoint the four histories need four payload values,
hence two bits under this interface. Conditioning additionally on
$k=1$ or $k=3$ gives a singleton, and on $k=2$ gives two histories and
one bit. At beta's $(1,1)$ endpoint one bit distinguishes $F$ and $G$;
at any fixed source $v$, its empty-history fibre needs no rank data bit.
The decoder determines $k$ from the recovered word; it never assumes
that the endpoint has already determined $k$.

**Proposition 41.7 (finite charged arithmetic and the source boundary).**
For a current endpoint of potential $S=A+B\ge s_0$, a finite exact
calculation of all counts needed by (41.20)–(41.22) is obtained by filling
(41.13)'s total-count recurrence over $\mathcal Q_+\cap\{A+B\le S\}$ in
increasing potential, with base (41.14). It uses $O(S^2)$ table cells,
each of $O(S+1)$ bits. Use a work-array bit-cost model charging
$O(S+1)$ bit operations to access and add cells of that width, with
$O(\log(S+1))$-bit indices. This gives $O((S+1)^3)$ sufficient table
bits and arithmetic bit work per complete fill.
A decoder can reuse this table, perform at most $S-s_0$ predecessor
steps and materialize that many macro letters. Recomputing at every
completed prefix of a run ending at potential $S_*$ gives a conservative
$O((S_*+1)^4)$ total arithmetic bit-work upper bound. These bounds
exclude native source traversal, communication and physical duration.

Proof. There are $\sum_{s=1}^S s=O(S^2)$ valid pair cells. In each
reachable cell at potential $s$, every word has length at most $s-s_0$,
so its count is at most $\sum_{i=0}^{s-s_0}2^i=2^{s-s_0+1}-1$.
Unreachable cells have count zero. Hence $O(S+1)$ bits per cell suffice,
and each recurrence requires at most one addition of that width.
Binary indices, comparisons and table addressing also fit the stated
conservative bounds. The decreasing-potential proof of (41.22) gives
at most $S-s_0$ rank comparisons/subtractions; their $O(S+1)$-bit work
and the output fit within the table bound. There are at most
$S_*-s_0$ nonempty completed prefixes, each with potential at most
$S_*$; summing fresh-fill bounds proves the last assertion. No eventual
$S_*$ is used by the algorithm; it is only an analysis parameter.
$\square$

This is a sufficient arithmetic realization conditional on lawful
backed binary work records, not a claim about minimum peak workspace.
The supplementary payload count excludes the source, authentic binding,
rights, ancestral tapes, installed program, initial/current pair fields,
width metadata, table, temporary arithmetic, decoder/output buffers and
reserved cleared capacity. All are charged separately. A native $F$
performs $a'$ promotions and $b'$ splits at current composition $(a',b')$
after acquiring its $a'+b'$ entry rows; a $G$ performs one split after
acquiring its actual leftmost path. Navigation, field operations,
replies and returns add their own work. No unit-cost integer, default
acknowledgement or modular field supplies the exact count table.

Recovering $h$ does not recover an unspecified earlier source tree,
authentic reference, complete tape or physical time. If a logical
description of $t_0$ has itself been lawfully acquired and supplied,
evaluating its recovered macros computes $t_h$ and their deterministic
successful primitive edit trace in the mathematical syntax, with the
corresponding computation and output costs. Merely supplying $v$ does
not supply that initial tree description. Evaluation of a description
is not physical replay, cloning, a source reset or inversion of growth.
The rank holds at completed transactions; interruption/fault recovery
inside a transaction requires its own contract.

### 41.5 Suppliers and the exact scope of the synthesis

The source-specific deduction is the exhaustive fixed-$F$ run and
affine-action-fibre classification, its sum over **all** $k$ for every
fixed attained beta-positive source, and the concrete current-endpoint
rank bijection using those complete native macro dictionaries. The
chronological affine action itself is reused from
[GraftAffineClosure](../../../D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean),
including `step`, `run`, `atomicBlock`, `matrixM` and the affine supplier
within `result`. There false denotes replacement and true translation.
[PositiveClosingExecution](../../../D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.lean)
uses the opposite Boolean orientation, as its `residue_run` map by
`Bool.not` records. This section uses named chronological letters and
does not transfer a modular closing period into a native inverse.

The actual source correspondence and domain are
[LAB Arithmetic Growth, §§9.3–9.4 and 12.2](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md).
The causal counted-block and actual-image interfaces, including their
separate retained bits, workspace and output costs, are already present
in [Spatial Records Chronology, §§18–20 and 23.1](RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md)
and [Boundary Dynamics, Propositions 102.4–102.5](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md).
The latter are the proposition numbers, distinct from that chapter's
subsection numbers. The paid source-bound compressed-record interface
is [AAII §47](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md).
[FARG](FIBONACCI_ATOMIC_RELATION_GENERATION.md) supplies literal tree
substitution and the composition/quantity interpretation;
[Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)
supplies the typed distinctions among action, boundary, memory and
process. None of these citations identifies arithmetic alpha
translation with permission for a literal native root graft.

Cover, *Enumerative Source Encoding*, IEEE Transactions on Information
Theory **19**(1), 73–77 (1973), [author PDF](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf),
§I Propositions 1–2 and inverse algorithm, supplies the generic finite
ranking method, not a new coding principle here. Berstel, *An Exercise
on Fibonacci Representations*, RAIRO–Theoretical Informatics and
Applications **35**(6), 491–498 (2001), [full text](https://www.numdam.org/item/ITA_2001__35_6_491_0.pdf),
concerns normalization and counting of binary Fibonacci
representations; it is generic prior art, not a premise that its
bounded-digit dictionaries equal (41.7)'s arbitrary nonnegative run
multiplicities. No Frougny result is a premise. The synthesis is
`repo-derived`; these searched suppliers do not establish worldwide
originality, and the prose proofs assert no new Lean verification.

All results concern finite completed histories under the declared
same-source rights, material and exact-record contract. A policy
excluding some macro words changes the operational dictionary; the
unrestricted counts above cannot silently be reused for that policy.
For the supplied $v$, the literal macro chronology and the enriched
boundary $(q,r)$ mutually recover on their actual images. A lawfully
supplied initial logical tree description additionally makes either
one determine the final tree and successful primitive trace; reversing
from the final tree alone is not asserted. Endpoint counts alone do not
recover general shape or chronology. None of these maps supplies
elapsed time, physical bytes, source authority or unknown prior history.
This finite synthesis leaves the continuous RRO research objective open.

## 追加锚（本行以下为增补区）

## 42. Recovering an unknown native entry and its completed macro history

### 42.1 The entry event index and the geometry retained by the source

**Definition 42.1 (same-source recovery inputs).** Retain Definition
41.1's one actual LAB root/source/epoch, authentic binding, current
exclusive rights, lawful traversals, all-event ancestral tapes and
sufficient finite material for each finite run. The attained entry
$t_0$ ranges over the entire tree domain $\mathcal D_+$, not one seed,
one composition fibre or one prescribed shape. After attachment the
only source-changing operations are completed native $F/G$ macros:
$F$ is LAB Definition 9.3's sealed old-frontier replacement $\rho$;
$G$ is its acquired current leftmost-beta split. There are no
interleaved source-changing legacy edits. Every inner and outer call
consumes its full serialized reply, acknowledgement and real return.
A completed inner primitive alone need not be a completed outer macro.

For a logical tree put

$$
\ell(t)=a(t)+b(t),\qquad n(t)=a(t)+2b(t)-1.
\tag{42.1}
$$

Write $\operatorname{Run}(W,t)$ for the logical tree after the
chronological completed word $W$; the pair-valued Run of §41 is its
composition projection. The recovery inputs here are precisely an
authenticated exact entry index $n_0=n(t_0)$ and the lawfully acquired
final logical syntax $z=\operatorname{Run}(W,t_0)$. Neither the old
syntax, its composition, its leftmost depth nor the macro length is an
additional input. Recovery targets $(t_0,W)$ as logical syntax and a
literal word. Pointer identity, allocated runtime bytes, authority,
pre-attachment primitive order and elapsed time are different targets.
The acquisition conditions are made explicit in Proposition 42.6.

**Lemma 42.2 (exact event count and spine record).** The value $n(t)$ is
the exact number of successful addressed $P/S$ events from the original
allocated alpha to any attained $t$. On $\mathcal D_+$, $n(t)=1$ holds
exactly at beta, and $n(t)>1$ exactly at multileaf entries. Each completed
macro extends the logical leftmost spine by exactly one.

More precisely let

$$
\operatorname{Sp}()=\beta,\qquad
\operatorname{Sp}(r_1,\ldots,r_d)
 =\langle\operatorname{Sp}(r_2,\ldots,r_d),r_1\rangle.
\tag{42.2}
$$

Every $t\in\mathcal D_+$ has one such presentation, where $r_1$ is
the root's right subtree and $r_d$ is the deepest right subtree.
With $d$ its logical leftmost depth,

$$
\begin{aligned}
F(t)&=\operatorname{Sp}(\rho r_1,\ldots,\rho r_d,\alpha),\\
G(t)&=\operatorname{Sp}(r_1,\ldots,r_d,\alpha),\\
n(F(t))-n(t)&=\ell(t),\qquad n(G(t))-n(t)=1.
\end{aligned}
\tag{42.3}
$$

For $W=X_1\cdots X_m$, let $K=|W|_F$ and
$k_i=|X_{i+1}\cdots X_m|_F$. In the final spine, each entry position
$j\le d$ has right subtree $\rho^K r_j$, and the position born at
macro $i$ has right subtree

$$
\rho^{k_i}\alpha\quad(1\le i\le m).
\tag{42.4}
$$

Proof. AA Definition 19.1, equation (AA.73), gives the alpha-origin
split count $a+b-1$ and promotion count $b$, independently of their
legal shuffle. Their sum is (42.1). Equivalently every $P$ and $S$
increments $n$ by one, starting at zero. Since $b\ge1$ on
$\mathcal D_+$, $a+2b-1=1$ forces $(a,b)=(0,1)$, hence the singleton
beta tree. Every other entry has a branch. LAB Lemma 2.1 gives a beta
at the end of its logical left descent; this proves the unique spine
presentation, including the empty spine at beta.

Global replacement preserves the old spine branches, replaces every
old right subtree by its $\rho$ image and replaces its terminal beta
by $\langle\beta,\alpha\rangle$. Native $G$ changes only that terminal
beta. These are exactly the first two equations of (42.3). LAB Theorem
9.4 gives their composition laws, whose substitution into (42.1)
gives the last two equations. Induction on the chronological word now
proves (42.4): a new spine position has right alpha; every later $F$
replaces that whole subtree, and every later $G$ leaves it unchanged.
$\square$

The positions in (42.4) are proof coordinates, not acquired macro
markers or a stored entry depth. They explain how this restricted
chronology survives in geometry. The trees $\rho^k\alpha$ are pairwise
distinct: for every nonempty ordered tree, replacement increases
$a+2b$ by $a+b>0$. At two consecutive positions known to have been
born after attachment, their exponents differ by one precisely when
the later macro is $F$, and otherwise agree. The decoder below also
locates the entry without being supplied those positions. Logical
spine depth counts binary source branches. In AA Definition 17.3's
material realization, a beta has a unary terminal marker; that extra
material edge is excluded from this depth and from every macro frontier.

### 42.2 The two possible predecessors and a terminating inverse

**Lemma 42.3 (native overlap and its entry boundary).** Let
$\mathcal O=G[\mathcal D_+]$. It is exactly the set of native trees
with a nonempty leftmost spine whose deepest right subtree is alpha.
Its inverse $\operatorname{pr}:\mathcal O\to\mathcal D_+$ collapses
only the deepest $\langle\beta,\alpha\rangle$ to beta. Every
nonempty completed macro word ends in $\mathcal O$.

Reuse the actual-image inverse $\delta$ of $\rho$ from PG §37.2,
(PG.3705), and Theorem 44.6. Thus its domain is the decidable grammar

$$
I=\rho[\mathcal T]::=\beta\mid\langle\beta,\alpha\rangle
                              \mid\langle I,I\rangle.
\tag{42.5}
$$

For $s=\operatorname{Sp}(r_1,\ldots,r_d)\in\mathcal D_+$ put
$H(s)=\operatorname{Sp}(\rho r_1,\ldots,\rho r_d)$. Then

$$
\begin{aligned}
F(s)&=G(H(s)),&\operatorname{pr}(F(s))&=H(s),\\
n(H(s))&=n(s)+\ell(s)-1.&&
\end{aligned}
\tag{42.6}
$$

At beta, $H(\beta)=\beta$. At every multileaf $s$, $H(s)\notin
\mathcal O$ and $n(H(s))>n(s)$. In particular, an overlap
$F(s)=G(u)$ forces $u=H(s)$; for multileaf $s$, this $u$ cannot itself
have arisen from a nonempty completed macro word.

Proof. The spine presentation proves the characterization of
$\mathcal O$, the collapse inverse and injectivity of $G$. Equation
(42.3) puts both macro outputs in $\mathcal O$ and proves the first
line of (42.6). The second follows by subtracting the one-event $G$
increment from $n(F(s))=n(s)+\ell(s)$.

The reused grammar (42.5) has disjoint alternatives because
$\alpha\notin I$: the special pair has right alpha, whereas an internal
pair of images has right child in $I$. Recursion on finite subtrees
decides membership and computes $\delta$; it also supplies the reused
global injectivity of $\rho$. For multileaf $s$, the deepest right
subtree of $H(s)$ is $\rho r_d$, which cannot be alpha. Thus it is
outside $\mathcal O$ and cannot be a nonempty macro output. Its strict
$n$ inequality follows from $\ell(s)\ge2$. Applying the collapse to
$F(s)=G(u)$ gives the asserted unique $u$. $\square$

**Theorem 42.4 (unknown-entry recovery and the sole beta ambiguity).**
For every fixed $n_0>1$, the map

$$
(t,W)\longmapsto\bigl(n_0,\operatorname{Run}(W,t)\bigr),\qquad
 t\in\mathcal D_+,\quad n(t)=n_0,\quad
 W\in\{F,G\}^{<\omega},
\tag{42.7}
$$

is injective on its entire stated domain. It has a terminating inverse
on its actual image, recovering both the unknown initial logical tree
and the literal macro word, including the empty word. No entry
composition or depth is supplied.

For $n_0=1$, the entry is beta. The endpoint beta has just its empty
history. Every nonempty reachable final logical tree has exactly the
two preimages

$$
(\beta,FU),\qquad(\beta,GU)
\tag{42.8}
$$

for one uniquely determined suffix $U$. Conditional on $n_0=1$, such
a nonempty final tree and no other distinguishing channel, a supplement
recovers the target exactly if and only if it separates these two
preimages. One binary first-macro choice is necessary and sufficient.

Proof. Here is a decoder for $n_0>1$. Reject a nonnative input or one
with $n(z)<n_0$. If $n(z)=n_0$, return $(z,\varepsilon)$. Otherwise
require $z\in\mathcal O$ and put $c=\operatorname{pr}(z)$. Select the
last letter and its predecessor by

$$
(p,X)=
\begin{cases}
(c,G),&n(c)=n_0\ \text{or}\ c\in\mathcal O,\\
(\delta z,F),&\text{otherwise, provided }z\in I
                         \text{ and }\delta z\in\mathcal D_+.
\end{cases}
\tag{42.9}
$$

Reject when the second branch has no stated predecessor or when
$n(p)<n_0$. Recursively decode $(n_0,p)$ as $(t,V)$ and return
$(t,VX)$. All membership tests, collapse, counts and the actual-image
inverse are finite syntax operations. In the $G$ branch $n$ decreases
by one. In the $F$ branch it decreases by $\ell(p)\ge1$. Thus the
recursion terminates in at most $n(z)-n_0$ predecessor steps, with
rejection allowed off the image.

To prove that this decoder selects the actual last letter, consider
any nonempty actual word with input entry index $n_0>1$. Its current
predecessor $s$ is multileaf, since event count never decreases. If
its last letter is $G$, then $c=s$. Either the preceding word is empty,
so $n(c)=n_0$, or it is nonempty, so $c\in\mathcal O$. The first
branch therefore applies. If its last letter is $F$, Lemma 42.3 gives
$c=H(s)\notin\mathcal O$ and $n(c)>n(s)\ge n_0$. Neither condition
of the first branch holds. The second applies and $\delta z=s$.
Induction on decreasing $n$ proves that the returned pair is exactly
the actual $(t,W)$. Consequently two such pairs with the same input
cannot differ, even if their entry trees, depths and word lengths
were initially unknown.

Conversely every accepted predecessor in (42.9) really satisfies
$X(p)=z$. At the base the recovered tree is native and has index
$n_0$. Induction back up the recursion shows that every accepted
answer belongs to the actual image and replays to the supplied
logical syntax. This proves both inverse laws on that image, rather
than merely uniqueness of a promised word.

When $n_0=1$, Lemma 42.2 forces beta and strict event growth separates
the empty word. Both first letters send beta to
$K=\langle\beta,\alpha\rangle$, whose index is two. Apply the already
proved $n_0=2$ inverse to the final tree: it returns $(K,U)$ with a
unique $U$. This proves exactly (42.8). A decoder receiving identical
supplementary values on these two targets cannot distinguish them;
two different values suffice by selecting their first letter. This
is the ordinary conditional injection bound applied to this concrete
two-point fibre. $\square$

A retained request, script or controller record can already reveal that
first choice; the theorem then requires no additional bit beyond those
supplied inputs. It does not assert that two complete installations
have identical observations. In particular their macro requests can
differ even when the successful source edits agree. The inverse
computes descriptions. It does not undo source edits, restore old
pointers or grant a reset, deletion or inverse-growth capability.

### 42.3 A sharp bounded INITIAL reference

**Proposition 42.5 (least attachment-reference alphabet).** Fix an
integer $N\ge2$. The entry is unknown in

$$
\mathcal E_N=\{t\in\mathcal D_+:2\le n(t)\le N\}.
\tag{42.10}
$$

An encoder $E:\mathcal E_N\to A$ is fixed at attachment independently
of all future macro choices. Supply only $E(t)$ and the final logical
tree; the target is both $t$ and every finite completed macro word.
The least possible attained reference alphabet has exactly $N-1$
values. The exact index $E(t)=n(t)$ attains it, with conditional
fixed-width binary width $\lceil\log_2(N-1)\rceil$.

Proof. Theorem 42.4 supplies a decoder with the $N-1$ indices
$2,\ldots,N$. For the reverse inequality, put
$t_j=G^{j-1}(\beta)$ for $2\le j\le N$. These are actual native
entries obtained after the original alpha promotion and successive
leftmost-beta splits. Their indices are $j$, and all have the common
final logical tree $t_N$, using the future word $G^{N-j}$, including
the empty word at $j=N$. The targets $(t_j,G^{N-j})$ are distinct.
Their attachment references must therefore be distinct when the
final tree is fixed. Hence at least $N-1$ attained reference values
are necessary. The generic pigeonhole and binary-width principles
are reused; the native common-endpoint chain gives their lower-bound
instance and Theorem 42.4 gives the matching upper bound. $\square$

This is a side-information theorem for an attachment reference, not
a minimum total physical-memory claim. It conditions on the complete
final syntax and excludes all other history-dependent inputs. Adding
beta to the entry domain makes this target impossible for an encoder
of $t$ alone: $E(\beta)$ is the same for $F$ and $G$, which have the
same final tree. A future first-choice distinction must then be supplied
through some other channel.

### 42.4 Acquired syntax, old ancestral tapes and macro parsing

**Proposition 42.6 (paid inputs and the addressed-expansion consequence).**
Under Definition 42.1, an exact entry index can be acquired by a
stationary finite traversal of the actual bound source, counting its
logical alpha and beta leaves with backed exact counters and computing
(42.1). It can instead be supplied by a correctly maintained backed
exact counter of all successful alpha-origin events. A final stationary
finite traversal acquires the complete final logical syntax. Conditional
on these acquired inputs and finite decoding workspace/output, Theorem
42.4 needs no ancestral-tape contents as decoder input for its target.

For each fixed multileaf entry, the map from completed native macro
words to their full indexed addressed primitive expansions is injective.
At beta, its only ambiguity is the first letter in (42.8). If the current
source and its acquired all-event ancestral tapes are supplied, AA
Theorem 19.2 recovers their full alpha-origin indexed addressed primitive
history. An authenticated exact $n_0$ then locates the continuation
suffix, and replay of the first $n_0$ acquired events on logical syntax
recovers the entry if needed. These interfaces do not insert macro
delimiters in the primitive records.

Proof. The traversal uses AA Definitions 17.3 and 20.2's arity parsing
and LAB's stationary logical-frontier acquisition. From the authentic
root follow only existing logical child links, check current grants and
the actual reached references, and exclude beta's unary material marker
from the logical frontier. A finite traversal stack, acquired address
backing and exact finite counter fields suffice to count each logical
leaf once. The same finite traversal, retaining ordered constructors
and leaf tags, obtains final syntax. Retain the source binding and epoch
across both acquisitions and the intervening macros. Source stability
through each traversal and serialization exclude mixing counts or
subtrees from different cuts. All reference tests, reads, arithmetic,
list operations, reply transport, workspace, clearing and output are
charged uses of finite owned material. Counter width must suffice for
the actual finite value; it is not an unbounded finite-control state.
Attachment may discard its acquired old syntax after computing $n_0$;
Theorem 42.4 does not secretly retain it as another decoder input.

The default modular pair fields of LAB §11 give residues, not an exact
$n_0$. They cannot replace this acquisition without an additional proven
range/counter contract. Likewise the syntax is acquired data, not a
free computation oracle, guessed reference or waiting-as-a-clock.
Every finite syntax operation of the inverse terminates; backing all
its integers, parsed trees, recursive work and materialized word gives
a finite computation for each admitted finite input. This is neither
a runtime bound for the native driver nor an assertion that one fixed
finite arena handles all future inputs.

For the expansion claim, the primitive list and fixed initial logical
tree determine the final logical tree by the original addressed rules.
Theorem 42.4 then recovers the unique word for a multileaf entry. At beta
the two first macros both expand to the same single $S_\varepsilon$;
the suffix starts at the same $K$ and has the same deterministic
expansion. The theorem excludes any further ambiguity. This reuses
AA19.2 for full-order recall from the current source and all-event tapes:
its decoded events include both kinds and their logical addresses.
By Lemma 42.2 the supplied $n_0$ is precisely the old-prefix length,
so indices $n_0+1,\ldots,n(z)$ select the continuation. Replay of its
old prefix from the known alpha computes $t_0$ as a description.
Thereafter the source inverse, or primitive replay followed by it,
recovers macro grouping with the stated beta qualification. No recall
request is presumed callable outside the existing Ready contract.
$\square$

Dispensing with tape contents in this decoder does not remove tapes
maintained by the installation. It establishes no smaller total storage
or faster native implementation. Old tape acquisition, source growth,
frontier acquisition, code, roots, rights, buffers and output retain
their own costs. Nor does the source-only decoder recover an arbitrary
pre-attachment primitive shuffle: that separate target still uses the
appropriate records.

### 42.5 Lawful partial cuts and the limits of content projections

**Proposition 42.7 (equal content at unequal completion cuts).** Start
from the same attained multileaf $t$, with any one coherent prior
primitive history and its tapes. Let $p$ be its leftmost beta address.
Compare these two legal alternative executions: a fully returned $G$,
and an $F$ paused after its first successful primitive has completed
maintenance, its literal reply, acknowledgement and inner return. Their
logical source and all ancestral-tape contents are equal. Their complete
outer controller/Busy/Ready/return states differ. Thus this content
projection cannot certify outer completion or distinguish these two
macro situations.

There is also a stronger source-only collision at every multileaf entry:
the fully completed word $GF$ and the execution of $F$ followed by
exactly the first two successful primitives of a second $F$ have the
same logical source. The latter second macro is genuinely incomplete.
Their primitive chronologies and coherent tape contents differ.

Proof. The first old-frontier row in $F$ is the acquired current
leftmost beta. Hence both compared first executions perform exactly
$S_p$ on the same source. The all-event appends are identical and
complete at the chosen inner-return cut, giving the same logical
source and tape words. There is at least one other old-frontier row
because $t$ is multileaf. The $F$ caller retains those unprocessed rows
and its continuation and has not returned; $G$ has returned. Even at
beta the content equality holds if $F$ is paused before its outer
return, though no further primitive row then remains. Such equality
is a statement about a projection of legal joint states, not equality
of full observers.

For the stronger collision, let $E$ be the nonempty left-first sequence
of edits at all old leaves other than $p$. Its addresses are
prefix-incomparable with $p$. The successful primitive expansions are

$$
\begin{aligned}
GF &: S_p\,S_{pL}\,P_{pR}\,E,\\
F\text{ then two primitives of }F &: S_p\,E\,S_{pL}\,P_{pR}.
\end{aligned}
\tag{42.11}
$$

Indeed after $G$, the first two frontier leaves are the new beta at
$pL$ and alpha at $pR$. After the first $F$, exactly these are again
the first two leaves of the next sealed frontier. Both displayed
executions replace the old subtree beta at $p$ by
$\langle\langle\beta,\alpha\rangle,\beta\rangle$ and replace every
other old leaf once by its $\rho$ image. Edits in $E$ commute with
those at $pL,pR$ because their target subtrees are disjoint; hence
the logical endpoints agree. The second frontier also contains
leaves outside $p$, so after its first two rows that macro still has
unprocessed rows. The two primitive lists differ: immediately after
$S_p$, one edits $pL$, the other edits an address outside $p$.
AA19.2's source-relative tape bijection therefore makes their tape
contents different at the common endpoint. $\square$

The first comparison uses the source-and-tape-content projection;
the second uses only logical source. Neither supplies an outer
FetchGrowth call while busy or during unfinished maintenance. At an
inner Ready cut the surrounding caller can still be Busy, and the
outer request contract need not admit recall. Mathematical evaluation
of a coherent tape word is separate from a lawful callable observation.
These collisions do not refute the completed-word theorem: one side
of each comparison is outside its completed-macro domain.

### 42.6 Restricted macro orbits, endpoint archives and supplier scope

**Corollary 42.8 (number of native final trees in a composition fibre).**
Fix an attained multileaf entry $t$ of composition $v$. With $N_v(q)$
as already computed in §41, the number of distinct $F/G$-reachable
final logical trees of composition $q$ is exactly $N_v(q)$. For the
beta entry and a nonempty reachable endpoint $q\ne(0,1)$ it is
$N_{(0,1)}(q)/2$. At $q=(0,1)$ there is the one empty-history tree;
unreachable endpoints give zero.

Proof. LAB12.2 identifies each word's final composition with §41's
pair Run. For a fixed multileaf entry, Theorem 42.4 makes the map from
that complete endpoint dictionary to final logical trees injective;
it is surjective by the definition of its restricted orbit. At beta,
Theorem 42.4 gives exactly two words per nonempty final tree. Their
compositions agree, so each nonempty dictionary has even size and
halving counts its distinct trees. Strict growth excludes a nonempty
word at the beta endpoint. $\square$

For example §41.3's four words at beta's composition $(2,3)$ yield
exactly two native trees, as its explicit trees already show. The
corollary counts the restricted macro orbit. It does not count all
primitive-reachable trees of that composition, and it does not
rederive §41's affine-action, full-word counting or ranking theory.

**Proposition 42.9 (every-returned-macro pair archives).** Suppose the
exact composition at attachment and after every completed macro is
supplied as an acquired chronological archive. It determines all
macro choices except the initial choice at beta. A single final pair,
primitive-kind-only records, unordered work totals or §40's sparse
block archives are different projections and do not in general
supply this information.

Proof. At a current composition $(a,b)$ the two possible successors
are $(b,a+b)$ and $(a+1,b)$. They agree exactly when $a=0,b=1$.
In $\mathcal D_+$ that pair forces beta. After the first macro its
index strictly exceeds one and it never returns to beta. Successive
exact pairs therefore determine every subsequent choice; at beta
the first pair transition leaves the two choices unresolved.

For the contrasting projections, §41.3's $GFF$ and $FGFG$ have the
same final pair but different trees, and each has exactly two $F$'s,
two successful primitive promotions and four splits when started at
beta; their macro lengths nevertheless differ. At the attained entry
$\langle\beta,\beta\rangle$, the completed words $F$ and $GG$ expand
to $S_LS_R$ and $S_LS_{LL}$ respectively. Both have primitive-kind
word $SS$, zero promotions, two splits and final composition $(2,2)$,
but their logical endpoints are respectively
$\langle\langle\beta,\alpha\rangle,\langle\beta,\alpha\rangle\rangle$
and $\langle\langle\langle\beta,\alpha\rangle,\alpha\rangle,\beta\rangle$.
Thus even within the completed menu these smaller projections lose
macro choices. Separately, the arbitrary legal primitive lists
$S_LS_R$ and $S_RS_L$ from that entry have the same logical endpoint
and kind word but different addressed order; the latter list is not
its completed $F$ expansion. The sparse pair-archive collision family
is exactly §40.3's paid block interface, whose record omits the
intermediate returned-macro cuts. $\square$

The archive in Proposition 42.9 contains paid cut history; it is not a
source-only input or a full physical record. A primitive-kind word
supplies neither its addresses nor macro separators. Conversely
arbitrary $P/S$ shuffles with the same final source, as in AA17–19,
do not refute Theorem 42.4's restriction to the completed native menu.
None of the event counts, macro words or archives is elapsed time.

**Convention 42.10 (reused results and the new correspondence).** The
substantive correspondence here is between the completed native
macro history with its unknown entry and the final logical source
with an exact entry event index, uniformly over all attained
$\mathcal D_+$. Its proof uses the native leftmost-spine overlap in
Lemma 42.3. LAB9.3–9.4 and 12.2 supply the actual macro/source bridge;
AA17 and 19–23 supply attainment, alpha-origin event counting,
all-event tapes and lawful Ready service. FARG supplies the ordered
syntax and global substitution. PG37.2's (PG.3705) and PG44.6 supply
the actual-image parser and global substitution injectivity. In
[GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean)
the proof of global substitution injectivity is the local
`have substitution_injective` inside `result`, not a separately
exported declaration of that name. These are reused mathematical
suppliers, without a new compilation or kernel-certification claim.

[Native Entry Reference and Graft Order, §3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ENTRY_REFERENCE_AND_GRAFT_ORDER.md)
reuses the same $\rho$ parser but has a different $G$, a root graft.
Its disjoint-menu theorem does not apply to LAB's local leftmost
split: here the images overlap as (42.6) states. The generic
actual-image inverse, injection, pigeonhole and coding principles
are existing suppliers; the bounded reference application is
Proposition 42.5, not a new generic coding theorem.

Engelfriet, *Tree Automata and Tree Grammars*,
[arXiv:1510.02036v1, Definition 3.62](https://arxiv.org/html/1510.02036v1),
defines ranked-tree homomorphisms by recursive substitution. It is a
framework for $\rho$, not a proof of recognizability for this finite
local-$G$ menu. Berthé, Steiner, Thuswaldner and Yassawi,
*Recognizability for sequences of morphisms*,
[arXiv:1705.00167v2, §2](https://arxiv.org/html/1705.00167v2),
concerns morphism representations of bi-infinite sequences and their
recognizability; its domain and hypotheses are not those of (42.7).
Relative to these inspected frameworks and the cited repository
suppliers, the native recovery correspondence is `repo-derived`.
No worldwide originality or formal verification of this append is
asserted. The results concern finite completed runs and explicitly
projected partial cuts; they leave the broader RRO recovery questions
and the continuing research objective open.

## 追加锚（本行以下为增补区）

## 43. Native partial-frontier recognizability and complete unfinished-history fibres

### 43.1 The native prefix and its two admissibility sorts

**Definition 43.1 (coherent prefix syntax).** Retain Definition 42.1's
one LAB root/source/epoch, authentic operands, exclusive current rights,
full ancestral tapes and finite backing per finite run. Let $L(u)=\ell(u)$.
For $u\in\mathcal D_+$ and $0\le j\le L(u)$, define $F_j(u)$ to be the
logical source after exactly the first $j$ rows of Definition 41.1's
sealed OLD frontier have completed their guarded primitive, all tape and
arithmetic maintenance, literal reply, acknowledgement and inner return.
Newly born leaves are excluded. Thus $F_0(u)=u$, $F_{L(u)}(u)=\rho(u)$,
and native $G(u)=F_1(u)$. An active outer call has not yet returned;
even at $j=L(u)$ its pending output/acknowledgement/return is retained.
At $j=0$ acquisition may still precede sealing or a next-row operand.
Only such coherent source cuts, and stationary control transitions
between them, are considered; an unfinished inner commit is excluded.

For the inverse use two syntax sorts, not two new source types:

$$
\mathcal T_B::=\beta\mid\langle\mathcal T_B,\mathcal T_A\rangle,
\qquad \mathcal T_A::=\alpha\mid\mathcal T_B.
\tag{43.1}
$$

AA Theorem 17.2 gives $\mathcal T_A=\mathcal D$ and
$\mathcal T_B=\mathcal D_+$. The left child of any branch belongs to
$\mathcal T_B$, because it is born beta and cannot become alpha;
the right child may also be an untouched alpha. At the actual root,
using sort $B$ means that the initial promotion has already happened,
not that its actual birth type was beta. Extend $F_j$ descriptively to
either sort by applying $\rho$ once at its first $j$ original leaves.
This auxiliary extension at alpha gives no native $G$ there.

Reuse the actual-image inverse $\delta:I\to\mathcal T$ of (42.5).
For $s\in\{A,B\}$ define the decidable full-image predicate

$$
J_s(y)\quad\Longleftrightarrow\quad y\in I\ \text{and}\
\delta(y)\in\mathcal T_s.
\tag{43.2}
$$

Both conditions matter: $\langle\beta,\beta\rangle\in I$ but its
inverse $\langle\alpha,\alpha\rangle$ is not attained. Counts use
$n=a+2b-1$ as in (42.1), not elapsed time or material depth.

### 43.2 A uniform ordinal inverse, including its exact domain

**Theorem 43.2 (all native partial-frontier preimages).** There are finite
effective functions $K_s(y)$ and $U^s_j(y)$ on the following exact domain:
$y\in\mathcal T_s$ and integer $0\le j\le K_s(y)$. They satisfy

$$
\begin{aligned}
\{(u,j):u\in\mathcal T_s,\ 0\le j\le L(u),\ F_j(u)=y\}
 &=\{(U^s_j(y),j):0\le j\le K_s(y)\},\\
U^s_j(F_j(u))&=u,\qquad F_j(U^s_j(y))=y,\\
n(U^s_j(y))&=n(y)-j.
\end{aligned}
\tag{43.3}
$$

In particular $K=K_B$ and $U_j=U^B_j$ give the required entire
$\mathcal D_+$ fibre, uniformly over different unknown entry trees.
For $J_s(y)$ there is the additional saturation identity

$$
K_s(y)=L(\delta y),\qquad U^s_{K_s(y)}(y)=\delta y.
\tag{43.4}
$$

An input outside the stated sort, a negative/noninteger progress, or
$j>K_s(y)$ rejects. The maximum need not be a fully returned frontier;
(43.4) applies exactly to native full images, not to every $y$.

Proof. Put $C=\langle\beta,\alpha\rangle$. The recursion starts with

$$
\begin{array}{c|c|c}
(s,y)&K_s(y)&\text{positive-progress inverse}\\\hline
(A,\alpha)&0&\text{none}\\
(A,\beta)&1&U^A_1(\beta)=\alpha\\
(B,\beta)&0&\text{none}\\
(s,C)&1&U^s_1(C)=\beta
\end{array}
\tag{43.5}
$$

Always put $U^s_0(y)=y$. For a branch $y=\langle v,w\rangle\ne C$,
first decide $J_B(v)$. If true put $k=L(\delta v)$ and set

$$
\begin{aligned}
K_s(y)&=k+K_A(w),\\
U^s_j(y)&=
\begin{cases}
\langle U^B_j(v),w\rangle,&0\le j\le k,\\
\langle\delta v,U^A_{j-k}(w)\rangle,&k<j\le k+K_A(w).
\end{cases}
\end{aligned}
\tag{43.6}
$$

If $J_B(v)$ is false, set instead

$$
K_s(y)=K_B(v),\qquad
U^s_j(y)=\langle U^B_j(v),w\rangle\quad(0\le j\le K_B(v)).
\tag{43.7}
$$

These are structural recursions on proper subtrees. Membership in $I$,
$\delta$, sort tests and leaf counts also recurse on finite syntax.
They terminate on every finite input, including irregular attained trees.

We prove the complete fibre assertion and (43.4) simultaneously by
structural induction on $y$. At a leaf alpha, no nonempty edit can have
produced it. At a leaf beta, the only positive prefix is the one alpha
promotion, admitted in sort $A$ and excluded in sort $B$. At $C$, a
positive prefix from a single leaf is precisely the beta split. It
cannot instead come from a branch: that branch's first original leaf
lies in its left child of sort $B$, whereas the output left child beta
has no positive-progress preimage of sort $B$. These observations prove
(43.5), its uniqueness, and its full-image saturation cases.

Consider now $y=\langle v,w\rangle\ne C$. A preimage with positive
progress cannot be a leaf, since a one-leaf edit gives only beta or $C$.
Write it $u=\langle x,z\rangle$. If $j\le L(x)$, the prefix acts only
on the left: $v=F_j(x)$ and $w=z$. The smaller-tree induction gives
exactly $x=U^B_j(v)$, for $0\le j\le K_B(v)$. If $j>L(x)$, the
whole left child has been replaced: $v=\rho x$, so necessarily
$J_B(v)$, $x=\delta v$, and $L(x)=k$. The right child must then be
$z=U^A_{j-k}(w)$, with $1\le j-k\le K_A(w)$. These conditions are
also sufficient by the actual left-first prefix rule.

When $J_B(v)$ fails, the second possibility is absent, giving (43.7).
When it holds, the smaller-tree saturation identity says
$K_B(v)=k$ and $U^B_k(v)=\delta v$. Thus the possibilities meet at one
identical boundary value $j=k$ and give exactly (43.6), with no gap,
duplicate entry at a fixed $j$, or extra accepted value. This proves
the complete fibre and the two inverse laws for the branch.

For its saturation case, $J_s(y)$ implies that $\delta y$ is a branch
$\langle\delta v,\delta w\rangle$: neither exceptional leaf image
is possible here. Its sorts give $J_B(v)$ and $J_A(w)$. Induction in
(43.6) gives $K_s(y)=L(\delta v)+L(\delta w)=L(\delta y)$ and the
inverse at that endpoint is exactly $\delta y$. This closes the
simultaneous induction. Each scheduled $P/S$ increases $n$ by one,
so $n(y)=n(u)+j$ and the last identity of (43.3) follows. $\square$

The birth restriction is essential to this theorem, rather than merely
to its operational interpretation. On unrestricted labelled trees,
$F_1(\beta)=F_1(\langle\alpha,\alpha\rangle)=C$.
The second entry is excluded by (43.1). At beta itself the native fibre
of its current syntax is only $(\beta,0)$; the auxiliary alpha case of
(43.5) does not enlarge that fibre. Full progress is included by (43.4)
without treating the outer call as returned.

### 43.3 Joining the completed inverse to the unfinished call

**Theorem 43.3 (complete active-macro history fibres).** For integer
$n_0\ge1$ let the completed-history supplier be the ENTIRE set

$$
\mathcal C_{n_0}(u)=\{(t_0,W):t_0\in\mathcal D_+,\ n(t_0)=n_0,
                         \operatorname{Run}(W,t_0)=u\}.
\tag{43.8}
$$

For fixed current syntax $y$, the active-$F$ target is
$(t_0,W,u,j)$, where $W$ contains only macros whose outer returns have
actually completed, $u$ is the entry to the present $F$, and this call
has completed $j$ old rows. Its exact fibre is

$$
\mathcal A^F_{n_0}(y)=
\mathop{\dot\bigcup}_{j=0}^{K(y)}
 \{(t_0,W,U_j(y),j):(t_0,W)\in\mathcal C_{n_0}(U_j(y))\}.
\tag{43.9}
$$

Active $G$ restricts the union to $j\in\{0,1\}$; returned idle has
just $\mathcal C_{n_0}(y)$ and no active progress. Every such set is
finite and effectively recognizable, with rejection off its image.
For $n_0>1$, a supplied earned $j$ selects at most one complete target;
equivalently an exact current entry index $m=n(u)$ selects
$j=n(y)-m$. For $n_0=1$, each selected nonempty completed prefix has
exactly §42.4's first-$F/G$-bit pair; an empty prefix remains separate.
The current macro identity is retained even when its effects coincide.

Proof. Given an actual target, its last coherent source is $F_j(u)$.
Theorem 43.2 forces $0\le j\le K(y)$ and $u=U_j(y)$; its preceding
returned word gives a member of (43.8). Conversely any term in the
right-hand side is realized by its completed word to $U_j(y)$, then
by the first $j$ rows of a new native $F$, pausing before its outer
return. LAB9.4 proves guards at all remaining old rows, and LAB11.2
supplies the finite complete inner calls under the same-source backing
premises. The proof is existential per finite alternative; it does not
instantiate simultaneous physical copies. Retaining $j$ makes the union
disjoint even if other coordinates coincide.

Compute $K,U_j$ and apply Theorem 42.4's actual-image decoder at each
candidate entry. Its syntax tests and strictly decreasing $n$ give a
terminating exact recognizer, including the empty word at index $n_0$.
For $n_0>1$ that theorem makes each summand empty or singleton. For
$n_0=1$, its empty case is $(\beta,\varepsilon)$; every other accepted
entry has exactly $(\beta,FV)$ and $(\beta,GV)$ with one unique $V$.
No choice between them is recovered by their common $j$ or $m$.
Restriction to $G$ uses its exactly one original beta split, not a new
macro law. Its genuine outer request still identifies it as $G$ even
at beta, where it shares the source effect of $F$. Idle follows the
completed theorem directly. $\square$

Initial-source information, a known script or control subphase can
restrict (43.9) further. Let $\mathcal A^F_{n_0,\phi,Z}(y)$ denote
the intersection with those actually supplied predicates, where $\phi$
is the actual phase and $Z$ any other acquired information. Such a
filtered set need not have interval progress indices. In the family
below even completed-history filtering removes $j=1$ while retaining
$j=0$ and larger values. Conditional cardinalities and supplement
claims always use this filtered set, not the unfiltered interval of
Theorem 43.2. Subphase compatibility is tested against the actual saved
continuation; a source-only fibre does not reconstruct arbitrary
controller bytes or grant a missing callable observation.

### 43.4 Progress, entry count and the next original boundary mark

**Proposition 43.4 (three equivalent coordinates at a coherent cut).**
Conditional on current syntax $y$ and the native prefix contract, each
of the following selects the same unique $(u,j)$ when it is accepted:
(1) earned progress $j$; (2) exact entry event count $m$; (3) the
semantic address $p$ of the next untouched ORIGINAL leaf, or exhaustion
$\top$. With the appropriate current macro/phase and $n_0>1$, any of
them also selects the unique member of (43.9). At $n_0=1$ the stated
nonempty-prefix first-bit ambiguity remains. They determine the remaining
LOGICAL old-leaf schedule, not physical row identities, rights or tapes.

Proof. The first two convert by $m=n(y)-j$ and Theorem 43.2. For the
third, reuse Native Entry Reference Definition 10.1 and Theorem 10.2,
(ER.41)–(ER.43), on labelled logical syntax, before that volume's
$E=\rho^2$ encoding. Their marked prefix is exactly $F_j(u)$ when $p$
is original leaf $j+1$, or $p=\top$ at exhaustion. Thus their parser
$D_p(y)$ recovers $u$ if and only if its marked-image tests hold.
Additionally require $u\in\mathcal D_+$; count original leaves before
$p$ to obtain $j$, or set $j=L(u)$ for $\top$. Conversely recover
$u=U_j(y)$ and enumerate its leaf addresses in left-first order to
obtain that $p$. The marked inverse's two laws prove these conversions
are inverse on the native actual image, including $j=0$ and exhaustion.
No encoded-source runtime or root-graft actuator transfers with them.

The recovered tree supplies the ordered list of its original leaves
from position $j+1$ onward and their old tags. Those untouched addresses
are still leaves of $y$ with the same tags, so each describes the next
legal $P$ or $S$. Edits at distinct old leaves preserve each remaining
guard and address by LAB9.4. This determines all remaining source edits
and their final syntax, without requiring summaries at every boundary,
a second old-tree snapshot, or persistent logical copy. It does not
identify the actual allocated list cells or manufacture bound operands.
At exhaustion the source-edit schedule is empty but the outer protocol
may still have work. $\square$

**Proposition 43.5 (causal extraction and lawful continuation).** On the
coherent cuts of Definition 43.1, LAB's existing frontier, actual saved
inner continuation/subphase, next links and live bindings suffice for
its surrounding controller to resolve the next original mark or
exhaustion whenever such a row is already acquired. Before sealing,
the actual acquisition phase instead certifies $j=0$ and may have no
next-row operand. No new counter, permanent tape or external Busy
interface is required. Exact $j$, $m$ or syntax used as observations
must be acquired with paid finite backing; otherwise they are internal
mathematical projections only.

Proof. Stationary frontier acquisition reads actual child links from
the bound root, excludes beta's unary marker, and seals precisely the
old rows, with acquired addresses/tags/references and real next links,
as LAB Definition 9.3 specifies. Before source editing, the partial
traversal is still an acquisition phase: source and $j=0$ are unchanged,
but it is not valid to dereference a presumed first sealed row. After
sealing, the first row is the next original operand.

During each inner call the saved caller continuation and current row
survive, as LAB Definition 11.1 and Theorem 11.2 state. At the coherent
cut immediately AFTER inner return but BEFORE list advancement, the raw
cursor can still name the just-completed row. Resolving the semantic
next mark then follows that row's actual next link; treating its current
raw target as untouched would execute the wrong operation. After
advancement the cursor names the next row or records exhaustion. The
saved control location distinguishes these cases. Released consumed rows
are not needed to resolve the next mark from the retained current row
and suffix. At a last row's completed return, the resolved mark is
exhaustion even before the raw cursor is cleared. If $F$'s exhausted
frontier has also been cleared during pending outer output/return, the
actual exhausted subphase still resolves $\top$ without dereferencing
any released row. This resolution uses actual subphase/continuation and
live links, not source geometry alone or a convention that the cursor
has already advanced.

An optional direct completed-row scan requires the original sealed-list
head and entire completed prefix, with the links needed to locate the
resolved cut, to remain actually backed from sealing through that scan.
Their retention, reads, finite exact counting and later clearing/reuse
are charged; a raw cursor still on the returned row counts that row as
completed. LAB13.3 permits consumed rows to be released, so this scan is
unavailable after the required prefix backing is lost: the retained
suffix is not a record of the consumed prefix.

For the active $F$ call without that optional retention, paid stationary
acquisition of current syntax $y$ together with the resolved next mark $p$
still gives
$u=D_p(y)$ and exact $j$ by Proposition 43.4. Count the original leaves
before $p$ in this recovered description; at exhaustion use
$u=\delta(y)$ and $j=L(u)$, even while outer return is pending and all
frontier rows have been released. This reconstructs no physical old
list. Before sealing, the acquisition phase instead determines $j=0$
without presuming an old list or a next-row operand.

An optional exact progress field may instead be initialized to
zero and incremented once per completed inner return, retaining its
actual pending-control distinction during the update. Such a field is
an additional paid implementation choice, not an existing field assumed
by the theorem. Exact $m$ can be acquired at macro entry by a stationary
source count, as in Proposition 42.6, or maintained through successful
events and latched at entry, with backed finite arithmetic. LAB's modular
pair fields are residues and supply neither exact count without an
additional range/backing contract. Exact attachment $n_0$ has the same
paid acquisition requirement. A stationary traversal at the coherent
current cut acquires $y$; it is not an external read request during Busy.

At each complete inner return the accepted-event hook has already
updated the actual source, all ancestral tapes and arithmetic fields.
Induction over those returns proves the projection $y=F_j(u)$ and the
one-unit source-event/progress change between successive row cuts.
Stationary acquisition, list advancement and outer output do not change
that projection. At $j=L(u)$, preserve sealed outer output, its emission
cursor, pending acknowledgement, return and clearing. They have not yet
added the present letter to $W$. Only the real outer return moves that
letter into $W$ and enters idle; it performs no new source edit or progress
increment. Active $G$ is handled identically with its single acquired
leftmost-beta operand. Its request identity is not inferred from its
possibly coincident effect.

The actual controller can continue with its authentic operand, navigation,
reference comparison and guard, then complete each inner reply and its
outer traffic. A descriptive recovered schedule alone does not supply
these resources. The actual next PROTOCOL instruction still depends on
the saved subphase: it can be list advancement, output, acknowledgement
or return rather than a source edit. Legacy indexed recall still requires
the full tapes, actual controller, current rights and bindings, and AA's
Ready request contract. An inner Ready does not make its outer caller
idle. There is no competing outer request or FetchGrowth during Busy.
No claim extends to an arbitrary in-progress append/arithmetic cut or
to recovery of the full physical controller from $(y,n_0,j)$. $\square$

### 43.5 A common-initial-source collision strictly inside both calls

**Proposition 43.6 (different remaining addressed actions).** Fix
$C=\langle\beta,\alpha\rangle$, $n_0=2$, and compare completed $FG$
followed by active $F$ at progress three, with completed $GF$ followed
by active $F$ at progress two. Both current entries have four old leaves,
both cuts are strictly internal, and both sources are

$$
y=\langle\langle\langle C,\beta\rangle,\beta\rangle,\beta\rangle.
\tag{43.10}
$$

Their remaining next source actions differ, even with the same fixed
initial source and current command $F$.

Proof. Direct addressed expansion from $C$ gives

$$
\begin{array}{c|c|c}
W&\text{completed primitive expansion from }C&u=\operatorname{Run}(W,C)\\\hline
FG&S_L\,P_R\,S_{LL}&\langle\langle C,\alpha\rangle,\beta\rangle\\
GF&S_L\,S_{LL}\,P_{LR}\,P_R&\langle\langle C,\beta\rangle,\beta\rangle
\end{array}
\tag{43.11}
$$

The chronological old-leaf lists of both displayed entries have addresses
$LLL,LLR,LR,R$. Their respective tags are $(\beta,\alpha,\alpha,\beta)$
and $(\beta,\alpha,\beta,\beta)$. In the first case the active edits
are $S_{LLL}P_{LLR}P_{LR}$; in the second they are
$S_{LLL}P_{LLR}$. Substituting their guarded effects literally gives
(43.10) in each case. The first remaining schedule is $S_R$ and the
second is $S_{LR}S_R$. Hence the next source edits, addresses and their
resulting trees differ. The entries have $n=5,6$ and the common source
has $n=8$, agreeing with the two progresses. Coherent post-advancement
cuts can have the same between-rows subphase. Their full tapes and
physical controllers are not asserted equal. $\square$

Zero-edit distinctions are separate: an active newly admitted $F$ at
$j=0$ has the same syntax as its preceding idle cut, and an exhausted
$F$ before outer return has the same syntax as its following idle cut.
The latter changes $W$ on real return without a source edit. Neither
example supplies the strict-interior ambiguity just proved.

### 43.6 A growing family and exclusion of every other history

**Theorem 43.7 (exact full and strict-interior fibres at one fixed seed).**
Define $B_0(x)=x$, $B_{k+1}(x)=\langle B_k(x),\beta\rangle$.
For $r\ge0$, $0\le a\le r$, put

$$
W_a=G^aFG^{r-a},\quad j_a=r-a+2,\quad
u_a=\operatorname{Run}(W_a,C),\quad y_r=B_{r+2}(C).
\tag{43.12}
$$

Then $L(u_a)=r+3$, $0<j_a<L(u_a)$,
$F_{j_a}(u_a)=y_r$, and $n(y_r)=2r+6$. The active-$F$ fibre conditional
on this fixed $C$ and $n_0=2$ has EXACTLY the following $r+3$ members:

$$
\begin{array}{c|c|c}
\text{completed }W&\text{entry }u&\text{progress }j\\\hline
G^{r+1}F&y_r&0\\
W_a\ (0\le a\le r)&u_a&r-a+2\\
G^{r+1}&G^{r+1}(C)&r+3
\end{array}
\tag{43.13}
$$

Consequently its strictly internal between-row fibre has exactly $r+1$
members. No selected-family lower bound is substituted for this equality.

Proof. Write $A_0=\beta$, $A_{k+1}=\langle A_k,\alpha\rangle$,
so $C=A_1$ and $G(A_k)=A_{k+1}$. Applying $F$ to $A_{a+1}$ replaces
its terminal beta by $C$ and all its $a+1$ right alphas by beta.
Subsequent $G$ calls split only the terminal leftmost beta. Thus

$$
u_a=B_{a+1}(A_{r-a+1}).
\tag{43.14}
$$

This has $r+3$ old leaves. Its first $r-a+2$ rows are precisely all
leaves of the inner $A_{r-a+1}$. Full replacement of that inner tree
is $B_{r-a+1}(C)$; none of the outer $a+1$ beta leaves has been edited.
The endpoint is $B_{a+1}(B_{r-a+1}(C))=B_{r+2}(C)$. These are literal
old-address effects because each outer branch persists and the untouched
outer leaves follow the inner leaves in left-first order. Each $B$
adds one beta, increasing $n$ by two; $n(C)=2$ gives $2r+6$.
The progresses range distinctly from $2$ through $r+2$, and all are
strictly below $r+3$.

For completeness, put $s=r+2\ge2$. The whole-image inverse gives
$\delta(B_s(C))=A_s$. Theorem 43.2 therefore gives $K(y_r)=s+1$.
Its recursion, collapsing the innermost $C$ first and then undoing
successive right beta promotions, yields

$$
U_0(y_r)=y_r,\qquad
U_j(y_r)=B_{s-j+1}(A_{j-1})\quad(1\le j\le s+1).
\tag{43.15}
$$

This can also be checked without an inverse formula: the inner
$A_{j-1}$ has $j$ leaves and its full replacement is $B_{j-1}(C)$,
leaving the $s-j+1$ outer betas untouched; at $j=1$, $A_0$ has just
one leaf. Their endpoints are all $B_s(C)$, so uniqueness in Theorem
43.2 establishes the displayed candidates and excludes all other $j$.

At $j=1$ the entry is $B_s(\beta)$, whose deepest right subtree is
beta. It is outside $\mathcal O$ of Lemma 42.3. Its index is $2s+1>2$,
so it is neither an empty-word entry at $n_0=2$ nor a nonempty completed
macro output. Its completed-history summand is empty. At $j=0$ the
word $G^{s-1}F$ reaches $y_r$ from $C$. At $j=s+1$ the entry is $A_s$,
reached by $G^{s-1}$ from $C$. At each $2\le j\le s$, put $a=s-j$;
(43.14) is exactly $U_j(y_r)$ and its word is $W_a$. Theorem 42.4
excludes every other completed pair at each of these candidates. In
particular $n_0=2$ already forces $t_0=C$: its counts must be $(1,1)$,
and (43.1) permits only this two-leaf ordering. This proves the entire
exhaustion (43.13), not only attainability of its middle rows. All
$j\ge1$ entries there have $s+1$ leaves, so its last row is exhausted,
its first row is unstarted, and exactly its $s-1=r+1$ middle rows are
strictly internal. $\square$

### 43.7 Conditional information bounds under a current-event cap

**Proposition 43.8 (supplement width for the actual filtered fibre).**
Fix $(y,n_0,\phi,Z)$ as after Theorem 43.3 and let $q$ be the cardinality
of its nonempty admissible active-$F$ fibre. A supplementary value
recovers the target exactly if and only if it separates these $q$
possibilities. Its least conditional alphabet has $q$ values and its
least fixed-width binary width is $\lceil\log_2q\rceil$. This reuses
finite-fibre injection, pigeonhole and ranking, rather than asserting a
new coding theorem or a way to acquire the rank from syntax alone.

Under the explicit alpha-origin current-event cap $n(y)\le N$, for
$n_0>1$ one has

$$
q\le n(y)-n_0+1\le N-n_0+1.
\tag{43.16}
$$

An earned exact $j\in\{0,\ldots,N-n_0\}$ gives the matching general
upper bound on conditional width $\lceil\log_2(N-n_0+1)\rceil$.
For $n_0=1$, allow additionally the nonempty-prefix first-macro bit;
$q\le2(n(y)-n_0+1)$ and exact progress plus that bit suffice, leaving
the empty-prefix case separate rather than doubling it.

For the fixed seed $C$, fixed command $F$ and a common strictly internal
between-row phase, let $b_N$ be the maximum of the least conditional
binary widths over attained current sources with $n(y)\le N$, with no
other distinguishing $Z$. For every $N\ge6$,

$$
\left\lceil\log_2\left(\left\lfloor\frac{N-6}{2}\right\rfloor+1\right)\right\rceil
\le b_N\le\lceil\log_2(N-1)\rceil.
\tag{43.17}
$$

Thus the worst-case supplementary width is logarithmic in this stated
current-event cap, up to additive constants, with fixed initial source.

Proof. Equal supplements on distinct members give a decoder identical
inputs but unequal targets. Distinct ranks of the finite recognized
fibre suffice. These are exactly the reused conditional coding arguments.
For every nonempty summand, (43.3) and completed event growth give
$n(y)-j=n(u)\ge n_0$. Hence only $n(y)-n_0+1$ integer progresses are
possible. Theorem 42.4 gives at most one target per progress for
$n_0>1$, or at most two for $n_0=1$ with its single empty-word case.
This proves (43.16), both upper coding statements and their persistence
under filtering. With $r=\lfloor(N-6)/2\rfloor$, Theorem 43.7 supplies
exactly $r+1$ strict-interior alternatives at $y_r$ under the cap.
Their first next marks can be resolved after ordinary list advancement,
so they all admit that same between-row phase. Apply the first part
for the lower bound and (43.16) at $n_0=2$ for the upper. $\square$

These bounds condition on current syntax, exact attachment reference,
phase and every actually supplied $Z$. An actual cursor, saved request,
tapes or other acquired record may already separate the candidates.
There is no compulsory extra counter and no lower bound here on total
physical memory, syntax acquisition, tape storage or whole-run cost.
Without a current-event cap no fixed supplementary alphabet works for
all these finite strict-interior histories. This does not prohibit finite
backing for each particular finite run.

### 43.8 Resource scope and the precise recovery correspondence

**Proposition 43.9 (finite paid descriptions and protocol boundaries).**
With the acquisition/ownership premises of Definition 43.1 and
Proposition 43.5, the inverse and fibre recognizers are finite descriptive
computations. Their availability does not supply physical inverse edits,
a reset, elapsed-time recovery or a fixed storage bound for all histories.
Their source-space interpretation is AA Definition 17.3's oriented
material support or terminal boundary, with auxiliary tape edges excluded.

Proof. Acquire logical syntax by stationary traversal from the authentic
root, testing actual child arity, current grants and reached references;
beta's unary material marker is not another scheduled leaf. AA17.3's
arity representation uniquely distinguishes logical alpha, beta and
binary branch. Finite support determines its terminal antichain and the
antichain determines support by prefix closure. Thus an ACQUIRED complete
source support/boundary determines exactly the $y$ used above. A bare
untyped logical skeleton, a residue pair or a few frontier summaries need
not determine it and are not substituted as inputs.

For a parsed syntax with $V$ logical nodes, each $\delta$, sort test,
count or prefix reconstruction is a finite traversal on at most $V$
nodes. Theorem 43.2 has $K(y)\le n(y)-1$ on $\mathcal D_+$; moreover
$n(y)\le2L(y)-1\le V$. Thus there are at most $V$ candidates. A simple
implementation may retest syntax and counts on every step of Theorem
42.4's at most $n(y)-n_0$ predecessor descents. It then uses at most
$O(V^3)$ logical-node visits to list the full fibre, including at most
two histories per candidate. This is a conservative descriptive bound,
not an optimal algorithm or the runtime of native macro actuation.
On accepted inputs, counters and loop indices are $O(\log(V+1))$-bit
integers; reading supplied integers, binary
arithmetic, address strings and output copying must also be charged.
Explicit old-leaf paths may total $O(V^2)$ symbols for a single tree.
No word, parsed tree, recursive stack or complete answer is costless.

A physical implementation additionally pays actual reference width,
allocation/grants, field reads/writes, root navigation, frontier traversal,
link scans, all ancestor tape appends, exact counter backing/maintenance,
scratch clearing/reuse, and literal input/reply/acknowledgement/return.
These physical costs are not bounded by counting logical nodes alone;
the existing LAB13 and AA20–22 accounts remain applicable. Stationary
acquisition must use the same live source/epoch as the subsequent
projection. For each finite run all required reference, integer,
workspace and output backing is finite and supplied; no fixed finite
arena is asserted for their unbounded union. The inverse operates on
descriptions and never edits the old source back into existence.

Finally, $y$ or its acquired support/boundary together with a separating
coordinate recovers the logical macro chronology, active progress and
remaining logical old-leaf schedule. The same quantities compute the
corresponding descriptive views, giving the stated conditional
space/boundary/history/memory correspondence. Actual callable continuation
still passes through Proposition 43.5's authentic controller and rights.
For original indexed primitive recall, AA19.2 supplies the full-order
tape inverse and AA20 supplies its Ready-only service; macro histories
do not replace those tapes for arbitrary ancestral primitive shuffles.
None of these coordinates is a physical clock. $\square$

**Convention 43.10 (suppliers and mathematical attribution).** The native
ordinal inverse (43.3), its complete join (43.9), the exact family
(43.13) and their conditional consequences are `repo-derived` prose
results. LAB §§9–13 supply the sealed frontier, actual leftmost-beta
split, saved inner continuation, accepted-event maintenance and common
Busy/PairReady protocol. AA §§17,19–23 supply attainment/birth typing,
alpha-origin counting, support/boundary, all-event tapes and lawful recall.
FARG §§2–3 supply ordered syntax and global $\rho$. PG §37.2
(PG.3705) and Theorem 44.6 supply its actual-image parser; the
`substitution_injective` used in GenealogicalFiberTransport is local
inside `result`, not an exported declaration. These source correspondences
are not a new compilation or Lean verification of this section.

[Native Entry Reference §§10.1–10.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ENTRY_REFERENCE_AND_GRAFT_ORDER.md)
already supplies the marked inverse (ER.41)–(ER.43); its §§13–15 also
supply generic actual-fibre enumeration and conditional rank coding on
its own encoded menu. Only the labelled marked parser is reused here.
Its $\rho^2$ runtime, root graft, held anchors and full-controller recovery
do not transfer. Section 42 supplies the completed-history inverse.
This section's new assertion is fixed-progress recognizability across
ALL native unknown entries and the exhaustive join for unfinished calls,
not fixed-known-seed injectivity or a new generic zipper/coding principle.

Engelfriet, [arXiv:1510.02036v1, Definition 3.62](https://arxiv.org/html/1510.02036v1),
defines whole ranked-tree homomorphisms by recursive substitution.
Its linearity condition does not imply native prefix injectivity: the
unrestricted-tree collision following (43.7) uses this very $\rho$.
Huet's [Zipper, §1.1](https://pauillac.inria.fr/~huet/PUBLIC/zip.pdf)
represents a location by its focused tree and surrounding path/context.
That context representation is a supplier, not a proof of (43.3) or a
source of authentic LAB references and rights.
Bennett's [history-retention construction](https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html)
supplies the classical sufficient method for reversible computation,
with retained records and resources; it does not give this native
partial-prefix image or exclude its alternatives. Relative to these
frameworks and the cited repository suppliers, the claimed contribution
is the displayed native correspondence, with no worldwide originality
claim. Theorems concern finite coherent prefixes and their stated
logical projections; the continuing RRO recovery problem remains open.

## 追加锚（本行以下为增补区）

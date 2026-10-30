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

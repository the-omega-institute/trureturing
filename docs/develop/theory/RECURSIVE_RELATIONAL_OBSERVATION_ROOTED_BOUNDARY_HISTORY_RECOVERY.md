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

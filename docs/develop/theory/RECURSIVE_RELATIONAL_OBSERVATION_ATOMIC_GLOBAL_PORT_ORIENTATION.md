# Atomic substitution sources: acquisition of a persistent global port orientation

## 1. Actual source, physical ports and installation

**Definition 1.1 (source and two address alphabets).** Use the free ordered
algebra $\mathcal T$, substitution $\rho$, leaf count $\ell$, four-valued
response $r_t$, and presence $P_t$ of [Atomic Boundary Trichotomy][ABT]
(ABT), Definitions 2.1,33.1. Thus the atomic labels are $\alpha,\beta$,
the constructor is the ordered, nonassociative $\langle s,t\rangle$, and

$$
 \rho\alpha=\beta,\qquad
 \rho\beta=\langle\beta,\alpha\rangle,\qquad
 \rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
 \tag{GPO.1}
$$

These are two labels and one specified substitution, not two universal
operations. Semantic addresses have alphabet $\{L,R\}$. Physical addresses
have two distinguishable names $\{a,b\}$ and the same empty root word.
A realization has one bijection
$\pi:\{a,b\}\longrightarrow\{L,R\}$, extended letterwise to words as
$\pi_*$. It is the same bijection at every branch, including branches
created by later substitutions. Put

$$
 P^\pi_t(w)=P_t(\pi_*w),\qquad
 r^\pi_t(w)=r_t(\pi_*w).
 \tag{GPO.2}
$$

For $1\le A\le B<2A$, the entrance domain is

$$
 \mathcal E_{[A,B]}=
 \{(u,k,\pi,v): A\le n=\ell(u)\le B,\quad k\ge1,
                           \quad v=\rho^{2k}u\}.
 \tag{GPO.3}
$$

Here $u$ is the authentic entrance original, and $2k$ counts its actual
forward substitutions before entrance. The recovery target is
$(\pi,u,k,n)$, not an arbitrary predecessor or a primitive endpoint.
The passive domain $\mathcal E^{\rm pass}_{[A,B]}$ restricts $k\ge2$;
the preparation domain retains every $k\ge1$. The fixed global bijection
is a realization premise; (GPO.1) does not prove its physical persistence.
ABT16.2 leaves root and ordered-reference acquisition separate. Here
the bound root remains supplied, while the interpretation $\pi$ does not.

The ordered algebra and homomorphic extension are the existing
`FreeMagma.of`, `FreeMagma.mul`, `FreeMagma.lift` of Kenny Lau,
`Mathlib/Algebra/Free.lean`, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, instantiated as
`Source = FreeMagma Bool` with substitution and composition in
[GenealogicalFiberTransport][GFT]. Their supplied order is the semantic
order whose physical correspondence is unknown here.

**Assumption 1.2 (installed physical service).** The following specifies
the changes to ABT Assumptions 33.2,38.2 and retains their other duties.

1. There is one actual source register $v$, one bound original root, and
   distinguishable stable physical names $a,b$. Known semantic $L/R$
   references are replaced by the unknown global $\pi$ of Definition 1.1.
   There are neither arbitrary independent local swaps nor an unnamed
   unordered sibling relation. No root or source binding is acquired here.
2. The sole source observation during acquisition is a currently authorized
   total paid absolute-word Read. A request $w\in\{a,b\}^*$ is accepted
   whether or not it reaches a node. A projection delivers exactly
   $P^\pi_v(w)$ to acquisition control. Each invocation, including absence
   and repetition, is paid. Full replies $r^\pi_v(w)$ go only to the writer.
3. The only numerical entrance input is a canonical encoding of authentic
   $(A,B)$, with the relation (GPO.3). Authentication provides no $k,n,u$
   or $\pi$ operand. At fixed advice all other initially accessible fields
   are common across candidates: code, control, physical names, identifiers,
   grant encodings, initial backing contents and observable capacity.
   Padding, allocation identities, completion acknowledgements, errors and
   scheduling choices provide no additional orientation or source channel.
4. The actual append writer records every native localStep, every physical
   Read with its whole word and full reply, and every actual update with
   its old semantic epoch. Acquisition has no writer-read capability,
   no readable pre-entry archive, no epoch field, no timing observation,
   and no direct label or subtree inspection. Its own acquired bits and
   computation counters may be retained. They arise from the paid run.
5. Accessible owned backing supports advice, scratch, literal construction
   and the acquired output. It grows on actual finite requests, without
   initialization or preallocation from unknown parameters. Retention
   includes the right to read the acquired bytes and preserve their source
   binding. Every finite calculation, allocation and paid request used by
   the controller completes. This is variable storage, not bounded memory.
6. During passive acquisition the register is stationary through output
   formation and handoff. There is no concurrent substitution, source swap,
   reroot, clone or reset. The scheduling grant supplies progress of finite
   work, without a bound on physical delay. Reference and port stability
   also hold throughout subsequent lawful use.
7. At continuation the same binding has current rights for absolute Read,
   localStep, applyRho and stop, exactly ABT15's menu. The forward actuator
   substitutes on this same register and realizes (GPO.1), planting new
   children in accordance with the same $\pi$. Its internal wiring does
   not return $\pi$ to the controller. Direct cursor, graft, comparison,
   guard, archive and revocation operations are not supplied.
8. Installation, advice authentication and delivery, root and port
   maintenance, current grants, storage access and retention, scheduling,
   actual source material, preparation and writer services have their own
   prices. A mathematical decoder creates none of these services. The
   passive theorem uses no actuator; Section 5 explicitly changes when
   that actuator may first be used.

In particular every acquired address and stopping decision depends only
on public input, current control and already paid presence bits. A trusted
projection may receive a full reply internally, but exposes only its
presence bit, with no observable branch-dependent auxiliary field.

For comparison, child numbers and ordered child relations are part of
the navigation interface in Engelfriet–Hoogeboom–Samwel,
[*XML Navigation and Transformation by Tree-Walking Automata and
Transducers with Visible and Invisible Pebbles*, arXiv:1809.05730v1][XML],
§2, pp. 7–10. Label and child-number tests, walking and regular
look-around are supplied in Engelfriet–Inaba–Maneth,
[*Linear Bounded Composition of Tree-Walking Tree Transducers: Linear
Size Increase and Complexity*, arXiv:1904.09203v3][TWT], §§2–3.
Those literature-attested interfaces are different assumptions: no
child-number test, pebble, look-around, free walk or source copy is
included here. Centered representations in Berthé–Steiner–Thuswaldner–
Yassawi, [*Recognizability for sequences of morphisms*,
arXiv:1705.00167v2][REC], §2, concern bi-infinite words and word
morphisms, rather than this finite physical-port service.

**Definition 1.3 (simultaneous cost coordinates).** For actual acquisition
requests $w_1,\ldots,w_Q$, let

$$
 M_{\rm addr}=\max_i|w_i|,\qquad W=\sum_i|w_i|.
 \tag{GPO.4}
$$

Each word starts at the root and is submitted literally; shared prefixes
receive no discount. Let $J$ count actual controller localSteps, including
advice arithmetic, projection, address construction, translation, allocation
control, output and attachment. The writer is a separate append service:
its internal writes do not recursively generate new controller localSteps.
For a concrete local-work upper bound choose a fixed multitape bit machine,
with one elementary tape transition charged as one localStep. Input and
counter integers are binary; letters and finite phase tags have constant
width. A node-following Read implementation additionally charges its actual
root access and traversed edges, at most $|w_i|+1$ per invocation. Prices
for arbitrary other backends are their actual work, not this tariff's bound.
The localStep/update/Read event types and chronological concatenation are
those of [NativeSerialMachine][NSM]; the writer is not readable control.

For positive $t$ write $b(t)=1+\lfloor\log_2t\rfloor$. All bit bounds below
exclude capability encodings and record framing when explicitly stated.
The finite local machine description supplies no uniform storage bound.

## 2. A terminal fringe that identifies the global correspondence

**Lemma 2.1 (one side probe after a physical spine).** Let
$v=\rho^{2j}u$ with $j\ge2$ and $u\in\mathcal T$. Define the mathematical
quantity

$$
 h_a=\max\{s\ge0:P^\pi_v(a^s)=1\}.
 \tag{GPO.5}
$$

Then $2\le h_a\le2j+\ell(u)-1$ and

$$
 P^\pi_v(a^{h_a-2}ba)=
 \begin{cases}
 0,&\pi(a)=L,\\
 1,&\pi(a)=R.
 \end{cases}
 \tag{GPO.6}
$$

The test does not require $j$, an original leaf address, a label, or the
semantic interpretation of $a$ as an input.

Proof. Use the existing structural Fibonacci supplier
$T_m=\rho^m\alpha$, $T_0=\alpha,T_1=\beta$,
$T_{m+2}=\langle T_{m+1},T_m\rangle$ from
[Fibonacci Atomic Relation Generation][FARG], Definition 3.1 and Theorem
3.2. Also $\rho^{2j}\beta=T_{2j+1}$. For $m\ge1$, the left-only height
of $T_m$ is $m-1$: it is zero for $T_1$, and each left step from $T_m$,
$m\ge2$, reduces the index by one. Its right-only height is
$\lfloor m/2\rfloor$: a right step reduces the index by two until $T_0$
or $T_1$, both leaves. These statements follow directly by induction
from that supplier, including $T_2=\langle T_1,T_0\rangle$.

Let $d_L,d_R$ be the left-only and right-only heights of $u$, and let
$\eta_L=0$ or $1$ according as its leftmost leaf is alpha or beta.
Substitution preserves every original branch, and at its terminal
original leaf installs $T_{2j}$ or $T_{2j+1}$. Consequently

$$
 h_L(v)=d_L+2j-1+\eta_L,\qquad h_R(v)=d_R+j.
 \tag{GPO.7}
$$

The second identity is also ABT34.2's right-height supplier. Each original
extreme path has at most $\ell(u)-1$ edges, since every branch on it has
a distinct off-path leaf. Thus either physical interpretation gives the
stated bound on $h_a$, and both heights are at least two.

If $\pi(a)=L$, the final two edges of the extreme path lie inside its
terminal leaf replacement: its left height is at least three. At the
ancestor two edges before its terminal leaf the actual subtree is $T_3$.
Indeed, the left descent reduces its index to three there. Since
$T_3=\langle T_2,T_1\rangle$, the semantic word $RL$ is absent at that
ancestor. The physical word $ba$ is exactly $RL$, proving the zero case.

If $\pi(a)=R$, the replacement has right height $j\ge2$, so the same
ancestor again belongs to that replacement, not to the unknown original
context. At this ancestor its subtree is $T_4$ if the original terminal
leaf was alpha, and $T_5$ if it was beta. The final right descents are
$T_4,T_2,T_0$ or $T_5,T_3,T_1$. Both children of each of $T_4,T_5$
are branches, by the recurrence. Hence semantic $LR$ is present there.
Now the physical word $ba$ is $LR$, proving the one case. Every assertion
concerns a subtree of the same actual $v$; none selects or supplies an
unacquired original leaf to the controller. $\square$

**Proposition 2.2 (effective paid orientation).** On Lemma 2.1's domain,
one fixed presence-only controller acquires and retains $\pi$ without
updating $v$. Put $m_a=1+\lfloor\log_2h_a\rfloor$. Its actual calls
and literal costs satisfy

$$
 Q_o=2m_a+1,\qquad M_o\le2h_a,\qquad W_o\le2h_a(2m_a+1).
 \tag{GPO.8}
$$

In particular the additional paid call count is
$O(\log(j+\ell(u)+2))$. This is a protocol upper bound.
The terminal-fringe distinction and its application to the unknown
global correspondence are `repo-derived`; bracketing and binary search
remain the cited intermediate methods.

Proof. Query $a^1,a^2,a^4,\ldots$ until the first absent power, then
binary search between the last present and first absent lengths. Presence
on this path is exactly the initial interval $[0,h_a]$. This is the
ordinary exponential-bracketing and binary-search intermediate method
already used in ABT35.1,40.1; the new use is on a physically named,
semantically unknown direction. There are $m_a+1$ power tests and
$m_a-1$ midpoint tests, since their last bracket has gap $2^{m_a-1}$.
Thus $2m_a$ actual Reads determine $h_a$, with longest word
$2^{m_a}\le2h_a$. Submit the one further literal word
$a^{h_a-2}ba$, of length $h_a$. Its paid bit chooses the two alternatives
in (GPO.6); store that bit as the orientation encoding. The other image
of the bijection is then fixed. Every loop and word construction is a
finite local computation on acquired bits and binary counters. The
supplied progress and backing permit completion. There are zero updates,
and summing the actual word lengths gives (GPO.8). $\square$

## 3. Passive acquisition with the existing actual-original supplier

**Theorem 3.1 (unknown global ports on the whole passive domain).** Under
Assumption 1.2, there is one deterministic effective program, independent
of the unknown parameters, that on every
$(u,k,\pi,v)\in\mathcal E^{\rm pass}_{[A,B]}$ acquires and retains
$(\pi,u,k,n)$ in readable owned backing, keeps the same register equal
to $v$, and supplies its acquired semantic-address adapter to ABT40–42.
Only paid presence bits enter its source-dependent control.

The following bounds apply simultaneously to this one actual run. Write
$j=k$, $h=h_R(v)$, and retain $h_a,m_a$ from Section 2. Put

$$
\begin{aligned}
 m_R&=1+\lfloor\log_2 h\rfloor,&d_B&=\lceil\log_2B\rceil,\\
 q_I&=2m_R+(2B-1)d_B+4n-2,&
 D_I&=\max\{2h,h+B,j+n\},\\
 q&=2m_a+1+q_I,&D&=\max\{2h_a,D_I\}.
\end{aligned}
\tag{GPO.9}
$$

Then

$$
\begin{aligned}
 Q&\le q,&M_{\rm addr}&\le D\le4(j+B),\\
 W&\le2h_a(2m_a+1)+D_Iq_I\le Dq,\\
 J&\le C(q+1)(j+B+1)\Lambda^2,
 &\Lambda&=\lceil\log_2(j+B+2)\rceil,
\end{aligned}
\tag{GPO.10}
$$

for an absolute constant $C$ in Definition 1.3's chosen local tariff.
Additional working storage is $O(j+B+B\Lambda)$ bits, excluding the
retained output, advice, capabilities and writer. The retained target
payload uses at most

$$
 3n+b(k)+b(n)
 \tag{GPO.11}
$$

bits before framing and capabilities. Every Read-service traversal pays
its actual work, at most $W+Q$ root/edge steps for the node-following
implementation. No backend-independent physical-duration bound is claimed.

Proof. Run Proposition 2.2, then keep the acquired bit in control. For a
semantic word $p$, compute the literal physical word
$\tau_\pi(p)=(\pi^{-1})_*p$ by finite letterwise translation. The stored
bit determines each translated letter; no further source query is needed
to compute it. Nevertheless its copying and translation are paid local
work. By (GPO.2), for every semantic word, including one that passes a leaf,

$$
 P^\pi_v(\tau_\pi(p))=P_v(p),\qquad
 |\tau_\pi(p)|=|p|.
 \tag{GPO.12}
$$

Now run the existing ABT40.1 interval controller using precisely this
adapter. The correspondence to ABT38.2 is $u\mapsto u$, original interval
$[A,B]\mapsto[A,B]$, positive even lag $j\mapsto k$, source $v\mapsto v$,
and its semantic $L/R$ references are the newly acquired interpretations
of the retained physical names. Its total paid Read capability is (GPO.12),
on the same stationary register. Its absence, repetition, hidden-writer,
variable-backing and current-rights hypotheses are Assumption 1.2.
All its installation hypotheses therefore hold at this attained cut.

ABT40.2 supplies acquisition of the authentic $(u,k,n)$, termination,
stationarity, and $q_I,D_I$ in (GPO.9). In particular its trial pruning
and strict interval separation are reused results, not new orientation
lemmas: the final source traversal reconstructs labels only after the
acquired lag and order are available. The initial orientation bit is
retained alongside that target. No original tree, exact count or lag is
passed to the code by this proof. Summing the orientation and supplier
costs yields the first two lines of (GPO.10). Lemma 2.1 gives
$2h_a\le4j+2n-2\le4(j+B)$, while ABT40.2 gives $D_I\le2(j+B)$.
Translation changes no submitted length or call count. There are zero
updates in both phases.

The calibrated two-probe table is ABT12.3's semantic-address supplier,
with its erased-support counterpart in [NativeErasedSupportKernels][NES].
The stack traversal is the existing [NativeFullSourceProducer][NFP]
construction, using acquired parent replies to schedule children.

Here is a concrete finite local implementation supporting the remaining
claims, rather than a zero-price selector assumption. Use separate tapes
for binary counters, a current semantic path, a stack of phase frames,
one reusable literal buffer, and the preorder output. A depth-first frame
stores a phase and saved path/output lengths; it never stores an unknown
subtree. The capped ABT comparison has at most $B$ frames, the final
traversal at most $n\le B$. Paths and literals have length at most $D$.
Search brackets are at most $2h_a$ or $2h$, and all branch/leaf counters
are at most $B$ or $n$. Output positions are at most $3n-1$.
Thus each integer field has $O(\Lambda)$ bits, and working storage is
$O(D+B\Lambda)=O(j+B+B\Lambda)$.

Binary addition, subtraction, comparison, doubling and midpoint formation
can be performed by scans of $O(\Lambda)$ cells, with an optional return
scan. No multiplication of unknown parameters is required. Push or pop
one frame by copying its $O(\Lambda)$ cells at the stack head. Construct
each literal by copying the current path and appending the specified
repeated suffix, with a binary loop counter. Even charging
$O(\Lambda^2)$ for every such elementary counter or frame routine, its
cost is $O((D+1)\Lambda^2)$ per request. Letterwise physical translation
and presence projection fit this bound. Path extension or retraction
between successive depth-first nodes, constructor writes and label/count
writes require only a constant number of these routines per visited node.
The comparisons and final traversal visit at most their paid-query counts
of nodes; the final tree has $2n-1$ nodes and already costs $4n-2$ Reads.
There are $O(q+1)$ search, visit, stack, output and attachment routines
in total. Advice validation and binary final parameter copying cost
$O(\Lambda^2)$ as well, since $A\le B$. Increasing the fixed constant
therefore proves the $J$ bound in (GPO.10). This deliberately conservative
tariff counts finite bit work; it is not a best local-work bound.

The retained encoding is ABT41.2's $2n-1$ shape bits, $n$ label bits and
binary $k,n$, plus one orientation bit. This gives (GPO.11). Actual
allocation uses attained lengths, counters and replies; none of these
a posteriori bounds is an instruction to allocate from an unknown input.
The Read traversal bound follows by charging a root access and each
followed edge, stopping at the first failed prefix. $\square$

**Proposition 3.2 (writer, source and advice prices).** In Theorem 3.1,
the new raw writer contains exactly $Q$ physical Read entries and $J$
localStep entries, with all $W$ literal letters and all full replies.
Its semantic Read epochs are $2k$, hidden from acquisition control.
A self-delimiting binary serialization has payload

$$
 O\bigl(J+W+Q\Lambda\bigr)
 \tag{GPO.13}
$$

besides any old prefix, capability and storage metadata. If the original
composition is $(x_0,y_0)$, actual source material has
$x_0F_{2k+1}+y_0F_{2k+2}$ leaves and twice that number minus one nodes.
Retained advice additionally costs $b(A)+b(B)$ bits before framing.
These costs coexist with (GPO.10), rather than being bounded by $Q$ alone.

Proof. The event counts follow from Assumption 1.2's writer and zero
updates. Encode event type with constant overhead, word length and epoch
with self-delimiting binary fields, the literal letters themselves, and
the full constant-width reply. Each length and epoch field costs
$O(\Lambda)$ bits, by (GPO.10); a localStep marker costs constant space.
This proves (GPO.13). The source count is exactly the composition supplier
equation (ABT.35.8), not an acquired size operand. Advice is two positive binary
integers. All old source preparation, authentication, service work,
backing, output copies, retention lifetime and installation prices remain
Assumption 1.2's separate coordinates. In particular small added call
count does not imply small physical source or complete memory. $\square$

**Corollary 3.3 (exact count and magnitude as supplied advice).** Theorem
3.1 also applies with authentic exact original count, using $A=B=n$, or
with authentic magnitude $s=\lfloor\log_2n\rfloor$, using ABT41.1's
paid construction $A=2^s,B=2^{s+1}-1$. On every sharp interval,

$$
 Q=O\bigl(\log(k+n+2)+n\log(n+1)\bigr),\quad
 M_{\rm addr}=O(k+n),\quad
 W=O\bigl((k+n)(\log(k+n+2)+n\log(n+1))\bigr).
 \tag{GPO.14}
$$

Proof. These substitutions satisfy $n\le B<2A\le2n$, so $B<2n$.
Apply Theorem 3.1 and the exact existing advice correspondence of
ABT41.1. Both spine heights are $O(k+n)$, and $d_B=O(\log(n+1))$.
Magnitude-to-interval arithmetic and advice storage are paid as in that
supplier, in addition to the orientation stage. No new claim about
authenticating advice is used. $\square$

## 4. The exact two-substitution passive ambiguity

**Definition 4.1 (reflection and the two image grammars).** On unlabelled
ordered full binary shapes let $\mu(\bullet)=\bullet$ and
$\mu\langle s,t\rangle=\langle\mu t,\mu s\rangle$. On labelled originals
the same reflection fixes both atomic labels. Let

$$
 C=\langle\bullet,\bullet\rangle,\qquad
 D_\beta=\langle C,\bullet\rangle.
 \tag{GPO.15}
$$

The existing exact image grammar of ABT12.1 is
$\mathcal G::=C\mid D_\beta\mid\langle\mathcal G,\mathcal G\rangle$,
with its existing unique decoder to labelled originals. Define
$\mathcal H::=C\mid\langle\mathcal H,\mathcal H\rangle$.
Reflection of a physical word means exchanging all $a,b$ letters, not
exchanging different subsets of branches independently.

**Theorem 4.2 (exact opposite-orientation fibers at $k=1$).** Consider
the entire subdomain of Definition 1.1 with authentic $k=1$, even if this
extra fact and exact $n$ are disclosed. For a fixed complete physical
presence service there are the following possibilities.

* If its actual original $u$ contains a beta leaf, only one global
  orientation is compatible with a $k=1$ realization. The
  original and orientation are effectively recoverable from finite paid
  presence acquisition with this restricted $k=1$ domain known.
* If every leaf of $u$ is alpha, both global orientations are compatible.
  The entire target fiber within this $k=1$ domain consists of
  $(\pi,u,1,n)$ and $(\bar\pi,\mu u,1,n)$, where
  $\bar\pi$ exchanges $\pi(a),\pi(b)$. They are distinct targets because
  their orientation coordinates differ; their original coordinates differ
  exactly when $u\ne\mu u$.

Equivalently, at the shape level the exact overlap is

$$
 \mathcal G\cap\mu(\mathcal G)=\mathcal H.
 \tag{GPO.16}
$$

Proof. Every member of $\mathcal G$ has a branch root. Its three
possible root child types are respectively leaf/leaf, branch/leaf,
and branch/branch. The root types in $\mu(\mathcal G)$ are leaf/leaf,
leaf/branch, and branch/branch. Thus an element in both languages is
either $C$, or a pair whose two children belong to both languages.
Structural induction proves that every such element is in $\mathcal H$.
Conversely $C$ is fixed by $\mu$, and $\mathcal H$ is closed under
pairing and reflection, proving (GPO.16).

In ABT12.1's unique parsing, $C$ decodes to alpha, $D_\beta$ to beta,
and a pair of image trees to the pair of their decoded originals.
Consequently membership in $\mathcal H$ is exactly the absence of beta
leaves in that original. Replacing all-alpha leaves by the symmetric
cherry $C$ commutes with reflection. The opposite-orientation decode
is therefore exactly $\mu u$, with unchanged leaf count $n$. For a fixed
orientation the ABT12.1 inverse is unique. There are just two global
orientations, so the listed fiber is complete. If a beta occurs, (GPO.16)
excludes the opposite orientation, yielding uniqueness.

For effectiveness on the beta-containing restricted domain, acquire the
finite physical unlabelled tree by the existing depth-first stack method.
At a confirmed present node $p$, one paid bit $P^\pi_v(pa)$ tests whether
it is a branch, because the tree is full binary; schedule both children
only on a positive answer. This visits a finite tree and stops on stack
exhaustion, without a supplied size or height. Parse the acquired shape
in the two global orientations using the finite grammar above. Exactly
one parse succeeds, and its already cited decoder gives $u$. These are
paid finite acquisition and local parsing, with the full physical writer
retained. They are not a free complete-shape port or the sparse bound
of Section 2. $\square$

**Corollary 4.3 (same physical presence service, different actual originals).**
No passive controller satisfying Assumption 1.2 can uniformly recover
the joint target on the full $k=1$ subdomain, for any nonempty sharp
interval. In particular the sharp advice $A=B=3$ admits two histories
with exactly the same physical presence service and different ordered
authentic originals.

Proof. For any $n\in[A,B]$ choose an all-alpha original. The two members
of its fiber in Theorem 4.2 already prevent uniform recovery of the
orientation coordinate. To witness different originals take

$$
 u=\langle\langle\alpha,\alpha\rangle,\alpha\rangle,
 \qquad u'=\mu u=\langle\alpha,\langle\alpha,\alpha\rangle\rangle.
 \tag{GPO.17}
$$

Use $k=1$, $\pi(a)=L,\pi(b)=R$ for the first realization and the reversed
bijection for $u'$. The same all-alpha cherry replacement proves that
$P^\pi_{\rho^2u}(w)=P^{\bar\pi}_{\rho^2u'}(w)$ for every physical word.
Both have exact original count three and advice $[3,3]$.

Choose identical accessible bindings, grants, initial control and backing,
with the same admissible allocation and completion behavior. Induction on
accessible transitions shows identical local choices and physical queries,
identical returned presence bits, and hence identical stopping and retained
outputs. They cannot equal both targets. This induction concerns every
passive adaptive controller on this service, not just the proposed protocol.
It is the standard observation-fiber indistinguishability argument used in
ABT39.2 and [Joint Moment Fibers][JM], §§36–39.

The service equated here is the installed presence projection. The hidden
full physical replies need not agree: at a replacement cherry the alpha
and beta labels occupy opposite physical children. The inaccessible raw
writer may therefore differ, even when its epochs agree. Giving that
writer or full labels to control changes the observation contract. The
counterexample does not assert failure for every individual $k=1$ source,
as Theorem 4.2's beta-containing domain shows. It also makes no assertion
against protocols that actually mutate the register. $\square$

## 5. Two paid preparation substitutions on the same source

**Assumption 5.1 (early actuation and changed acquisition cut).** Replace
only Assumption 1.2's restriction on first actuator use by current permission
to execute two completed, serial applyRho calls before any acquisition
Read. Their sole accessible result is the common completion acknowledgement;
there is no source, epoch or orientation reply. All other installation
conditions, authentic entrance original $u$, entrance lag $2k$, advice,
binding and physical names remain as in Definition 1.1. The actuator
preserves the same global $\pi$ on old and new nodes. After these two
actual updates, acquisition is stationary on

$$
 v^+=\rho^2v=\rho^{2(k+1)}u.
 \tag{GPO.18}
$$

No other writer intervenes. The new cut is after preparation, not the
entrance cut. A public phase bit $\varepsilon$ is zero for the passive
mode and one for this two-update mode. It records the controller's two
completed acts, not an unknown source clock. At the acquisition cut put
$j=k+\varepsilon$, so the actual register is $\rho^{2j}u$.
Preparation material and internal actuator work are additional to the
acquisition coordinates of Section 3.

**Theorem 5.2 (all positive entrance lags with paid preparation).** Under
Assumptions 1.2,5.1, every member of $\mathcal E_{[A,B]}$, including every
$k=1$ source, admits actual acquisition and retention of $(\pi,u,k,n)$
after those two updates. It uses no reset, replacement original or clone.
The acquisition costs are (GPO.9)–(GPO.13) with $j=k+1$ and the heights
of $v^+$, and its source updates during that stationary acquisition are
zero. The complete preparation/acquisition interval has exactly two
source updates, $Q$ Reads and $J+J_p$ controller localSteps, where
$J_p=O(1)$ for the fixed two-call phase control. One additional retained
phase bit suffices to distinguish its cut from the passive cut.

Proof. Execute the two permitted calls and wait for their actual serial
completion. By the actuator relation their successive registers are
$\rho v$ and $\rho^2v$, with old update epochs $2k,2k+1$ in the writer.
Neither acknowledgement supplies their unknown numeric values.
Equation (GPO.18) follows from actual composition of these substitutions.
In particular $j=k+1\ge2$, although entrance $k$ remains unchanged.

Theorem 3.1 applies to the new stationary register with authentic original
$u$ and the same interval. Its acquired lag is the lag at that cut,
namely $j$. It returns $u$ and $n$ without changing them to a predecessor
chosen for convenience. Subtract the known one from the acquired $j$ by
paid binary local work to retain the entrance $k$. Include this subtraction
and output copying in $J$; the proof of its bound permits another
$O(\Lambda^2)$ routine. Retain $\varepsilon=1$ so that current offset
$2(k+1)$ is computable from the entrance record. The target payload is
at most $3n+1+b(k)+b(n)$ bits, excluding framing, advice and capabilities.

The two-call phase needs only fixed phase tags; its finitely many controller
transitions give $J_p=O(1)$ independently of source size. This does not
make either global update an elementary material operation: Proposition
5.3 prices them. The raw writer has $Q+J+J_p+2$ new native events, in their
actual order, with no omitted preparation events. Its acquisition Read
epochs are the current $2j=2(k+1)$; its preparation updates retain the
entrance-relative old epochs $2k,2k+1$. The known phase count
has not relabelled the entrance lag, supplied an unknown clock or provided
a history archive. No optimum for preparation count or material work is
claimed. $\square$

**Proposition 5.3 (material, internal work and writer of preparation).**
Let $(x,y)$ be the actual alpha/beta composition of the entrance register
$v$, not an accessible controller operand. An in-place, old-node traversal
implementation of the two substitutions can have the following exact
structural charges. Set

$$
\begin{aligned}
 L_0&=x+y,&L_1&=x+2y,&L_2&=2x+3y,\\
 N_i&=2L_i-1\quad(0\le i\le2),&
 V_p&=N_0+N_1,&G&=\lceil\log_2(N_2+2)\rceil.
\end{aligned}
\tag{GPO.19}
$$

Its substitution traversal processes $V_p$ old nodes, overwrites
$L_0+L_1$ old leaf tags, allocates
and initializes $2y+2(x+y)$ new nodes, and writes that same number of
new child links. The largest live source is $N_2$ nodes. With internal
compact node references of $O(G)$ bits and ordinary explicit access
charges, one finite bit implementation has internal actuator work
$O((N_0+N_1+N_2)N_2G^2)$, source backing $O(N_2G)$ bits, and traversal
scratch $O((H_0+2)G)$ bits, where $H_0$ is the entrance tree height.
None of these is paid by the acquisition Read bound.

Proof. The existing composition law sends $(x,y)$ to $(y,x+y)$ and then
to $(x+y,x+2y)$, giving the three $L_i$ and $N_i$. In one pass visit each
node that existed at the beginning of the pass once. At an old branch
schedule its two old children. At an old alpha leaf overwrite its tag
with beta. At an old beta leaf overwrite its tag with branch, create
two children, and link them in the actuator's fixed semantic order beta,
alpha. Do not visit these new children in the same pass. This is exactly
one simultaneous leaf substitution, not repeated substitution of a newly
created leaf. The first pass has $y$ such births; the second has $x+y$.
Each birth adds two nodes and two child links. This proves every exact
structural count, and

$$
 N_2-N_0=2y+2(x+y).
 \tag{GPO.20}
$$

Existing branches and node identities can be retained in place; the root
binding is not changed and no second callable source is created. Each
pass increases height by at most one, so its depth-first stack needs
$O(H_0+2)$ frames. Choose a private sequential allocator with compact
indices at most $N_2$, never exposed to acquisition control. Each reference
and counter has $O(G)$ bits. Store source records sequentially with
self-delimiting indices and links, growing their widths on actual
allocation rather than presupposing $N_2$. A record access can scan at
most $N_2$ records, comparing their indices by finite binary scans;
even allowing width changes and tape shifts, its work is
$O(N_2G^2)$. These lookup scans are charged in addition to the one
substitution-processing visit per old node. This deliberately simple
implementation uses no random-access oracle. Its source records occupy
$O(N_2G)$ bits. Every processing visit, tag overwrite, allocation, link
write and stack manipulation uses a bounded number of such accesses or
$O(G)$-bit scans. Their total number is $O(N_0+N_1+N_2)$, giving the
work bound. Sequential lookup needs only $O(G)$ temporary bits and does
not copy the source; together with the depth-first stack this gives the
scratch bound. The internal compact representation is the selected
implementation's storage contract; converting a different supplied
representation would incur its additional actual work.

These are internal actuator resources. Its compact identities, scratch,
allocation behavior and runtime are not acquisition observations, as
required by Assumption 1.2. New links realize the installed $\pi$;
their creation does not prove that installation premise. Source material
and access are charged even though applyRho is one native event.
The native writer separately appends exactly two update entries, with
old epochs $2k,2k+1$, and the $J_p$ controller markers. Their payload is
$O(J_p+\log(k+2))$ before framing. It does not record one extra native
event for every actuator-internal bit transition; that work has the
separate coordinate just priced. Combining this prefix with Section 3's
writer gives $O(J+J_p+W+(Q+2)\Lambda)$ new payload bits. All actual
service metadata and any retained discarded internal storage are additional.
If entrance $u$ has composition $(x_0,y_0)$, then the supplied recurrence
gives $x=x_0F_{2k-1}+y_0F_{2k}$ and
$y=x_0F_{2k}+y_0F_{2k+1}$. Thus these material charges can grow far
beyond the sparse orientation query count. $\square$

## 6. Incidence, terminal boundary, substitution count and usable memory

**Definition 6.1 (four observations of the attained process).** Fix authentic
advice and mode $\varepsilon\in\{0,1\}$. The positive domains are passive
$k\ge2$ when $\varepsilon=0$, and all entrance $k\ge1$ after the actual
preparation when $\varepsilon=1$. At their successful acquisition cut let
$v_\varepsilon=\rho^{2(k+\varepsilon)}u$, $j=k+\varepsilon$, and define:

* $S$ is the actual rooted physical incidence, represented by the finite
  prefix-closed set $\{w:P^\pi_{v_\varepsilon}(w)=1\}$. Its edges retain
  physical names $a,b$, but no leaf labels or semantic orientation bit.
* $\partial$ is the actual physical terminal-address antichain: those
  $w\in S$ with neither $wa$ nor $wb$ in $S$. It has no leaf labels.
* $T=2j$ is the number of actual substitutions from the authentic original
  to this cut. The entrance count is $T_{\rm ent}=T-2\varepsilon=2k$.
  Neither observation includes duration, labels, shape, acquired queries
  or a writer archive. This mathematical count is not an acquisition input.
* $\mathsf M$ consists of the acquired readable record
  $(\pi,u,k,n,\varepsilon)$ with its retained backing, same root binding
  and current continuation grants. Its data payload is denoted $R$.
  Scratch and the inaccessible raw writer are separate resources.

These definitions observe incidence, terminals, actual substitution count
and callable retained information directly; they are not definitions by
desired inverse functions. They refine the independently defined views
of ABT42.1 by distinguishing physical from acquired semantic directions
and by making the preparation cut explicit.

**Theorem 6.2 (recovery-route agreement on the declared domains).** With
the installed common references, advice and mode of Definition 6.1,
each of $S$ and $\partial$ determines the same target
$(\pi,u,k,n)$ as the actually acquired $R$. Their recovery routes agree.
The data in $R$ recovers these very $S,\partial,T,T_{\rm ent}$.
These are data inverses on the attained domains; creation of backing,
binding and grants is still Assumption 1.2's duty. The actual procedure
produces usable $\mathsf M$ with the Section 3 and Section 5 prices.

Proof. Every node of a finite tree extends to a terminal node, so prefix
closure of $\partial$ is precisely $S$, and its maximal words return
precisely $\partial$. This is ABT42.2's finite-tree intermediate fact,
now applied to physical words. Membership in this $S$ supplies exactly
the mathematical bit answers used by Proposition 2.2. Lemma 2.1 therefore
recovers the unique $\pi$ on either positive domain, where the current
lag is $j\ge2$. Translating by that recovered bijection supplies the
semantic incidence required by ABT40.2, at the same authentic original
and interval. Its mathematical decoder returns $(u,j,n)$. Subtracting
the known $\varepsilon$ returns the entrance $k$. Theorems 3.1,5.2 show
that the actual paid acquisition makes exactly these inferences. Hence
both routes return the same $R$ data, not independently chosen marginals.

Conversely $R$ computes $j=k+\varepsilon$ and the finite ordered tree
$\rho^{2j}u$. Relabel its addresses by $\tau_\pi$ to obtain the actual
physical incidence $S$ and terminal set $\partial$, and compute $T=2j$
and $T_{\rm ent}=2k$. Substitution and the letter map are precisely the
realization relations, so these recovered sets equal the originals.
The two compositions are identities on their attained data. Constructing
an expanded copy as local data has its actual computation and storage
price; it is not required for sparse acquisition, a source reset or a
free additional physical register. Neither prefix closure nor a data
inverse manufactures authority. Usable retention is supplied by the
actual writes into owned backing and surviving grants in the proved
run. $\square$

**Proposition 6.3 (time-only failure and task equivalence).** Even with
authentic exact $n$, interval, mode and known $\pi$, the count $T$ does
not determine the original or its complete logical Read/ApplyRho behavior.
For originals viewed through that logical menu at epoch zero, equality
of all finite source-free observations is exactly equality of $u$.
No minimal complete-memory or optimal orientation-cost assertion follows.

Proof. Fix any $n\in[A,B]$, an $n$-leaf ordered shape, one allowed $k$
and one orientation. Give its leaves all-alpha labels in one realization
and all-beta labels in the other. Both have the same $n$, advice, mode
and $T=2(k+\varepsilon)$, but different originals. A Read at any one
original leaf address distinguishes their logical replies. More generally
different ordered labelled finite trees have different four-valued
responses at some semantic address: descend through equal branch roots
until the first unequal node type or leaf label. The one-Read-and-stop
logical program at that literal address distinguishes them. Equal originals
give equal future trees under each logical substitution and equal replies
at each request. Induction on an adaptive source-free controller's finite
steps then gives equal logical observations. Thus the behavioral equivalence
is exactly tree equality. Orientation and lag are additional acquisition
and realization coordinates; this argument does not prove their necessity
in every memory encoding or for each restricted consumer. $\square$

**Theorem 6.4 (retained orientation used on the same changing register).**
At either successful cut, let an effective source-free logical native
program in ABT15's menu have initial control computed from public task
input and the retained $R$. It has a lawful presence-macro continuation
on this same register, binding and acquired physical adapter. At each
completed macro boundary after $e$ logical updates,

$$
 r_e=\rho^e u,\qquad
 \widehat r_e=\rho^{N}r_e=\rho^{2j+e}u,\qquad
 N=2j=2(k+\varepsilon),\qquad \widehat e=2j+e.
 \tag{GPO.21}
$$

Completed logical replies, including absence, lawful continuation choices
and entire terminal outputs agree with that logical program. The acquired
orientation remains callable after each update. All attained finite logical
fragments have finite compiled executions, and logical termination implies
compiled termination. No arbitrary logical program is asserted to terminate.

Proof. Compute and store $N=2(k+\varepsilon)$ by paid local arithmetic
from $R$, and attach the consumer by a real localStep. At the cut the
actual acquired tuple and actual source relation are exactly ABT42.3's
initial relation with fixed offset $N$, and the current ordered Read
service is (GPO.12). Apply its existing ABT15 presence macros, translating
every generated semantic word by the retained $\tau_\pi$.

For a logical localStep only control changes. A logical Read runs its
finite presence macro on $\widehat r_e$ and invokes its continuation
only when all required paid bits have been obtained. ABT13.2,15.3 and
[DelayedOriginalReadout][DOR]'s presence guard give
the exact original four-valued reply, including absence and odd absolute
physical epochs. Translation preserves each bit by (GPO.2). A logical
update invokes one actual actuator operation; its persistent global
wiring gives the semantic successor $\rho\widehat r_e$ on this very
register. The identity
$\rho\rho^N r_e=\rho^N\rho r_e$ preserves (GPO.21) without recalibrating
$N$ or changing $\pi$. A stop returns the same output. Induction on
finite logical fragments, including ABT15's pending-macro invariant,
proves all the claims. Cutting after a first macro bit retains its paid
request, phase and bit; resumption does not repeat or erase that event.

At a continued fragment with actual costs $Q_c,W_c,M_c,U_c,J_c$, the
joint preparation/acquisition/continuation run pays

$$
 Q+Q_c,\quad W+W_c,\quad
 \max(M_{\rm addr},M_c),\quad 2\varepsilon+U_c,\quad
 J+J_p+J_c,
 \tag{GPO.22}
$$

where $J_p=0$ in passive mode, and $J_c$ includes consumer, macro,
translation, output and evaluator local work. ABT15.4's exact completed-
macro call and letter formulas apply with $k$ there replaced by $j$;
physical letter translation preserves them. Update material/internal work,
retention and continuation storage remain separate charges. In particular
the two preparatory updates are not two logical consumer updates, and
the authentic entrance original and lag are never changed to make this
application fit. $\square$

**Proposition 6.5 (raw-writer distinction and retained scope).** The
continuation in Theorem 6.4 preserves the declared logical task, not raw
writer identity or direct cursor-action domains. The unknown-global-port
result has no implication for arbitrary local swaps, an unbound root,
untrusted advice, lost backing, revoked rights, unknown earlier histories,
or physical duration.

Proof. The raw writer has the actual concatenation
$H_{\rm old}H_{\rm prep}H_{\rm orient}H_{\rm interval}H_{\rm cont}$,
with empty $H_{\rm prep}$ only in passive mode. It contains the real
orientation calls, interval calls, local work and optional two updates.
A logical program consisting of one Read then stop has only its one
logical Read; the physical writer already contains these additional
acquisition entries. Even its continuation Read can expand to several
physical entries, as ABT15.6's explicit example shows. No causal logical
interpretation deletes those physical events or exposes their hidden
contents to acquisition. Likewise a logical leaf can have physical children
after expansion, so a direct DownL action has a different success domain;
this is the unchanged ABT15.6 cursor counterexample.

Globality is used at the exact call $a^{h_a-2}ba$ and at every translated
word in (GPO.12). If local assignments vary independently, its letters
need not follow a semantic extreme path, and the lemma's premise is absent.
For an actual collision in that different model take any unequal sources
$s,t$, originals $\langle s,t\rangle$ and $\langle t,s\rangle$, and the
same $k\ge2$. Reverse only the semantic assignment at the root in the
second realization, using the same assignments within corresponding
subtrees. Since substitution preserves an original branch, the complete
physical labelled trees can be identical, while those ordered originals
differ. This does not satisfy the single-global-$\pi$ premise.

All the other listed services are explicit hypotheses rather than source
consequences. The same-current-tree/different-history and arbitrary-parity
ambiguities of ABT9,37.2,39.2 remain in their original domains. Existing
fixed-apparatus, cursor, graft, guarded and joint-contact tasks keep their
own initialization, response, current-right and cost obligations. No
atomic-to-continuous, affine or quantum correspondence is assumed here.
Thus neither the proved data inverses nor the lawful native continuation
is an unrestricted four-expression inverse or a physical realization of
the larger relational-observation programme. $\square$

[ABT]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md
[FARG]: FIBONACCI_ATOMIC_RELATION_GENERATION.md
[JM]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[GFT]: ../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[DOR]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[NES]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.lean
[NFP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean
[NSM]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean
[XML]: https://arxiv.org/abs/1809.05730v1
[TWT]: https://arxiv.org/abs/1904.09203v3
[REC]: https://arxiv.org/abs/1705.00167v2

## 追加锚（本行以下为增补区）

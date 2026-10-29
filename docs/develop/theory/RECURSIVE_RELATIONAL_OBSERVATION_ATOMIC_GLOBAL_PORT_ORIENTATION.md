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

## 7. A first-completion Read grant and the odd acquisition cut

**Assumption 7.1 (the one-completion service variant).** Keep Definition
1.1 and all the source, advice, observation, common-initialization,
backing, writer, progress and continuation conditions of Assumption 1.2.
The entrance register is still the authentic
$v=\rho^{2k}u$, with $k\ge1$ and $A\le n=\ell(u)\le B<2A$;
the target is still $(\pi,u,k,n)$. The following is an additional
installation condition, replacing the two-call acquisition schedule of
Assumption 5.1 for this variant only. The actor may execute one completed
applyRho on this same register and then obtain stationary paid total Read
at that first completion, before issuing another update. Its only accessible
actuator result is the common completion acknowledgement. The register
remains stationary through acquisition, output formation and handoff, and
the same global $\pi$ applies to every old and newly created branch.
Thus the attained register is

$$
 x=\rho v=\rho^{2k+1}u.                         \tag{GPO.23}
$$

The preparation count $d=1$ is known from the actor's completed act;
$2k+1$ is not supplied as a numeric epoch. All preparation, installation,
Read, maintenance, allocation, retained access and writer costs are paid.
No completion timing, allocation pattern, identity or hidden full reply
provides an extra source channel. Stationarity forbids interleaving even
a second preparation update with these Reads.

This first-completion Read grant is a premise about the installed service.
A service that mandates two completed calls before granting Read, as allowed
by Assumption 5.1, need not have it. Neither that assumption nor Theorem
5.2 installs the present variant. The source algebra and authentic entrance
history are unchanged; the availability cut is different. The two-call
result and all its charges remain valid in their original scope.

**Lemma 7.2 (orientation at an odd cut, including the shortest fringe).**
For every $u\in\mathcal T$, $k\ge1$ and global $\pi$, let
$x=\rho^{2k+1}u$ and
$h_a=\max\{s:P_x^\pi(a^s)=1\}$. Then
$1\le h_a\le2k+n$. If $h_a=1$, then $\pi(a)=R$. If $h_a\ge2$, then

$$
 P_x^\pi(a^{h_a-2}ba)=
 \begin{cases}0,&\pi(a)=L,\\1,&\pi(a)=R.\end{cases}
                                                        \tag{GPO.24}
$$

Consequently the exponential bracketing and binary search of Proposition
2.2, followed by this test only when $h_a\ge2$, acquires $\pi$ using
exactly $2m_a+\mathbf1_{h_a\ge2}$ Reads, where
$m_a=1+\lfloor\log_2h_a\rfloor$. Its maximum literal length is at most
$2h_a$ and its total literal length is at most $2h_a(2m_a+1)$.

Proof. Write $d_L,d_R$ for the original extreme-path lengths and
$\eta_L,\eta_R\in\{0,1\}$ for the beta indicators of their terminal
leaves. The existing recurrence for $T_i=\rho^i\alpha$ gives left height
$i-1$ for $i\ge1$ and right height $\lfloor i/2\rfloor$. Preserving
original branches therefore gives

$$
 h_L(x)=d_L+2k+\eta_L,\qquad
 h_R(x)=d_R+k+\eta_R.                            \tag{GPO.25}
$$

Since $d_L,d_R\le n-1$, these imply the bounds and exclude $\pi(a)=L$
when $h_a=1$. If $a$ means left, the terminal leaf replacement has left
height at least two. Two edges before the end of that left path its
subtree is exactly $T_3=\langle T_2,T_1\rangle$; the semantic suffix
$RL$ is absent there. This proves the zero case.

If $a$ means right and its terminal replacement has right height at least
two, the ancestor two edges before the end is $T_4$ or $T_5$. Both its
children are branches, so semantic $LR$ is present. The remaining case
has right height one inside the replacement. It is necessarily $k=1$
and an original alpha leaf, with replacement $T_3$. If the whole height
is one, the first rule already applies. Otherwise the ancestor two edges
before the end is the original parent of that terminal original leaf.
Its left child is $\rho^3t$ for an actual nonempty original sibling $t$.
Every $\rho^3t$ has a branch root, so $LR$ from that parent is present.
This proves (GPO.24) also when its testing ancestor is outside the terminal
replacement. No original leaf address is supplied to the actor.

Presence on $a^s$ is the initial interval $0\le s\le h_a$. The existing
bracketing calculation uses $m_a+1$ power tests and $m_a-1$ midpoint
tests, all literal words of length at most $2h_a$. The optional final
word has length $h_a$. The stated simultaneous bounds follow. All
choices depend only on already paid bits and finite binary arithmetic;
the installation's backing and progress make these actual terminating
calculations. $\square$

## 8. Odd-cut pruning and authentic lag acquisition

**Lemma 8.1 (odd-offset node table and newborn exclusion).** Fix arbitrary
$t\in\mathcal T$, $k\ge1$, and $y=\rho^{2k+1}t$. At every semantic
address $p$ put

$$
 B_k^o(p)=pR^kL,\qquad C_k^o(p)=pR^kLL,
 \qquad b=P_y(B_k^o(p)),\quad c=P_y(C_k^o(p)).       \tag{GPO.26}
$$

At a present original node their pairs are respectively $00,10,11$ for
alpha, beta and branch. If $p$ was originally absent, both bits are zero,
even if $p$ is now present. In particular, on all addresses without a
presence promise,

$$
 P_y(pR^kLL)=1\quad\Longleftrightarrow\quad
                  r_t(p)=\mathsf{branch}.          \tag{GPO.27}
$$

Proof. The recurrence $T_{i+2}=\langle T_{i+1},T_i\rangle$ gives, for
all $i,s\ge0$,

$$
 P_{T_i}(R^sL)=1\iff i\ge2s+2,\qquad
 P_{T_i}(R^sLL)=1\iff i\ge2s+3.                   \tag{GPO.28}
$$

For $s=0$, an $L$ child exists exactly at ranks at least two, and an
$LL$ descendant exactly at ranks at least three. A further initial $R$
requires a branch and lowers rank by two; induction on $s$ proves both
criteria, with ranks zero and one failing at the first edge. These are
applications of the guarded atomic navigation supplier of Atomic Block
Conjugacy, Theorem 3.2; nonnegative final rank alone is not being used
as a reachability condition.

At an original alpha or beta leaf the current subtree is $T_{2k+1}$ or
$T_{2k+2}$. Equation (GPO.28) gives $00$ or $10$. At an original branch,
the right child is $\rho^{2k+1}s$ for a nonempty original $s$. Follow
$R^{k-1}$ there. Each original branch encountered preserves both children;
after reaching an original leaf the remaining atomic rank is at least
three, since at most $k-1$ atomic right edges have removed two each.
Thus two further left edges are possible. If all $k-1$ right edges instead
end at an original branch, its left child is an odd substituted nonempty
tree and has a branch root, so the same two left edges are possible.
This proves $P_{\rho^{2k+1}s}(R^{k-1}LL)=1$ in every case. Hence $c=1$,
and its prefix probe has $b=1$.

For original absence, take the first original leaf prefix $z$ of $p$ and
write $p=zw$ with $w\ne\varepsilon$. This is the original-leaf
factorization in ActualLeafHistoryRigidity.actual_address_geometry.
The corresponding replacement is $T_{2k+1+\eta}$, $\eta\in\{0,1\}$.
If $w$ fails, both probes fail. If it succeeds, each of its edges starts
at a branch and lowers rank by one or two. Its reached rank is therefore
at most $2k+1$. Formula (GPO.28) makes $R^kL$, and consequently $R^kLL$,
absent. The argument includes all later-born addresses and proves
(GPO.27). $\square$

**Definition 8.2 (odd trial pruning).** For a finite actual tree $y$ and
$j\ge1$, form $F_j^o(y)$ from the root: a reached node $p$ is a branch
exactly when $P_y(pR^jLL)=1$; only on that answer schedule its two
children. Otherwise record a terminal dot. Let $a_j^o(y)=\ell(F_j^o(y))$.
A positive test implies an actual branch at $p$, so every scheduled node
exists. Recursion descends proper actual subtrees and terminates. This
is a paid test-defined pruning, with no guessed labels or inverse-image
promise at an incorrect trial $j$.

**Theorem 8.3 (odd clock and the sharp-interval crossing).** For all
$k\ge1$, $u\in\mathcal T$, $n=\ell(u)$ and $x=\rho^{2k+1}u$, set
$H=k+h_R(u)$. Then for every integer $s\ge1$,

$$
 P_x(R^{s-1}LL)=1\iff s\le H,
 \qquad k\le H\le k+n-1.                        \tag{GPO.29}
$$

For $1\le j\le k$,

$$
 F_j^o(x)=\operatorname{sh}(\rho^{2(k-j)}u),
 \qquad a_j^o(x)\ge2^{k-j}n.                     \tag{GPO.30}
$$

For $j\ge k$, $F_j^o(x)$ is a pruning of $\operatorname{sh}(u)$.
Consequently, whenever $n\le B<2n$,

$$
 a_j^o(x)\le B\iff j\ge k\quad(j\ge1),
 \qquad k=\min\{j\ge1:a_j^o(x)\le B\}.          \tag{GPO.31}
$$

Proof. Let $d=h_R(u)$, with rightmost original leaf label indicator
$\eta$. At an original proper prefix $R^j$, $j<d$, the left child is
an odd substituted nonempty tree and is a branch, so $R^jLL$ is present.
For $j\ge d$, the suffix $R^{j-d}LL$ is evaluated inside
$T_{2k+1+\eta}$. By (GPO.28) it is present exactly when
$2k+1+\eta\ge2(j-d)+3$, equivalently $j<d+k$, for either value of
$\eta$. This also covers suffixes that fail before their end. Taking
$j=s-1$ gives (GPO.29); the original right path has at most $n-1$ edges.
The clock here is this threshold $H$, not the right height of $x$,
which by (GPO.25) can instead be $H+1$.

For $j\le k$, write $w=\rho^{2(k-j)}u$. The actual equality
$x=\rho^{2j+1}w$ lets Lemma 8.1 identify each pruning branch exactly
with a branch of $w$. Starting at its root and recursing only at those
branches proves the first equality in (GPO.30). The reused two-step
composition inequality $\ell(\rho^2w)\ge2\ell(w)$, from ABT39.1,
proves its lower bound.

For $j\ge k$, every original leaf has zero branch test by (GPO.28).
Starting at the original root, the traversal can therefore only retain
original branches or stop earlier: it never descends below an original
leaf. It is a pruning of the original shape and has at most $n$ leaves.
For $j<k$, (GPO.30) has at least $2n>B$ leaves; at $j=k$ it has exactly
$n$. These prove (GPO.31), including $n=1$. The proof does not assume
monotonicity of $P_y(pR^jLL)$ on arbitrary full binary trees: that would
be false without the substituted-source conditions. $\square$

**Proposition 8.4 (actual cap comparison).** Given $B\ge1$, $j\ge1$
and a finite nonempty actual $y$, left-before-right traversal of $F_j^o(y)$
can decide whether $a_j^o(y)>B$ with at most $2B-1$ paid Reads, each
of length at most $j+B+1$. It uses no acquired full shape.

Proof. Use exactly ABT34.3's branch-cap traversal, with its probe replaced
by $pR^jLL$. Count positive tests and stop at the $B$th, reporting greater;
if the pending stack is exhausted first, report at most. A full binary
tree has one more leaf than branch, so both answers are correct. Before
a query, pending-slot count $1+b-l>0$ implies $l\le b$, where $b,l$
are previous positive and negative tests. Thus the $B$th positive has
at most $B-1$ preceding zeros; a completed smaller traversal also has at
most $2B-1$ nodes. Each queried $p$ has at most $B-1$ discovered branch
ancestors, so $|pR^jLL|\le j+B+1$. A positive test implies a real branch,
which justifies scheduling its children. These are actual requests and
finite stack computations, not evaluation of an unknown pruning in control.
$\square$

## 9. One actual update followed by sparse internal acquisition

**Definition 9.1 (the single acquisition program).** Check the supplied
advice $1\le A\le B<2A$ by paid finite arithmetic, then execute and wait
for the one preparation update in Assumption 7.1. On its stationary $x$:

1. Acquire $\pi$ by Lemma 7.2 and retain its bit. Thereafter translate
   each computed semantic word by the acquired letter map $\tau_\pi$.
2. Query $R^{s-1}LL$ for $s=1,2,4,\ldots$ through the first absence,
   and binary search the last bracket to acquire the threshold $H$ of
   (GPO.29). Every word is translated and submitted literally from the
   bound physical root. The first bit is one on the promised domain.
3. Initialize $l=\max(1,H-B+1)$, $z=H$. While $l<z$, choose
   $j=\lfloor(l+z)/2\rfloor$ and use Proposition 8.4. Its greater answer
   sets $l=j+1$, and its at-most answer sets $z=j$. At the singleton
   retain $K=l$.
4. Traverse from the confirmed original root. At each $p$ execute both
   probes (GPO.26), with $k=K$, in the displayed order. Their pairs
   $00,10,11$ construct an alpha leaf, beta leaf or branch. Schedule
   children only in the branch case. Count acquired leaves, producing
   $\widehat n$, and assemble the acquired ordered tree $U$ in owned
   backing. Retain $R_o=(\pi,U,K,\widehat n,d=1)$ with readable backing,
   the same source binding and the current continuation grants.

Malformed advice or impossible bit combinations may give a fixed error;
none occurs on the promised domain. The acquired tree is data built from
paid bits. No call receives $u,k,n$, an original leaf address, an unknown
pruning, a full response, or an unacquired full physical shape as an operand.

**Theorem 9.2 (complete-domain acquisition and simultaneous prices).**
For every $1\le A\le B<2A$ and every entrance realization in
$\mathcal E_{[A,B]}$, under Assumption 7.1 the program of Definition 9.1
terminates, retains exactly $R_o=(\pi,u,k,n,1)$ and leaves this same actual
register equal to $x=\rho^{2k+1}u$. Its acquisition uses no further update.
Let $h_a$ be as in Lemma 7.2 and put

$$
\begin{aligned}
 m_H&=1+\lfloor\log_2H\rfloor,&d_B&=\lceil\log_2B\rceil,\\
 q_I^o&=2m_H+(2B-1)d_B+4n-2,&
 D_I^o&=\max\{2H+1,H+B+1,k+n+1\},\\
 q_o&=2m_a+1+q_I^o,&D_o&=\max\{2h_a,D_I^o\},\\
 \Lambda&=\lceil\log_2(k+B+3)\rceil.
\end{aligned}                                                   \tag{GPO.32}
$$

Write $E_a,E_p$ for the actual extra controller bit transitions needed
to access or copy service encodings and maintain their grant-bearing
bindings during acquisition and preparation, beyond the tape routines
specified below; let $S_E$ be their peak additional scratch. These are
paid finite coordinates under Assumption 7.1, without an assumed uniform
bound in $k,n$. They exclude the Read backend, actuator internals and
writer's private work, which have their own coordinates. In particular
retaining an opaque service handle is not assumed to be a free operation.

In Definition 1.3's fixed bit-machine tariff the same run satisfies

$$
\begin{aligned}
 Q&\le q_o,&M_{\rm addr}&\le D_o\le4(k+B+1),\\
 W&\le2h_a(2m_a+1)+D_I^oq_I^o\le D_oq_o,\\
 J&\le C(q_o+1)(k+B+1)\Lambda^2+E_a.&&
\end{aligned}                                                   \tag{GPO.33}
$$

Here $J$ includes all acquisition controller arithmetic, projection,
translation, allocation control, output and handoff. One fixed preparation
phase adds $J_p\le C+E_p$ localSteps, and the joint interval has exactly
one update, $Q$ Reads and $J+J_p$ localSteps. Additional acquisition scratch
is $O(k+B+B\Lambda)+S_E$ bits, excluding retained target, advice,
capabilities and writer. The retained target including its orientation
and preparation bits occupies at most $3n+1+b(k)+b(n)$ bits before framing. In particular,
on every sharp interval the simultaneous protocol bounds are

$$
\begin{aligned}
 Q&=O(\log(k+n+2)+n\log(n+1)),\\
 M_{\rm addr}&=O(k+n),\\
 W&=O((k+n)(\log(k+n+2)+n\log(n+1))).
\end{aligned}                                                   \tag{GPO.34}
$$

Proof. Lemma 7.2 acquires the actual global bijection from this one $x$.
Thus every later translated word has exactly its semantic presence bit
and unchanged length, by (GPO.12). The threshold tests in (GPO.29) are
one exactly for $s\le H$. Exponential search uses $m_H+1$ tests and
binary refinement $m_H-1$, with longest literal $2^{m_H}+1\le2H+1$.
Both phases terminate without a supplied height or lag.

Since $H-k=h_R(u)\le n-1\le B-1$, the next interval contains $k$ and
has at most $B$ integers. Authentic sharp advice gives $n\le B<2n$.
Theorem 8.3 therefore makes every cap answer at most equivalent to
$j\ge k$. Each interval update retains $k$ and at least halves its
size up to a ceiling, so at most $d_B$ comparisons leave exactly $K=k$.
Each comparison pays its at most $2B-1$ Reads; its trial $j\le H$
gives maximum word length $H+B+1$. No inverse is invoked at an incorrect
trial.

At $K=k$, Lemma 8.1 identifies every reached original node. The root
exists; a decoded branch confirms its two original children. Structural
induction therefore gives $U=u$ with acquired count $\widehat n=n$.
The acquired-stack traversal of NativeFullSourceProducer supplies the
stack/switch/combine method; the probes replace its full-reply read at
each node. It visits exactly $2n-1$ nodes, makes exactly $4n-2$ Reads,
and its words have length at most $k+n+1$. Repeated addresses in these
phases are actual repeated calls and are included. The register never
changes during any acquisition phase. Supplied finite-work progress and
backing imply termination through the final retained write and handoff.

Summing these actual phases proves the first two lines of (GPO.33).
The bounds $h_a\le2k+n$, $H\le k+n-1$ and $n\le B$ prove its displayed
bound for $D_o$. A concrete implementation uses the same tapes as Theorem
3.1: binary counters, shared current path, phase/length stack frames, one
reusable literal buffer, and growing preorder output. A capped comparison
has at most $B$ frames and the final traversal at most $n$ frames.
Paths and buffers have length $O(k+B)$; all counters, brackets, saved
lengths and output positions have $O(\Lambda)$ bits. Hence the scratch
bound holds. At most $O(q_o+1)$ search/visit/stack/output routines are
needed: a cap visit has one paid query and a final node visit has two.
Copying or extending a literal, translating its letters and binary-loop
control cost $O((k+B+1)\Lambda^2)$ per routine by ordinary tape scans.
Counter arithmetic, output construction, forming $2K+1$, and the
payload part of handoff fit the same bound. Work on service encodings
contributes $E_a$, with its extra scratch $S_E$; preparation control has
a fixed phase transition in addition to its $E_p$. This proves the stated
conservative estimates, with one constant for the fixed tape code
independent of every unknown source parameter. Allocations
follow actual counters and acquired lengths, rather than these unknown
upper bounds.

There are $2n-1$ preorder shape bits, $n$ label bits, $b(k)+b(n)$ numeric
bits, one orientation bit and one preparation bit. This proves the payload
bound; the binding, grants and framing are additional. Finally
$n\le B<2A\le2n$ gives $B<2n$, so (GPO.34) follows from (GPO.32).
Neither a call optimum nor a total-price optimum is asserted. $\square$

**Proposition 9.3 (the one-pass material and writer charges).** Let
$(x_0,y_0)$ be the actual entrance-register composition, inaccessible to
acquisition control. Set

$$
 L_0=x_0+y_0,\quad L_1=x_0+2y_0,\quad
 N_i=2L_i-1,\quad G=\lceil\log_2(N_1+2)\rceil.       \tag{GPO.35}
$$

The old-node implementation in Proposition 5.3, stopped after one pass,
processes exactly $N_0$ old nodes, overwrites $L_0$ old leaf tags, creates
$2y_0$ new nodes and writes $2y_0$ new child links. Its peak live source
is $N_1$ nodes. In that proposition's compact sequential representation,
internal actuator work is $O((N_0+N_1)N_1G^2)$, source backing is
$O(N_1G)$ bits, and traversal scratch is $O((H_0+1)G)$ bits for entrance
height $H_0$. The actor's sparse costs (GPO.33) do not pay these charges.

The new native writer has exactly $Q+J+J_p+1$ entries. It contains the
one actual update at old epoch $2k$, all acquisition Reads at epoch
$2k+1$ with their full physical replies and literal words, and every
controller localStep. A self-delimiting binary payload costs
$O(J+J_p+W+(Q+1)\Lambda)$ bits besides old prefix, framing/capability
and storage-service metadata. For the root/edge-following Read backend,
its additional traversals cost at most $W+Q$ root/edge steps.

Proof. Reuse the one-pass part of Proposition 5.3's implementation: visit
only nodes present at the beginning of the pass. An old alpha tag becomes
beta; an old beta tag becomes branch and receives the ordered new beta,
alpha children. Newly allocated children are not visited in this pass.
The composition changes to $(y_0,x_0+y_0)$, proving all exact structural
counts and $N_1-N_0=2y_0$. The root and old branch identities persist.
The source grows by actual allocation, using private compact indices,
not an accessible size operand or an exposed timing channel.

There are $O(N_0+N_1)$ processing, tag, allocation, link and stack
operations. As in Proposition 5.3, each can use a sequential lookup or
width-change scan of $O(N_1G^2)$ bit work; records occupy $O(N_1G)$
bits and stack depth at most $H_0+1$. This proves the representation-
specific bounds without a random-access oracle or a second callable source.
Actuator-internal transitions are this separate work coordinate, not new
native controller events. Another supplied source representation incurs
its own access or conversion price.

The native event counts follow directly from the installed append writer.
All word lengths and the update/Read epochs have $O(\Lambda)$-bit
encodings; a localStep marker has constant payload. Literal letters cost
$W$, giving the writer bound. Each Read starts at the root and follows at
most its submitted length in edges, giving $W+Q$. If authentic $u$ has
composition $(a_0,b_0)$, entrance material has
$a_0F_{2k+1}+b_0F_{2k+2}$ leaves, as in ABT35.3. Its earlier preparation
price remains before this interval, not zero. Advice uses additionally
$b(A)+b(B)$ bits; authentication, installation, retained lifetime,
source/service maintenance and output copying retain their actual prices.
$\square$

## 10. The sharp preparation coordinate and its service boundary

**Theorem 10.1 (uniform worst-case additional preparation is one).**
Fix any nonempty sharp authentic interval $1\le A\le B<2A$ and the
first-completion service of Assumption 7.1. Among deterministic effective
protocols recovering the entire authentic target $(\pi,u,k,n)$ on the
whole $\mathcal E_{[A,B]}$, the least possible worst-case number of
additional source substitutions is exactly one. The lower bound holds
even if all stationary entrance Reads are permitted, and even if exact
$k=1$ and exact $n$ are disclosed on the obstructing subdomain.
This is a preparation-count minimum, with no total-price dominance claim.

Proof. Theorem 9.2 supplies the uniform one-update protocol with all
simultaneous charges. A protocol with worst-case zero updates is passive.
For any $n\in[A,B]$, choose an all-alpha original of that leaf count.
The two authentic $k=1$ targets $(\pi,u,1,n)$ and
$(\bar\pi,\mu u,1,n)$ have the identical complete physical presence
service by Theorem 4.2; their orientation coordinates differ. All other
accessible initial fields and completion/allocation behavior may be
chosen identical, as in Corollary 4.3. Induction on paid Reads and local
steps gives the same acquired bits, choices and output in both cases,
so one output cannot be both targets. This reuses the passive obstruction
rather than purporting to extend it to mutating protocols. It excludes
worst-case zero and proves the minimum. $\square$

**Corollary 10.2 (supplier-relative passive and strict-grant statements).**
On the whole passive $k\ge2$ domain of Theorem 3.1, zero preparation
suffices and is minimal. On the separately known $k=1$ domain containing
a beta leaf, Theorem 4.2 already gives finite zero-update acquisition;
on its all-alpha opposite-orientation fibers passive uniform acquisition
fails. For the full positive-even entrance domain, Assumption 5.1 alone
still supplies the two-update upper bound of Theorem 5.2. If a service
forbids acquisition Read until two completed preparations and provides
no other accessible source observation before that barrier, its uniform
worst-case count within that strict service is exactly two.

Proof. The first two sufficiency assertions are direct reuse of their
stated suppliers; nonnegative preparation counts make zero minimal.
The all-alpha failure is their unchanged two-target fiber. In the strict
service, before two completions the only available source-action result
is the common acknowledgement. A terminating protocol that always used
at most one update would therefore have identical accessible executions
on two different entrance targets, chosen with the same advice and
initial fields. It cannot be uniformly correct. The existing two-update
protocol attains the bound. The conditional count two in that different
service does not establish that Read is physically unavailable after one
completion in any particular installation. $\square$

One can have a cheaper additional-update coordinate and still a more
expensive complete run. For example the one-update protocol's longer odd
probes need not have the same Read/backend/local prices as a two-update
protocol; maintaining a first-completion grant may itself cost more.
Propositions 5.3 and 9.3 expose material prices, but no weights or backend
comparisons turn their separate coordinates into a universal total order.
No query, memory, actuator-work or physical-duration optimum is inferred
from Theorem 10.1.

## 11. Total presence continuation at a retained odd offset

**Theorem 11.1 (all-address odd-offset Read macro).** Fix $k\ge1$, any
logical current tree $t\in\mathcal T$, and actual register
$y=\rho^{2k+1}t$. For a nonroot address $p=ad$, $d\in\{L,R\}$, set

$$
 G_k^o(p)=aR^kLL.                                  \tag{GPO.36}
$$

In addition to (GPO.26), this is a total paid presence query. Its bit
$g$ is one exactly when $p$ was present in $t$. The complete actual table
is

| Logical reply $r_t(p)$ | $g$ for nonroot $p$ | $b$ | $c$ |
| --- | --- | --- | --- |
| absent | $0$ | $0$ | $0$ |
| alpha | $1$ | $0$ | $0$ |
| beta | $1$ | $1$ | $0$ |
| branch | $1$ | $1$ | $1$ |

The following adaptive macro returns precisely $r_t(p)$ without updating
$y$: first Read $B_k^o(p)$; if $b=1$, Read $C_k^o(p)$ and return beta
or branch according as $c=0$ or $1$. If $b=0$ at the root, return alpha.
If $b=0$ at a nonroot, Read $G_k^o(p)$ and return absent or alpha
according as $g=0$ or $1$. Only paid presence bits enter this control.
For $D_p=|p|+k+1$ its exact path costs are

| Logical request/reply | $Q_p$ | $W_p$ | $M_p$ |
| --- | --- | --- | --- |
| root alpha | $1$ | $D_p$ | $D_p$ |
| beta or branch, any $p$ | $2$ | $2D_p+1$ | $D_p+1$ |
| nonroot alpha or absent | $2$ | $2D_p$ | $D_p$ |

These are this macro's prices, without an odd-offset optimality assertion.

Proof. By (GPO.27) at the arbitrary parent $a$, $g=1$ exactly when
$r_t(a)=\mathsf{branch}$. In a full binary tree that is equivalent to
presence of either child $ad$, including when $a$ itself was absent.
This proves the guard. Lemma 8.1 gives all the other entries, explicitly
including absence at a now-born address. If $b=1$, absence and alpha
are excluded and $c$ distinguishes the two remaining replies. If $b=0$,
only alpha or absence remains; the nonempty root excludes absence and
the guard handles every nonroot. Lengths of $B_k^o,C_k^o,G_k^o$ are
respectively $D_p,D_p+1,D_p$, proving the table by summing the actual
calls. Malformed formal bit patterns can have a fixed absent default;
they do not occur on this domain. $\square$

For example take $k=1,t=\alpha,p=L$. The actual $T_3$ has a node at
$L$, but $B_k^o(p)=LRL$ is absent and
$G_k^o(p)=RLL$ is absent. The macro returns the original absence, rather
than the current presence of that new node. This example illustrates the
proved all-source guard, rather than substituting a finite check for it.

**Theorem 11.2 (retained same-register continuation and cuts).** At
Theorem 9.2's cut, let a supplied effective source-free logical native
program have menu localStep, absolute four-valued Read, applyRho and
stop, and initial control computed from its public task input and the
retained $R_o$. Its instruction and continuation calculations have an
actual finite-code evaluator. Then it has a presence-only compiled use
on this same actual register and the retained adapter. At every completed
macro boundary after $e$ logical updates,

$$
 r_e=\rho^eu,\qquad \widehat r_e=\rho^Nr_e=\rho^{2k+1+e}u,
 \qquad N=2k+1\text{ fixed},\qquad \widehat e=N+e.   \tag{GPO.37}
$$

Every completed logical reply, continuation choice and entire terminal
output agrees with the logical program. Every attained finite logical
fragment whose evaluator work is finite has a finite compiled execution;
logical termination with finite evaluator work implies compiled termination.
No arbitrary program is asserted to terminate. The converse at completed
boundaries also holds: a compiled execution produces only the corresponding
logical instructions, replies and successors.

Proof. Compute and retain $N=2K+1$ by paid local work and attach the
consumer by an actual localStep. Definition 9.1 has acquired $K=k$ and
its same-source relation; no unknown calibration operand remains. Use the
Ready/NeedC/NeedG phase construction of ABT15.1, replacing its even macros
by Theorem 11.1 and translating each literal by $\tau_\pi$. Ready stores
the original effective control. NeedC stores the pending $(p,f)$ and
actually obtained $b=1$; NeedG stores nonroot $(p,f)$ and actually obtained
$b=0$. The continuation $f$ is retained effective control data, not an
oracle. Its evaluator state and all intermediate word/counter work are
also retained when a cut occurs.

A logical localStep changes only control. For Read, Theorem 11.1 applies
to $t=r_e$ and this fixed $N$, returns exactly $r_{r_e}(p)$ and only
then evaluates $f$ on that reply. All macro Reads use the same stationary
$\widehat r_e$. A logical update performs exactly one actual applyRho;
the installed persistent orientation and
$\rho\rho^Nr_e=\rho^N\rho r_e$ prove the next boundary relation. The
old physical update epoch is $N+e$ and the old logical epoch is $e$;
the former is a hidden writer field, not an input to control. Stop returns
the very same complete output and adds no native Event. Induction on
logical steps proves the assertions. Conversely every completed macro
has just the indicated decoded reply, no other control branch; the other
three instructions have their stated single successor/output. This proves
the completed-boundary converse by induction as well.

For a cut after the first Read of a two-call macro, the original logical
Read has not completed, the original continuation has not run, and the
same logical tree/register relation still holds. Store its acquired bit,
phase and request. Resume with its one remaining Read, rather than
repeating the first one. Cuts within finite evaluator work retain that
work's current machine configuration. A cut at Ready can attach any
source-free continuation with the declared input/control contract.

More explicitly, process the actual physical trace online from the retained
initial consumer state. Emit the original localStep and logical old-epoch
update at their corresponding instructions, emit one logical Read only on
macro completion, and emit no logical event for declared evaluator
microsteps. Maintain the pending state just described. If $s_1$ is the
state after a true fragment $h_1$, this causal interpretation satisfies

$$
 \Pi_o(s,h_1h_2)=\Pi_o(s,h_1)\,\Pi_o(s_1,h_2).     \tag{GPO.38}
$$

This follows directly by sequential processing, including a pending cut;
it needs neither future events nor the hidden source. The actual writer
still appends every event in $h_1h_2$. Thus the connection and output
claims preserve all relevant successors and do not identify raw and
logical logs. Crucially the offset stays $N=2k+1$ even when the absolute
physical epoch $N+e$ is even. Neither a new even-lag acquisition nor a
substitution of $(N+e)/2$ for the retained $k$ is performed. $\square$

**Proposition 11.3 (continued resources on the same run).** For a completed
finite logical continuation from the acquisition handoff let $R$ count
its Reads, let $A_0$ count its root-alpha
replies, let $R_+$ count its beta-or-branch replies, and let its addresses
be $p_i$ with $D_i=|p_i|+k+1$. The compiler just proved has exact costs

$$
 Q_c=2R-A_0,\qquad
 W_c=2\sum_{i=1}^R D_i+R_+-(k+1)A_0,
 \qquad U_c=U,                                    \tag{GPO.39}
$$

where $U$ counts logical updates. Each beta/branch macro has maximum
$D_i+1$, each other macro maximum $D_i$; an empty fragment has maximum
zero. Every local instruction/evaluator transition, literal construction,
translation, pending-state write, retained read, output and allocation is
paid. On the bit-machine tariff the macro word/counter work can be bounded
by

$$
 C\sum_{i=1}^R(D_i+2)\lceil\log_2(k+|p_i|+4)\rceil^2,            \tag{GPO.40}
$$

in addition to actual consumer/selector/continuation evaluation, closure
storage/copying, attachment and its original localSteps. These additional
costs and their actual workspace need not have a uniform bound.

Proof. Sum Theorem 11.1's path table. Every root-alpha macro removes one
length-$k+1$ call from the baseline two length-$D_i$ calls; every beta or
branch adds one letter. Each logical update executes exactly once.
For (GPO.40), copy the supplied finite path, append the right suffix and
one or two left letters using binary loops, translate and project, and
store the finite phase tag and acquired bit. The same tape construction
as Theorem 9.2 costs $O((D_i+2)\log^2(k+|p_i|+4))$ per macro. Reading
and copying any larger effective continuation closure or consumer state
is accounted separately by its actual evaluator, rather than hidden in
this address-dependent bound. A reusable literal buffer has peak length
at most the maximum displayed $D_i+1$; a pending cut also retains $p_i$,
its effective continuation and any in-progress evaluator workspace.

If $J_c$ is the actual total continuation localStep count, including all
these tasks, the full preparation/acquisition/continuation run pays

$$
 Q+Q_c,\quad W+W_c,\quad
 \max(M_{\rm addr},M_c),\quad 1+U,\quad J+J_p+J_c. \tag{GPO.41}
$$

Cuts inside a macro instead count its already executed calls/words, with
pending work retained; concatenation adds actual expenditures without
refunds. The raw writer is exactly
$H_{\rm old}H_{\rm prep}H_{\rm acq}H_{\rm cont}$, with one preparation
update and every physical macro reply. For a finite fragment its epoch
fields are bounded by $N+U$; its new continuation payload can be
$O(J_c+W_c+(Q_c+U)\log_2(N+U+M_c+2))$ bits before framing and service
metadata. Apply the one-pass material accounting of Proposition 9.3 at
each actual continuation update, with that update's actual composition
and height. All retained lifetime, source material, backing, extra output
and service charges coexist with (GPO.41). $\square$

## 12. Recovery routes, task meaning and source boundaries

**Definition 12.1 (independent observations at the one-update cut).**
Fix authentic $(A,B)$ and the known preparation mode $d=1$. On the
attained actual $x=\rho^{2k+1}u$ define:

* $S_o=\{w\in\{a,b\}^*:P_x^\pi(w)=1\}$, with its rooted physical
  $a/b$ incidence, observes discrete space without leaf labels or a
  supplied semantic orientation.
* $\partial_o$ is the actual antichain of terminal physical addresses in
  $S_o$, without labels. It observes the terminal boundary.
* $T_o=2k+1$ counts actual substitutions from the authentic original to
  this cut, and $T_{\rm ent}=T_o-1=2k$ counts them at entrance. Neither
  count includes shape, labels, duration, queries or a readable archive.
* $\mathsf M_o$ is the acquired readable record $R_o=(\pi,u,k,n,1)$
  together with its actual accessible backing, same-root binding and
  current continuation grants. Its acquired payload, scratch, inaccessible
  raw writer and physical source are separate resources.

These are direct observations of one common actual process. In particular
$\mathsf M_o$ is not a definition that places the complete history inside
each view, and $T_o$ is a count rather than an installed clock port.

**Theorem 12.2 (attained recovery, agreement and continued use).** Under
Assumption 7.1, $(A,B,S_o)$ and $(A,B,\partial_o)$ each determine the
same authentic $(\pi,u,k,n)$ retained by Theorem 9.2. Conversely the
payload of $\mathsf M_o$ determines these very $S_o,\partial_o,T_o$
and $T_{\rm ent}$. Both routes and both compositions agree on their
attained data domains. The actual paid procedure creates usable retained
$\mathsf M_o$ under the supplied services and supports Theorem 11.2's
same-register actions. No inverse from incidence data alone creates backing,
binding, progress or rights.

Proof. Every node of a finite tree extends to a terminal node. Thus prefix
closure sends $\partial_o$ to exactly $S_o$, and taking its maximal words
recovers exactly $\partial_o$. Applying Lemma 7.2 to the membership bits
of this same $S_o$ gives its unique semantic correspondence. Thereafter
Theorems 8.3 and 9.2 decode its original and authentic entrance lag using
the same sharp interval. Consequently both routes return the same target,
not independent choices of source realizations. The actual acquisition
makes precisely those inferences with paid bits and retained writes.

Conversely the acquired payload computes the finite tree $\rho^{2k+1}u$
and translates its addresses using its very $\pi$. This is exactly the
actual $x$ by (GPO.23), giving the same physical incidence, terminals and
counts. On attained data the two compositions therefore return the initial
data. Expanded reconstruction, if requested as local output, has its own
finite computation/storage price; sparse acquisition does not build an
expanded physical copy. The actual backing and surviving grants make the
acquired payload callable, and (GPO.37) proves the compatibility of its
continued actions with the same source's true successor. At a later cut,
use the retained $N$ and actual logical update count $e$ as in that relation;
this theorem does not assert that the initial odd-cut decoder can be
reapplied to the unrecorded absolute epoch. $\square$

**Proposition 12.3 (time-only failure and the exact logical task).** Even
with exact $n$, advice and known $\pi$, $T_o$ alone does not determine
$u$ or its complete logical Read/applyRho behavior. For common source-free
logical control and initialization, the equivalence of originals under
all finite logical Read/applyRho/stop tests is exactly equality of $u$.
The present target contains additional realization coordinates; this does
not prove a minimal complete-memory encoding for every consumer.

Proof. Choose any $n\in[A,B]$ and an $n$-leaf ordered shape. Its all-alpha
and all-beta labellings at the same $k$ and orientation have equal counts,
advice and $T_o$, but a logical Read at any original leaf address has
different replies. More generally distinct finite ordered labelled trees
have different four-valued replies at some literal address: descend through
common branch roots until the first unequal node type or label. One Read
and stop at that address distinguishes them. Equal originals have equal
successor trees under every logical update and equal replies at every
request; induction on the common logical controller gives equal choices
and outputs. This proves exactly the stated task equivalence. The target's
$k$ and $\pi$ also specify the authentic entrance and physical adapter;
no lower bound here makes each such field necessary for every restricted
consumer or every alternative memory representation. $\square$

**Convention 12.4 (suppliers, new content and remaining bridges).** The
additional mathematical content is the first-completion conditional
one-update upper bound, the all-odd-cut fringe including its short-spine
case, the odd threshold/pruning acquisition on the authentic whole interval,
and its total presence-only odd-offset continuation. The sharp preparation
count combines that upper bound with the existing passive obstruction.
These are source-specific `repo-derived` deductions, not literature-priority
or Lean-certification claims. Their source correspondences are:

| Supplier | Exact use and boundary |
| --- | --- |
| FARG Definitions 2.1,3.1, Theorems 3.2,3.4; GenealogicalFiberTransport and its owning Scribe | The same free ordered source, pair-distributing substitution, Fibonacci atomic children and composition growth. True labels alpha, false labels beta. The substitution injectivity proof's `no_alpha` helper does not acquire an unknown lag or orientation. |
| [Atomic Block Conjugacy](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md), Definition 3.1 and Theorem 3.2; ActualLeafHistoryRigidity.actual_address_geometry and its owning Scribe, including the proof-local `absent` helper | Guarded rank decrements along existing edges, and the exact factorization of an absent address as a strict extension of an original leaf. The latter clause is for arbitrary finite native trees, without a positive-image premise. Only these navigation clauses are used in Lemma 8.1. |
| ABT12–15,33–43; this volume §§1–6 | Existing even image parsing, passive indistinguishability, cap traversal, interval separation method, paid stack and macro/pending-cut architecture. Here $u,A,B,k,\pi$ keep their authentic meanings; the new actual register has offset $2k+1$, so the old even node table is not silently applied there. Theorem 5.2 is reused as two-update sufficiency, not re-presented as a preparation optimum. |
| DelayedOriginalReadout, including private `clock_step`, `clock_at_step`, `label_clock_decode`, `guard_clock` and public clock/guard/decoder theorems, with its owning Scribe | The right clock and all-parity full-reply supplier. At an odd offset its guard distinguishes alpha from beta/branch replies; the present observer receives only presence. Lemmas 8.1 and Theorem 11.1 supply the missing support-level odd guard rather than importing those hidden label distinctions. |
| NativeErasedSupportKernels and its owning Scribe, including `root_reflection`, `erased_reply_presence` and `erased_support`; ActualFibonacciSupportChain and its owning Scribe | Exact even erased/presence kernels and actual strict support chains. They retain their stated even epochs and label/absence distinctions. Their existing rank and support facts are intermediate suppliers, without a new class-level lower bound being inferred from an API search or finite example. |
| NativeFullSourceProducer, including `traverse`, `production_reads`, `stationary`, and its owning Scribe; NativeSerialMachine and its owning Scribe | Source-blind acquired-stack assembly, one actual register, full physical chronology and effective pending-state reasoning. Native Op.read accepts a complete Reply; every physical continuation here is explicitly composed with presence before acquisition/macro control. |
| DelayedTemplateCertificate and its owning Scribe; NativeUniformTree and its private navigation helpers | Known-template full-label certificates and finite-code evaluation retain their original inputs. No known template, complete Reply, zero-cost selector or free unknown tree is supplied by this contribution. |
| Kenny Lau, pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Mathlib/Algebra/Free.lean, `FreeMagma.of`, `mul`, `liftAux`, `lift` | The supplied nonassociative ordered algebra and homomorphic extension. It supplies neither source access nor physical ordered-port installation. |

For the relevant primary comparison, Engelfriet–Inaba–Maneth,
[*Linear Bounded Composition of Tree-Walking Tree Transducers: Linear
Size Increase and Complexity*, arXiv:1904.09203v3][TWT], §§2–3, defines
ranked trees with child numbers, configurations and rules testing input
labels/child numbers, moves up/down/stay and optional regular look-around.
Those are literature-attested navigation/transduction interfaces; this
observer has total paid absolute words with only presence and no walking,
look-around, hidden label test or source copy. Its linear-bounded
composition theorem does not instantiate the present acquisition contract.
The word-morphism recognizability comparison in Assumption 1.2 likewise
retains its bi-infinite word domain. Exponential bracketing, binary search,
finite prefix closure and stepwise simulation are reused intermediate
methods, not independently new results. This is a bounded source comparison,
without an exhaustive literature or global novelty assertion.

Only the single global-port relation is handled. Independent local swaps,
unbound roots, untrusted advice, lost backing, revoked grants, concurrent
updates, arbitrary earlier histories and physical duration keep their
separate obligations. Without the sharp advice, ABT39.2's same-current-tree
history collisions persist after any common number of forward updates;
without positive-even entrance provenance, ABT9's parity ambiguity is not
removed by adding the same one to both histories. The one-completion grant
has not been installed or deduced from a mandatory two-call barrier.
The logical menu excludes direct cursor, graft and guarded operations;
the raw-writer and cursor counterexamples of ABT15.6 are unchanged.

The two labels and specified substitution are not a universal two-generator
foundation, and discrete incidence is not a physical metric or a diffusion
law. In particular the signed phase-source steering action in
[FIB Native Long-Time Phase Steering Action](https://github.com/the-omega-institute/trureturing/blob/c2579220ab0412d6d3c5b418563dd0502200f9e4/docs/develop/theory/FIB_NATIVE_LONG_TIME_PHASE_STEERING_ACTION.md),
§§74–78, and the full-test constant-diffusion obstruction in
[FIB Native Central-Noise Green Stability](https://github.com/the-omega-institute/trureturing/blob/c2579220ab0412d6d3c5b418563dd0502200f9e4/docs/develop/theory/FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md),
§§9–11, concern their own continuous sources, clocks and services. No map
between those sources and this ordered tree process is assumed. The
original fixed-apparatus, original-Q, parked-consumer and unchanged-
initialization problems, and the NCR/PVC/PR57/PG/Atlas suppliers, retain
their original targets and open acquisition/action bridges. This unit
advances the conditional acquisition-to-retained-use route; it does not
supply unrestricted four-way recovery or complete the larger programme.

## 追加锚（本行以下为增补区）

## 13. A fixed scaffold with jointly unknown labels and authentic lag

**Definition 13.1 (the actual finite comparison family).** Retain exactly
Definition 1.1's free ordered source, substitution (GPO.1), physical
alphabet, stable bound root and persistent global bijection $\pi$.
Fix a finite nonempty ordered full binary scaffold $S$ whose $n\ge1$
leaves, in left-to-right order, have addresses $p_1,\ldots,p_n$.
Every leaf is a slot; there are no additional constant leaves. Put

$$
 d_i=|p_i|,\qquad \delta=\min_i d_i,\qquad
 h=\max_i d_i,\qquad L=\sum_{i=1}^n d_i.
 \tag{GPO.42}
$$

For $x\in\{0,1\}^n$, let $u_x=S[x_1,\ldots,x_n]$, with $0$
meaning alpha and $1$ beta. For every integer $K\ge1$ the family is

$$
 \mathcal F(S,K)=
 \{(x,k,v):x\in\{0,1\}^n,\quad K\le k\le2K-1,
                       \quad v=\rho^{2k}u_x\}.
 \tag{GPO.43}
$$

Each member is one authentic original, its actual positive even entrance
lag and its one actual entrance register. The required output is precisely
$(u_x,k)$, rather than some predecessor, current endpoint, or value of a
smaller logical task. The scaffold fixes original occurrences, not a
shared-subtree quotient. Distinct label vectors give distinct originals
in the free algebra. Thus (GPO.43) has $K2^n$ different required outputs.
For $n=1$ the scaffold is a single slot, its address is empty and
$\delta=h=L=0$.

**Assumption 13.2 (stronger comparison access and complete control).**
In this comparison interface the true unlabelled ordered scaffold $S$,
the true $\pi$ and the authentic lag bin $[K,2K-1]$ are common public
inputs. Immediately at entrance there are current rights for total paid
presence Read, arbitrary serial forward applyRho on this same register,
localStep and stop. Between completed actions there is no concurrent
update. A Read itself observes a stationary register. All other conditions
of Assumption 1.2 are retained: the root and physical names remain stable,
updates preserve $\pi$, and the full append writer is inaccessible to
control. In particular its old-epoch fields, full four-valued replies,
pre-entry prefix and internal work are not observations.

At fixed $S,K,\pi$, every other initially accessible field is common
across all $K2^n$ members. This includes program selection, control,
identifiers, grants, backing contents, readable capacities, prior outputs,
reply latches and allocation metadata. All later accessible source-bearing
state must be obtained from the actually paid presence bits and common
inputs. Errors, acknowledgement contents, schedules, resource identities,
allocation choices, runtime and source size supply no further channel.
Local calculations, evaluator transitions, construction and submission of
literal words, backing growth, retention, output and handoff are real
paid operations. Owned growing storage and completion of each finite
legal calculation/request are supplied, without a uniform space or time
bound. Update material, private actuator work, writer work, installation,
authentication, reference maintenance and current-right maintenance also
retain their actual separate prices.

A competitor is any common deterministic effective protocol terminating
with the correct pair on every member of (GPO.43). It may perform any
finite number of forward updates, adaptively between Reads, and any
finite local work on each member. There is no uniform update allowance,
no requirement of a fixed update schedule and no ban on odd intermediate
epochs. The finite family and sourcewise termination imply an a posteriori
finite maximum run length for this particular competitor and these public
inputs; that maximum is neither an input nor a stopping oracle. No reset,
clone, inverse substitution, reroot, cursor, graft, hidden-source comparison
or writer read is available.

The three optimized coordinates are Definition 1.3's $Q,W,M_{\rm addr}$,
with maximum zero if there is no Read. Every call, including repetition
and absence, is charged. Each semantic word is translated by the public
$\tau_\pi$ and submitted as an entire physical root word of the same
length; there is no shared-prefix, cached-receipt or free-focus discount.
Actual arithmetic and memory costs are not omitted merely because this
optimization projects onto these three coordinates.

The public grants in this assumption are a lower-bound relaxation of
original acquisition: the controller has more information and earlier
access. They are not a service installed by a theorem. The encoded scaffold,
port bit and bin have their own acquisition, authentication, encoding,
storage and access costs. They reveal neither $x$ nor $k$ within (GPO.43).
For example a preorder scaffold has $2n-1$ branch/slot bits; its usable
physical binding and authenticity are additional to that data. A fixed
encoding of the bin may store $K$ and compute its endpoint by paid binary
work. None of these costs is claimed bounded by a query count alone.

## 14. Preserved original cones and common-prefix blind radii

**Lemma 14.1 (actual register and one-cone replies).** For every
competitor of Assumption 13.2, fix any reached prefix $H$ of paid presence
replies, just before its next Read. There are a common finite extra-update
count $e_H\ge0$ and a common next literal word. For every member compatible
with that prefix, its actual register at that Read is

$$
 \rho^{2k+e_H}u_x
       =S[(T_{2k+e_H+x_i})_{i=1}^n],\qquad T_j=\rho^j\alpha.
 \tag{GPO.44}
$$

A semantic word that ends at a proper internal scaffold node has constant
presence one. Every other word has a unique original-leaf prefix $p_i$;
its answer depends only on $k,x_i,e_H$ and its suffix after $p_i$.
It cannot inspect two original cones. This includes a suffix that fails
inside its replacement and an empty suffix at its root.

Proof. Source-free deterministic control, common initialization and the
absence of auxiliary source channels imply that equal reply prefixes give
equal controller states, local steps, update requests and next words.
This is induction through the actual actions, including real acknowledgements,
allocations and finite evaluator work. A compatible terminating run witnesses
that the segment to the next Read is finite. The segment is identical for
all compatible members; no computation of a termination bound is needed.
Only its extra-update count $e_H$ is common: the hidden absolute epochs
$2k+e_H$ need not agree and are not fed into this induction.

Substitution distributes over pairing and preserves every pre-existing
branch and its two child positions. Structural induction on $S$, followed
by induction on the number of actual updates, gives (GPO.44), using
$\rho^m\beta=T_{m+1}$. The finite scaffold's leaf addresses are
prefix-incomparable. To classify any word, follow it in $S$. Either it
ends at an internal node or it first reaches exactly one leaf. Full
binarity leaves no missing scaffold child before that first leaf. In
the latter case write the word uniquely as $p_iq$ and evaluate $q$ in
the displayed $T_{2k+e_H+x_i}$. All scaffold branches have persisted,
so that evaluation is the actual answer on this same register. $\square$

**Lemma 14.2 (uniform present suffixes and the two stationary probes).**
For every integer $a\ge0$, every rank $j\ge2a$ and every word $q$ with
$|q|\le a$, $P_{T_j}(q)=1$. Consequently at the prefix in Lemma 14.1,
all suffixes of length at most $k+\lfloor e_H/2\rfloor$ are present
in both possible replacements for each fixed $k$ and original leaf.
Any query that branches among compatible members of the entire bin has
length at least $\delta+K+1$.

At the stationary entrance, for every original leaf $p_i$ and every
integer $s\ge0$,

$$
 \begin{aligned}
 P_{\rho^{2k}u_x}(p_iR^s)&=1\quad\Longleftrightarrow\quad s\le k,\\
 P_{\rho^{2k}u_x}(p_iR^{k-1}LL)&=x_i.
 \end{aligned}
 \tag{GPO.45}
$$

Proof. Use the existing recurrence
$T_0=\alpha,T_1=\beta,T_{j+2}=\langle T_{j+1},T_j\rangle$.
The general present-suffix fact is the `short` argument inside
ActualFibonacciSupportChain, recalled explicitly here for its shared-prefix
application. The empty word is present at every rank. If $q=Lq'$ or
$Rq'$ has positive length and $j\ge2|q|$, then $j\ge2$ and the
respective child has rank $j-1$ or $j-2$, each at least $2|q'|$.
Induction on the word length proves the fact. For the two replacements
the smaller rank is $2k+e_H\ge2(k+\lfloor e_H/2\rfloor)$.

A branching query must enter a cone, by Lemma 14.1. If its suffix had
length at most $K+\lfloor e_H/2\rfloor$, the same present-suffix
fact would make its answer one for every compatible $k\ge K$ and
both labels. Thus its suffix is longer, giving in particular length
at least $d_i+K+1\ge\delta+K+1$. This statement is about presence;
the full replies at these addresses can differ and remain hidden.

For (GPO.45), the right-spine height of $T_j$ is $\lfloor j/2\rfloor$:
a right edge is available at rank at least two and reduces rank by two,
ending at rank zero or one. Both ranks $2k,2k+1$ therefore have right
height $k$. Following $k-1$ right edges in those two trees reaches
$T_2$ or $T_3$. In $T_2=\langle\beta,\alpha\rangle$ the suffix
$LL$ is absent; in $T_3=\langle T_2,\beta\rangle$ it is present.
Preserved original cones prove (GPO.45), including $k=1$ with no right
edges before $LL$. This is exactly the leaf specialization of ABT12.3's
existing even node table; it does not supply a free label observation.
$\square$

## 15. Sourcewise prices and one simultaneous worst realization

**Theorem 15.1 (every-run lower bounds despite adaptive updates).**
For every $S,K$ of Definition 13.1, every competitor of Assumption 13.2
and every one of its actual runs on $(x,k)\in\mathcal F(S,K)$,

$$
 Q\ge n,\qquad M_{\rm addr}\ge h+k+1,\qquad
 W\ge L+n(k+1).
 \tag{GPO.46}
$$

Proof. Fix this complete actual run and an original leaf index $i$.
Compare with the fixed alternative obtained by flipping just $x_i$ and
keeping the same authentic $k$. It belongs to the same family, and
correctness requires a different original in the output. If every Read
along the fixed run had the same presence answer on this alternative,
induction on the actual actions as in Lemma 14.1 would force identical
updates, choices, stopping and output. This is impossible. Hence there
is a first Read with different answers between these two runs.

Before that Read their acquired prefixes agree, so their extra-update
counts are the same $e_i$. This Read really occurs at the same point
in both runs; subsequent schedules may differ without restriction.
Its word must enter cone $i$, since every other cone and the scaffold
are identical at this shared prefix. The two ranks there are
$2k+e_i$ and $2k+e_i+1$. Lemma 14.2 therefore forces the selected
word to have length at least

$$
 d_i+k+\lfloor e_i/2\rfloor+1\ \ge\ d_i+k+1.
 \tag{GPO.47}
$$

Choose this first differing Read for every $i$. These are distinct
Read occurrences: one word enters at most one original cone. The fixed
run therefore contains at least $n$ such calls. Summing their lengths
gives $L+n(k+1)$; all unselected calls have nonnegative costs. Selecting
a deepest original leaf gives maximum at least $h+k+1$. These are
three bounds on the same arbitrary actual run, without a fixed schedule
or a separate optimum for each coordinate. Forward updates only increase
the common blind radius in (GPO.47). $\square$

**Theorem 15.2 (one fixed input pays all three bin lower bounds).**
Put $r=\lceil\log_2K\rceil$, so $r=0$ when $K=1$. For every $S,K$
and every competitor in Assumption 13.2 there exists one fixed
$(x,k)\in\mathcal F(S,K)$ whose entire actual run simultaneously has

$$
 \begin{aligned}
 Q&\ge n+r,\\
 M_{\rm addr}&\ge h+K+1,\\
 W&\ge L+n(K+1)+(\delta+K+1)r.
 \end{aligned}
 \tag{GPO.48}
$$

Proof. Take the union of the actual terminating runs on the finite
$K2^n$-member family, with nodes indexed by reached reply prefixes.
Each individual run, including all local work and updates, is finite;
the union is finite. Common-prefix control makes the next query or
terminal output unique at each such node. Terminal reply words are
prefix-free: if one were a proper prefix of another, the latter run
would be forced by the common intervening actions to stop at the former
one's output. Distinct required pairs cannot have the same terminal
reply word. Thus this finite reply tree has exactly $K2^n$ terminal
leaves.

Suppress its single-child queries and deterministic local/update segments
for the counting argument only. They remain charged actions in the
actual run. The resulting tree is binary, with each internal vertex an
actual query that has both bit answers among the compatible members.
A binary tree all of whose paths have at most $b$ branching vertices
has at most $2^b$ leaves: for $b=0$ there is at most one leaf, and at
an internal root the two subtrees each have at most $2^{b-1}$ leaves.
Therefore some actual leaf has at least

$$
 \lceil\log_2(K2^n)\rceil=n+\lceil\log_2K\rceil=n+r
 \tag{GPO.49}
$$

branching queries. Choose the original member $(x,k)$ that realizes
that leaf. It is fixed for its entire run, rather than chosen anew at
each query.

On this very run, Theorem 15.1 selected $n$ distinct first-difference
queries. Each is a branching vertex of the unsuppressed tree: its
single-bit-flipped alternative with the same $k$ follows the whole
prefix and supplies the opposite next bit. Thus all $n$ selected calls
belong to the at least $n+r$ branching calls just counted. Charge their
individual lengths by $d_i+K+1$, using (GPO.47) and $k\ge K$.
There are at least $r$ other branching calls; charge each by
$\delta+K+1$ using Lemma 14.2. These sets of actual occurrences are
disjoint, so their sum is precisely the asserted lower bound for $W$.
The deepest selected leaf also gives $M_{\rm addr}\ge h+k+1\ge h+K+1$,
and branching calls alone give the $Q$ bound. No separately attained
coordinate maxima have been added. The argument counts only reached
finite segments and permits every adaptive finite update schedule in
the competitor class. $\square$

## 16. One stationary comparator and exact minimax Read count

**Definition 16.1 (the paid zero-update comparator).** Choose the
leftmost shortest public leaf $p_*$, so $|p_*|=\delta$. Maintain a
binary-encoded interval $[l,z]$, initially $[K,2K-1]$. While $l<z$,
form

$$
 s=l+\lfloor(z-l+1)/2\rfloor,
 \qquad\text{submit the literal }\tau_\pi(p_*R^s).
 \tag{GPO.50}
$$

On presence one set $l=s$; on zero set $z=s-1$. At the resulting
singleton retain $k=l$. For each original leaf $i=1,\ldots,n$,
submit once the whole literal $\tau_\pi(p_iR^{k-1}LL)$ and use its
paid bit for $x_i$. Assemble $u_x$ using the public scaffold and these
actually acquired labels. Write the pair $(u_x,k)$ into owned readable
backing, preserving its same-root binding and current grants. There
are no source updates in this procedure.

**Theorem 16.2 (joint upper witness and exact minimax queries).** One
deterministic effective implementation of Definition 16.1 works for
every finite scaffold $S$ and every $K\ge1$. On every member of
$\mathcal F(S,K)$ it terminates correctly with zero extra updates and
simultaneously satisfies

$$
 \begin{aligned}
 Q&\le n+r,\\
 M_{\rm addr}&\le h+2K,\\
 W&\le L+2Kn+(\delta+2K-1)r.
 \end{aligned}
 \tag{GPO.51}
$$

Consequently, even among competitors allowed arbitrary finite adaptive
forward updates,

$$
 \min_A\ \max_{(x,k)\in\mathcal F(S,K)}Q_A(x,k)=n+r.
 \tag{GPO.52}
$$

The same comparator's worst $W$ and $M_{\rm addr}$ are each at most
twice their corresponding lower bounds in (GPO.48).

Proof. The first line of (GPO.45) makes every clock bit exactly the
threshold test $s\le k$, independent of the unknown label at $p_*$.
Its update retains $k$ and reduces an interval of $m\ge2$ integers
to one of sizes $\lfloor m/2\rfloor,\lceil m/2\rceil$. After $t$
such tests its size is at most $\lceil K/2^t\rceil$. This follows
inductively from halving integer interval sizes; equivalently, dividing
an integer interval into its two nearly equal parts at each level leaves
parts of size at most the ceiling of the original size divided by $2^t$.
Since $2^r\ge K$, at most $r$ tests suffice. This includes bins whose
size is not a power of two; their short branches may stop earlier.

Whenever a test is made, its split obeys
$K+1\le l+1\le s\le z\le2K-1$. Thus each clock word has length
at most $\delta+2K-1$. When $K=1$ there is no clock query, $r=0$,
and the public bin already fixes $k=1$; no nonexistent split is used.
The second line of (GPO.45) makes the following $n$ label queries
correct, each of length $d_i+k+1$. Their summed length is exactly
$L+n(k+1)\le L+2Kn$, and their maximum is at most $h+2K$.
The clock words have maximum at most $\delta+2K-1\le h+2K$.
Adding the phases proves (GPO.51). For $n=1$ the empty original
prefix incurs no extra letters, but every suffix is still fully
submitted and every Read still paid. No balanced or perfect scaffold
has been assumed.

Here is an effective operational realization of these finite instructions.
Parse the supplied finite preorder scaffold and use an ordinary stack
and path buffer to list its leaves, lengths and a shortest leaf. Each
extension, comparison, stack write and any copying is local work.
Perform integer addition, subtraction, halving and comparison by finite
binary tape routines. Construct each repeated suffix with a binary loop
counter, concatenate its entire path and translate each physical letter
by the supplied port bit. Retain the actual returned bits, then traverse
the finite scaffold again to write its labelled output. All intermediate
counters, words, stack frames and output bytes occupy real owned storage;
none is obtained from a hidden parameter or a zero-cost selector. Each
routine is finite on its actual finite operands, and the assumed progress
and growing backing permit its completion. This proves termination and
correct retention through handoff, without asserting any uniform workspace,
local-time, writer-size or total-price optimum. The source remains exactly
its entrance $\rho^{2k}u_x$ throughout.

Theorem 15.2 gives the lower inequality in (GPO.52); (GPO.51) gives
the upper inequality with this single comparator. For the claimed common
factor, all quantities are nonnegative and

$$
 \begin{aligned}
 h+2K&\le2(h+K+1),\\
 L+2Kn+(\delta+2K-1)r
   &\le2\bigl[L+n(K+1)+(\delta+K+1)r\bigr].
 \end{aligned}
 \tag{GPO.53}
$$

Indeed subtracting the left sides from the right gives respectively
$h+2$ and $L+2n+(\delta+3)r$. These comparisons use the one-run
lower bounds for every competitor and one common upper witness. They
do not assert equality of optimal summed letters, a complete Pareto
frontier or optimality for a weighted total service price. $\square$

## 17. The original acquisition protocol's fixed-size lag orders

**Corollary 17.1 (restriction, relaxation and the original upper bound).**
Fix any $n\ge1$, any $n$-leaf ordered scaffold $S$ and one persistent
$\pi$. Give the original acquisition problem authentic advice $A=B=n$.
Every deterministic effective protocol correct for its full authentic
entrance domain, even with arbitrary finite adaptive forward updates
under a source-blind extension of its actuator schedule, obeys (GPO.46)
on the restricted family (GPO.43), and has one member in each bin obeying
all of (GPO.48).

For the published first-completion protocol of Theorem 9.2, the exact
upper bounds (GPO.32)–(GPO.33), specialized to $B=n$, imply, for this
fixed $n$,

$$
 Q=O_n(\log(k+2)),\qquad M_{\rm addr}=O_n(k+1),\qquad
 W=O_n((k+1)\log(k+2)).
 \tag{GPO.54}
$$

Therefore its worst costs over $K\le k\le2K-1$ have the optimal lag
orders $\log(K+2)$, $K+1$, and $(K+1)\log(K+2)$ in these three
coordinates. The lower orders hold simultaneously on one fixed member
of each such bin for every competing protocol. This is a binwise
worst-case assertion, not a logarithmic per-run lower bound on $Q$.

Proof. Restrict original inputs to the actual originals $u_x$ with this
scaffold, this fixed orientation and lag in the stated bin. Then grant
the controller the true $S,\pi,K$ and immediate Read/update permissions
of Assumption 13.2. The original code can ignore those inputs and extra
permissions and execute precisely its original actions, including its
actual preparations. Its full output projects by finite local work to
$(u_x,k)$, with unchanged Reads, words and source updates. Every other
accessible field is still common at initialization, the writer remains
hidden, and the same register realizes every transition. Thus it is a
competitor in the relaxed class; Theorems 15.1–15.2 apply a fortiori to
its original run. A protocol with a more restrictive grant schedule is
included by simply respecting that schedule. No installation or advice
cost is removed from the real original run by this comparison.

For the upper bound reuse Theorem 9.2 exactly, rather than transplanting
the stationary comparator into the unknown-scaffold problem. With $B=n$,
$H\le k+n-1$, $h_a\le2k+n$ and $d_B=\lceil\log_2n\rceil$,
its $q_o$ is $O_n(\log(k+2))$ and $D_o\le4(k+n+1)$ is $O_n(k+1)$.
Its stated $W\le D_oq_o$ yields (GPO.54). This is its one actual
preparation update and stationary odd-cut acquisition, not a new
zero-update procedure for unknown $\pi$.

On the bin, (GPO.48) has $r=\lceil\log_2K\rceil$ and in particular
$W\ge(K+1)(n+r)$, $Q\ge n+r$, $M_{\rm addr}\ge K+1$.
For $K\ge2$, these have the asserted three lower orders; $n\ge1$
also covers $K=1$ with positive constant lower bounds. The uniform
upper bounds (GPO.54) have the corresponding orders throughout the bin.
All constants may depend on the fixed $n$ and scaffold. No optimal
dependence on an unknown leaf count, unknown shape, or $n$-varying
original problem has been deduced. $\square$

**Convention 17.2 (what is acquired and what continues).** The authentic
integer $k$ and all original labels are target coordinates here. The
comparison controller actually pays its clock and leaf probes, their
literal lengths and finite bit work to acquire them; the original
controller actually pays Theorem 9.2's orientation, clock, cap tests,
node probes and one material update. Neither uses a readable hidden epoch
or writer. A restricted logical consumer can require less than $(u,k)$;
these bounds are not assigned to every task or every memory representation.

The independently meaningful observations for the original protocol remain
exactly Definition 12.1's physical incidence $S_o$, terminal antichain
$\partial_o$, authentic counts $T_{\rm ent}=2k,T_o=2k+1$, and acquired
readable $\mathsf M_o=(\pi,u,k,n,1)$ with actual backing, same-root
binding and current grants. Theorem 12.2 already supplies their attained
incidence/boundary recovery, agreement and the recovery of counts from
that record. Theorem 11.2 and Proposition 11.3 already supply lawful
same-register successors, pending cuts and the additive costs of actual
continued use. Those are reused conclusions. The new price bounds concern
acquiring their authentic original/lag coordinates, without re-publishing
those inverses or the continuation as new theorems.

The comparator instead ends at the stationary even entrance. Its pair as
abstract data is not automatically the original odd-cut usable record.
Any handoff to a service requiring the odd relation must actually perform
the permitted one extra update, retain its known phase, compute the needed
adapter/offset and retain accessible backing, binding and current rights;
those actions have their actual charges. Under those conditions the
already proved odd-cut continuation applies. Merely supplying the same
symbols to a decoder installs no new service. For any actual finite
acquisition followed by lawful continuation with costs $Q_c,W_c,M_c$,
the combined query coordinates are $Q+Q_c,W+W_c,\max(M_{\rm addr},M_c)$;
actual updates, evaluator work and all retained material add their own
charges, exactly as in Proposition 11.3.

## 18. Mathematical correspondence and the remaining recovery scope

**Convention 18.1 (reused proofs and source-specific content).** The
joint family, adaptive-update price theorem and common comparator above
are `repo-derived` ordinary mathematics. Their additional conclusion is
the authentic even-lag bin's additive joint acquisition price, with one
fixed realization witnessing all three lower bounds and one zero-update
comparator attaining the exact minimax binary Read count. The structural,
counting and search tools are suppliers, with the following precise
correspondence.

[GenealogicalFiberTransport][GFT] and its
[owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.scribe.cs)
use `Source = FreeMagma Bool`, true for alpha, false for beta, the same
pair-distributing substitution, and actual ordered shape/leaf-label
assembly. Its proof-local `no_alpha` serves substitution injectivity,
not unknown-source acquisition. The algebra and homomorphic extension are
Kenny Lau's `FreeMagma.of`, `mul`, `liftAux`, `lift` in the pinned
[Mathlib/Algebra/Free.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Free.lean).
These do not provide physical order or a source port.

[ActualFibonacciSupportChain](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.lean)
and its
[owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.scribe.cs)
supply the actual recurrence and support blind radii, including the
proof-local `recurrence`, `monotone`, `short` and `spine` arguments.
Lemma 14.2 recalls the all-word present-suffix induction to expose its
parameter $2k+e_H$; it does not claim that induction as a new theorem.
The stationary leaf test is precisely ABT12.3, with its actual full-root
word convention and authentic-domain conditions in ABT33.1–33.3.

[NativeSerialMachine][NSM] and its
[owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs)
supply source-blind control, deterministic reached-prefix replay and one
actual register's forward chronology. [ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)
and its
[owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs)
supply the literal `Address`, `Reply`, `readout` and leaf occurrence
conventions. Only those definitions are imported here: that module's
separate `paid` distinct-address objective is not this volume's
per-invocation $Q$. [DelayedOriginalReadout][DOR] and its
[owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.scribe.cs),
including private `clock_step`, `clock_at_step`, `label_clock_decode`
and `guard_clock`, give the known-epoch full-reply clock/guard context.
Both formal machine suppliers permit four-valued replies. Control here
explicitly receives their presence projection; no hidden alpha/beta or
branch distinction is borrowed as an extra bit.

[Native Dynamic Acquisition Frontiers](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DYNAMIC_ACQUISITION_FRONTIERS.md),
Definitions 2.3–2.5, Lemma 3.2, Theorems 3.3,5.1,5.4, already supply
single-occurrence dynamic locality, finite binary reply-tree counting
and one-coordinate first-difference charging. Those methods are credited,
not new lower-bound principles. Its $G_0/G_1$ bracket gadgets have a
common all-alpha leaf word, permit the stated one-hole context operations,
and yield $\sum_i(d_i+1)$; they are not the leaf-labelled originals
$u_x$ with one shared unknown even lag. Equations (GPO.47)–(GPO.48)
add the present source's lag-dependent blind radius and account for the
extra bin information on the very same run as all label charges.

[Acquired Orbit Resource Frontier](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md),
Definitions 8.1–8.2 and Theorems 8.3,9.1–9.3, solve stationary
single-orbit interval identification with full four-valued replies,
including the zero-origin boundary, bounded-query simulation and exact
call/peak attainment. Its two singleton reply cells affect capacity;
the presence-only interface here has only two outcomes, additional
unknown original labels, arbitrary finite scaffolds and adaptive forward
updates. Its exact lower bounds are not transferred to this different
contract.

[Native Alpha Task-Lag Realization](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_TASK_LAG_REALIZATION.md),
Assumption 1.1, Theorem 2.2 and §§4–5, uses an actually acquired early
encoder, a fixed complete later entry, a visible reference and full-reply
adjacent ages to transport Boolean coordinate tasks with literal weights.
Its original age cube, discarded/acquired state and lag target remain
unchanged. [Literal Query Frontier](RECURSIVE_RELATIONAL_OBSERVATION_LITERAL_QUERY_FRONTIER.md),
Definitions 1.1–1.2,2.1, likewise uses a complete acquired origin-code
fiber, stationary full replies and no updates. Their guarded all-word
navigation and coordinate methods are suppliers, not an acquisition of
this unknown authentic $(u_x,k)$ from only presence bits.
[Finite-Menu Minimal Memory](FIB_NATIVE_FINITE_MENU_MINIMAL_MEMORY.md),
Definitions 2.2–2.4 and §§7–9, instead minimizes complete retained
state for future menu values with a supplied count, and separately cites
paid unknown-lag capture. A supplied count, a minimal retained alphabet
and a bound on acquiring an unknown original/count are distinct contracts.
No retained-alphabet minimum is deduced from (GPO.48).

For primary comparison, Petra van den Bos and Frits Vaandrager,
[*State Identification for Labeled Transition Systems with Inputs and
Outputs*, arXiv:1907.11034v2](https://arxiv.org/abs/1907.11034v2),
§6, Definition 33, Lemma 34 and Theorem 35 with its full proof (v2 PDF
numbering, pp. 23–24), treat finite
suspension automata with finite input/output alphabets. Their injective
splits preserve the incompatibility of still possible states; the
completeness theorem assumes every two distinct states incompatible.
The common concern is preservation of distinctions through actions.
A finite set of entrance candidates does not identify the unbounded
forward register/controller state space with that finite automaton.
No source-, action-, observation- and literal-cost-preserving reduction
has been supplied here, and neither their synthesis nor its completeness
is used as a theorem about (GPO.43). The proofs above use the actual
finite run tree of each terminating competitor instead. This is bounded
source correspondence, without an exhaustive literature or priority
claim; absence of a theorem name or local dependency checkout supplies
no novelty evidence. These ordinary proofs are not new Lean certification.

**Convention 18.2 (precise limits of the acquired price).** The three
coordinates price actual deterministic exact acquisition within the
specified root-word and no-side-channel contract. They give neither an
exact summed-letter optimum nor an exact joint Pareto frontier, no
optimal unknown-size/shape dependence, and no uniform memory minimum,
finite-state implementation, runtime or total-service optimum. They
make no randomized, error-tolerant, extra-timing-channel or writer-readable
claim. Forward-update competitors are included; additional observation
channels are different hypotheses. Public scaffold, bin, orientation,
installation, rights, actual expanding material and internal update work
retain their separate nonzero resource accounts.

The larger four-expression objective still lacks recovery of an original
from time alone, unrestricted four-way recovery, physical metric and
duration identification, removal/acquisition of all installed-reference
and authenticity premises, and a universal reduction to two generators.
The original fixed-apparatus, original-Q, parked-consumer and unchanged-
initialization problems retain their exact assumptions and open
obligations. The NCR/PVC/PR57/PG/Atlas interfaces are not altered.

The independently published
[sharp-task retained environment record](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md),
Definitions 1.1–1.2 and §7, uses an actual measured quantum instrument,
all-qutrit inputs, classical outcome words and task-dependent terminal
CPTP decoders. [Environment Record Memory II](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY_II.md),
Definition 29.1, has its own erased-history qutrit-channel task.
[Central-Noise Green Stability](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md),
Definition 12.1 and §14, keeps its continuous stochastic cylinder,
persistent driving source, actual paid tracking and matched weighted
response. Binary measured labels and the continuous phase names are not
the free-tree constructors in (GPO.1). No common-source map transporting
initialization, observations, legal actions, backing, rights and resources
between any of those processes and (GPO.43) is proved. Their newer
conclusions therefore remain distinct suppliers with their own domains.
This finite source-specific acquisition-price result does not complete
the continuing common-source space/time/boundary/memory programme.

## 追加锚（本行以下为增补区）

## 19. Exact worst literal traffic on the scaffold family

**Definition 19.1 (the two optimization domains).** Keep Definition
13.1 and Assumption 13.2 without changing either the authentic output
$(u_x,k)$ or the competitor class. In particular, the public inputs are
the authentic scaffold $S$, persistent global correspondence $\pi$ and
bin $[K,2K-1]$; the only acquired source information consists of paid
presence bits on the one actual register. Competitors may make arbitrary
finite adaptive forward updates. Let $\mathscr A(S,K)$ be this class,
and put $b=2K-1$. Define

$$
\begin{aligned}
 W_*(S,K)&=\min_{A\in\mathscr A(S,K)}\max_{x,k}W_A(x,k),\\
 W_{\rm call}(S,2^r)&=
 \min_{\substack{A\in\mathscr A(S,2^r)\\\max_{x,k}Q_A(x,k)\le n+r}}
                         \max_{x,k}W_A(x,k).
\end{aligned}
\tag{GPO.55}
$$

Every maximum is over the full family (GPO.43). These are two different
optimization problems. Whole literal root words, absences and repetitions
have exactly the charges of Definition 1.3; prefixes are not shared for
free. The attaining protocols below establish the displayed minima, not
just infima. Neither objective includes the separate prices of local
work, source material, installation, retention or later use.

The guarded navigation supplier in
[FiniteSourceMass](../../../D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.lean),
`finite_source_masses`, including its proof-local `threshold_last`, gives
the following convenient form. For a nonempty semantic suffix $q$, write
$c(L)=1,c(R)=2$ and

$$
 \vartheta(q)=2+\sum_{\text{letters of }q\text{ except its last}}c(d).
 \qquad P_{T_j}(q)=1\ \Longleftrightarrow\ j\ge\vartheta(q),
 \qquad \vartheta(q)\le2|q|.
 \tag{GPO.56}
$$

Indeed its guarded threshold is the maximum of total path cost and
last-parent path cost plus two. The last edge costs at most two, so the
second term is that maximum. Equivalently, all proper-prefix residual
ranks must be at least two; their largest consumed cost occurs at the
last proper prefix. This also covers singleton suffixes and ranks zero
and one. The empty suffix is always present. This is reuse of actual
guarded navigation, not installation of a threshold oracle. By Lemma
14.1, each nonconstant reached Read is therefore, in one original cone,
the actual test $2k+e_H+x_i\ge\vartheta(q)$.

**Theorem 19.2 (unconstrained literal optimum in a stated regime).** For
every finite nonempty scaffold $S$, every $K\ge2$, and
$n\ge\delta+2K-2$,

$$
 W_*(S,K)=L+2Kn+\delta+2K-1.
 \tag{GPO.57}
$$

The condition on $n$ is sufficient for this formula; no maximal validity
domain or formula for smaller $n$ is asserted.

Proof. Fix any competitor and the single authentic input
$(x,k)=(0^n,b)$. For every $i$, compare this run with the allowed input
obtained by flipping only $x_i$. Correctness requires a first different
paid reply. At their common reached prefix, Lemma 14.1 supplies the same
extra-update count $e_i$ and word $p_iq$. The two ranks are
$2b+e_i$ and $2b+e_i+1$. Equation (GPO.56) forces
$\vartheta(q)=2b+e_i+1$, hence the selected word has length at least
$d_i+\lceil(2b+e_i+1)/2\rceil\ge d_i+b+1$.
The $n$ selected occurrences are distinct because a word enters only
one original cone.

Compare the same high input with the allowed input $(1^n,b-1)$.
Here $b-1\ge K$ uses precisely $K\ge2$. Their first different reply
has common extra-update count $e$, cone ranks $2b+e$ and $2b-1+e$,
and threshold $\vartheta(q)=2b+e$. Its literal length is at least
$\delta+b$. This occurrence is different from every selected label
occurrence: at this occurrence the high rank and its one-label-flipped
rank are both at least that threshold, so it cannot separate that label
flip. All charges occur on the same fixed high-input run. Thus

$$
 W_A(0^n,b)\ge L+n(b+1)+\delta+b.
 \tag{GPO.58}
$$

This argument permits every adaptive finite update schedule; it equates
only actually shared prefixes, not the later schedules of distinct runs.

For attainment choose a shortest public leaf $p_*$. On the stationary
entrance register submit $\tau_\pi(p_*R^s)$ for
$s=b,b-1,\ldots,K+1$, stopping at the first one. By (GPO.45) each
bit is exactly $[k\ge s]$. The first one identifies $k=s$; if all
bits are zero, set $k=K$. Then submit the $n$ actual words
$\tau_\pi(p_iR^{k-1}LL)$, acquire their label bits, assemble $u_x$
and retain $(u_x,k)$. Every operand is public or already acquired.
The exact costs on this one run are

$$
\begin{aligned}
 Q(k)&=\begin{cases}n+b-k+1,&k>K,\\n+K-1,&k=K,\end{cases}\\
 C(k):=W(k)&=\begin{cases}
 L+n(k+1)+\displaystyle\sum_{s=k}^{b}(\delta+s),&k>K,\\
 L+n(K+1)+\displaystyle\sum_{s=K+1}^{b}(\delta+s),&k=K.
 \end{cases}
\end{aligned}
\tag{GPO.59}
$$

For $K+2\le k\le b$,
$C(k-1)-C(k)=\delta+k-1-n\le0$ under the stated hypothesis;
also $C(K)-C(K+1)=-n$. Consequently
$\max_k C(k)=C(b)=L+n(b+1)+\delta+b$. Together with (GPO.58)
this proves (GPO.57). The displayed finite loops, binary comparisons,
literal construction, translation, acquired writes and assembly have
finite effective implementations exactly as in Theorem 16.2. They pay
their actual local work and use growing owned backing. They terminate
under the same progress premise, without any unknown stopping operand.
$\square$

## 20. The literal price forced by minimum calls

**Theorem 20.1 (exact traffic under the minimum-call constraint).** For
every finite nonempty scaffold, $K=2^r$ and $r\ge1$, without a lower
bound on $n$ beyond $n\ge1$,

$$
 W_{\rm call}(S,K)=L+2Kn+r\delta+2Kr-K+1.
 \tag{GPO.60}
$$

The call allowance $n+r$ is already the exact minimum worst $Q$ in
Theorem 16.2. The additional assertion is the optimal literal price
within that allowance, including updating competitors.

Proof. Let $D=n+r$ and take a correct competitor with worst $Q\le D$.
Its finite binary reply tree has $K2^n=2^D$ distinct terminal leaves,
as in Theorem 15.2. A binary tree of height at most $D$ with $2^D$
leaves is perfect: each child must attain its own capacity $2^{D-1}$,
and the same argument recurses. Equivalently, suppressing a one-child
paid Read would leave every terminal at branching depth $D$ and still
charge that extra Read, violating $Q\le D$. Thus every Read branches;
at depth $d$ each child has exactly half of the compatible candidates.
Deterministic local work and actual updates may occur between these
Reads and remain real paid actions.

Inductively, before the $(j+1)$st Read, $0\le j<r$, the compatible
set is $I\times\{0,1\}^n$, where $I=[a,a+m-1]$ has
$m=2^{r-j}\ge2$ lags. By Lemma 14.1 and (GPO.56), a branching
Read has a cone suffix and tests $2k+x_i\ge t$, with
$t=\vartheta(q)-e_H$. If $t=2s$ it selects whole lag layers and
reveals no label. If $t=2s+1$ is nonconstant, its positive side
contains whole layers plus exactly half of the layer $k=s$.
Each whole layer has $2^n$ members, whereas a perfect split requires
$(m/2)2^n$ members on each side. The half-layer case cannot supply
that integer multiple of $2^n$. Hence $t$ is even and its unique
balanced split is $s=a+m/2$. The successor set is again a lag interval
times the unrestricted label cube. This proves that the first $r$
Reads must acquire the lag by balanced thresholds before learning any
label. It is a conclusion about this tight budget, not an assumption
on all protocols.

On the fixed high-lag input $k=b$, their thresholds are
$s_j=2K-K/2^j$, $1\le j\le r$. At a reached such Read,
$\vartheta(q)=2s_j+e_H$, so its length is at least
$\delta+\lceil(2s_j+e_H)/2\rceil\ge\delta+s_j$.
Their total literal cost is at least

$$
 r\delta+\sum_{j=1}^r(2K-K/2^j)
          =r\delta+2Kr-K+1.
 \tag{GPO.61}
$$

After this clock prefix, all $n$ labels are still free. On the same
input, say $x=0^n$, the $n$ first-difference label occurrences of
Theorem 15.1 must occur afterwards, and cost at least
$L+n(b+1)=L+2Kn$. Adding these disjoint occurrences proves the
lower bound in (GPO.60).

Use the already installed zero-update midpoint comparator of Definition
16.1 for the upper. Its $j$th clock threshold on any path is at most
$2K-K/2^j$; equality holds on the high-lag path. This follows by
induction on the successive equal-size upper subintervals. Use $p_*$
for every clock word. Their costs are therefore bounded by (GPO.61),
and the label phase costs $L+n(k+1)\le L+2Kn$. On $k=b$ equality
holds in both phases, independently of $x$. Its worst $Q$ is $n+r$.
This proves attainment of (GPO.60). $\square$

**Corollary 20.2 (a strict conflict of the two coordinates).** When
$K=2^r$, $r\ge2$ and $n\ge\delta+2K-2$, the exact penalty for
requiring minimum worst calls is

$$
 W_{\rm call}(S,K)-W_*(S,K)
       =(r-1)\delta+(2r-3)K+2>0.
 \tag{GPO.62}
$$

Proof. Subtract (GPO.57) from (GPO.60). The first term is nonnegative
and $2r-3\ge1$. Thus no one protocol minimizes both worst $Q$ and
worst $W$ on this intersection. Each optimum has its own common-run
upper witness; they have not been added or declared jointly attainable.
For $r=1$ the two expressions agree. No assertion about the full
Pareto frontier follows. $\square$

## 21. Acquired use and supplier correspondence for the literal optima

**Proposition 21.1 (same-run prices and even handoff).** The descending
controller in Theorem 19.2 has worst $Q=n+K-1$; the midpoint controller
in Theorem 20.1 has worst $Q=n+r$. Both have zero acquisition updates,
worst $M_{\rm addr}=h+2K$, and their respective exact $W$ values
just proved. They actually retain the authentic pair at the unchanged
entrance cut. With the supplied $\pi$ and the derived public original
count $n$, their usable record is $(\pi,u_x,k,n,0)$ with backing,
same-root binding and current grants.

Proof. Equations (GPO.59) and the midpoint construction give the call
counts. Their label words have length $d_i+k+1$; at $k=b$ a deepest
leaf attains $h+2K$. Every clock word has length at most
$\delta+b<h+2K$. Actual assembly writes the acquired data into
owned readable backing and preserves the supplied services through
handoff. Since $K\ge2$, every successful cut lies in Definition 6.1's
passive $k\ge2$ domain, with authentic advice $A=B=n$. Theorems
6.2 and 6.4 therefore apply directly: physical incidence and terminal
boundary recover the same target, and the retained record recovers
these data and authentic count $2k$. With fixed $N=2k$, every completed
logical macro boundary satisfies
$\widehat r_e=\rho^N(\rho^eu_x)$ on this very register. The supplier
preserves complete four-valued logical replies, absence, choices,
outputs, successors and pending cuts. These are reused continuation
results, not consequences merely of a query optimum. $\square$

If an odd-offset consumer is selected instead, execute one actual
permitted update and retain its phase: now the register is
$\rho^{2k+1}u_x$. Theorem 11.1 and Theorem 11.2 then apply with fixed
$N=2k+1$. That update, its material and actuator work, finite offset
arithmetic and attachment are additional costs. Either handoff followed
by a finite continuation with charges $Q_c,W_c,M_c,U_c,J_c$ pays
$Q+Q_c,W+W_c,\max(M_{\rm addr},M_c)$ and its actual sum of updates
and local work. Resuming a pending macro retains its already acquired
bit and evaluator state; it does not refund or repeat that Read.

The programs pay parsing of $S$, shortest-leaf selection, every binary
counter operation, whole-word construction/translation, output assembly,
allocation, record access and maintenance. All are finite on their
attained operands. The Read backend additionally pays at most $W+Q$
root/edge steps under Definition 1.3's node-following implementation.
The source, private full writer, public scaffold/orientation/bin, their
authentication, surviving rights, code, scratch and retention lifetime
have separate actual prices. A data encoding of $x,k-K$ has $n$ label
bits and $\lceil\log_2K\rceil$ lag bits, but is not a total memory
minimum. Finite code does not mean fixed storage capacity.

The source-relative increment beyond Convention 18.2 is (GPO.58)'s
extra disjoint clock charge, the descending attainment regime, and the
tight-call forced clock prefix yielding (GPO.60). The existing cone,
first-difference, finite reply-tree and midpoint results of §§13–16
are suppliers. FiniteSourceMass and its
[owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.scribe.cs)
supply (GPO.56); NativeSerialMachine and its Scribe supply actual
reached-prefix control, not a hidden epoch. The ordered algebra remains
GenealogicalFiberTransport and pinned mathlib's `FreeMagma` as in §18.

For literature comparison, Cicalese–Keszegh–Lidický–Pálvölgyi–Valla,
[*On the Tree Search Problem with Non-uniform Costs*,
arXiv:1404.4504v1](https://arxiv.org/abs/1404.4504v1), §§1–2,
defines cost as the sum of actual query costs along one decision-tree
path, followed by its maximum. Proposition 2 is the general exponential
algorithm; **Theorem 2**, rather than Theorem 2.1, is the exact weighted
path algorithm. Their oracle cuts an edge of one fixed input tree and
returns its component containing a sought vertex. It does not implement
the multi-cone unknown label/lag source, changing ranks or literal root
tariff here. The weighted-search objective is literature-attested;
neither that path algorithm nor its complexity is transported without
such a correspondence. The formulas here have the direct proofs above.
They are repo-derived synthesis, with no worldwide-priority or new Lean
certification claim. Smaller-$n$ unrestricted $W$, non-power-of-two tight
call traffic, the whole frontier and total-resource parsimony remain
outside these exact formulas.

## 追加锚（本行以下为增补区）

## 22. A locally wired service and its exact two-step image

**Definition 22.1 (local birth wiring, with separate tasks).** The
following service replaces the single global $\pi$ of Assumption
1.2(1),(7). It does not change the source algebra (GPO.1). At each
actual branch there are distinguishable physical children $a,b$ and
a local bijection to its semantic children $L,R$. That bijection
persists as long as the branch persists. An old branch and its links
persist under substitution. When a beta leaf splits, one actual hidden
wiring bit places its semantic beta/alpha children at $a,b$ in either
order. All finite assignments at all births are legal. No probability
law, independence law or accessible law tying these choices to the past
is postulated. The choices are actual actuator inputs and material
relations, in addition to the labels and substitution; they are not
free advice to the observer.

Keep one stable bound root, total paid absolute physical-word presence
Read, localStep, serial forward applyRho and stop. Only a common
completion acknowledgement is exposed by an update. Full physical
labels, the writer, past epochs, link creation, allocation identities,
capacity, runtime and private choices provide no additional channel.
Control, code, grants and initial accessible backing are common at
fixed public inputs. Finite-work progress, owned growing readable
backing, current rights and reference maintenance remain paid installed
premises. Reads and declared acquisition phases are stationary; no
concurrent updates, reroot, reset, inverse, clone or historical root is
supplied. Each old-node update substitutes exactly once at the old
leaves, as in Proposition 9.3, with the new local wiring in place of a
global one. Every request, word, computation, allocation and retained
write is paid.

There are three distinct targets below. The arbitrary-original task
starts at an authentic $\rho^{2k}u$, with $k\ge1$ and authentic
$1\le A\le n=\ell(u)\le B<2A$, and asks which semantic original
$u$ is recoverable. The known-seed task starts at the actual known
alpha leaf, counts completed updates as $n$, and asks for the full
physical presence map after the next update, predicted at the current
cut. Historical calibration instead returns the labelled physical
state of a preceding cut after one real update. Original identity,
current prediction and historical recovery are not interchangeable
claims. The symbol $n$ denotes original leaf count only in §23 and
completed-update count only in §§24–25.

Write $\operatorname{phys}(t)$ for a labelled tree in its actual
physical $a/b$ order, and $\operatorname{sh}$ for label erasure.
Write $[t]$ for rooted label-preserving unordered isomorphism: it
forgets all child order but retains every branch, leaf and label.
These are occurrence trees, without subtree sharing or word
associativity. An unordered isomorphism is not an acquired local
semantic adapter.

**Theorem 22.2 (exact local two-step recognizer).** Put
$C=\langle\bullet,\bullet\rangle$. The set of possible unlabelled
physical shapes after two substitutions on an arbitrary labelled
physical tree is exactly the grammar

$$
 \mathcal G_{\rm loc}::=
 C\ \mid\ \langle C,\bullet\rangle\ \mid\
 \langle\bullet,C\rangle\ \mid\
 \langle g_1,g_2\rangle\quad(g_1,g_2\in\mathcal G_{\rm loc}).
 \tag{GPO.63}
$$

There is a terminating recognizer/decoder $D_{\rm loc}$ with the
following exact rules. A leaf rejects. At a branch, two leaf children
decode to alpha; mixed branch/leaf children decode to beta **only if
the branch child is exactly $C$**. A mixed case with a larger branch
rejects. Two branch children decode to their physical ordered pair
only if both recursive parses succeed; otherwise they reject. This
recognizes precisely (GPO.63), and every accepted shape has one and
only one labelled physical predecessor $U$. It accepts $X$ and returns
$U$ if and only if $X$ is the shape of a possible two-step locally
wired expansion of $U$. In particular
$[u]\mapsto[\operatorname{sh}(\rho^2u)]$ is injective.

Proof. After two updates an alpha leaf has shape $C$. A beta leaf
first creates a beta/alpha pair; the beta child then creates $C$ and
the alpha child stays a leaf, giving precisely the two mixed codes.
An old branch retains its physical children, each of which has a
two-step code with a branch root. Thus the four root cases are
disjoint, and the mixed case has the stated exact cherry requirement.
Structural induction gives acceptance and the original physical
predecessor for every actual expansion.

Conversely, for each accepted code realize its alpha or beta case by
the two actual leaf substitutions just described, choosing the beta
code's first birth orientation to match its displayed side. In the
pair case, realize the two recursive expansions below the old branch,
whose physical links are retained. This realizes every accepted shape.
The same disjoint cases force uniqueness of its predecessor; each
recursive call decreases tree size, proving termination. There need
not be a unique newborn-frame assignment or a unique expanded labelled
tree: the inverse just proved concerns the predecessor, not those
additional hidden fields.

The recognizer is equivariant under local exchanges of the two
children: its mixed cases both return beta, and its pair case exchanges
the two decoded children. Consequently unordered-isomorphic accepted
shapes have unordered-isomorphic labelled decodes. Applying this to
actual two-step images proves the last injectivity statement. Ordered
ABT12.1 alone would not prove that unordered assertion. $\square$

## 23. Arbitrary authentic originals: acquisition and the complete fiber

**Theorem 23.1 (acquired physical ancestor and exact semantic fiber).**
In Definition 22.1's arbitrary-original domain, let $U$ be the authentic
original written in its actual physical branch order. One common
effective presence-only procedure acquires and retains $(U,k,n)$ with
zero updates. For a fixed complete current physical presence service
and the same authentic interval, the entire semantic target fiber is

$$
 \{(v,k,n):[v]=[U]\}.
 \tag{GPO.64}
$$

Define the unordered-invariant integer $a$ by

$$
 a(\alpha)=a(\beta)=0,\qquad
 a(\langle s,t\rangle)=a(s)+a(t)+\mathbf1_{[s]\ne[t]}.
 \tag{GPO.65}
$$

There are exactly $2^{a(U)}$ different semantic originals in (GPO.64).
The fiber is a singleton exactly for perfect monochromatic originals,
including either single labelled leaf. On every nonsingleton fiber,
uniform recovery of the original semantic Read/applyRho task from this
service fails even with arbitrarily many adaptive forward updates.
The positive acquisition and the negative semantic conclusion concern
the same full realization class.

Proof. First acquire the finite current physical shape $X$ by a stack
traversal. Its root is known present. At each confirmed node $p$, pay
Read$(pa)$; this bit classifies branch versus leaf in a full binary
tree. Schedule $pa,pb$ only on a branch. Each actual node is visited
once and stack exhaustion terminates without a size or height oracle.
Now apply $D_{\rm loc}$, erase the decoded labels, and repeat until
the first decoded leaf count is at most $B$.

For decoding stage $j\le k$, Theorem 22.2 gives precisely the actual
physical version of $\rho^{2(k-j)}u$. Its leaf count is at least
$2^{k-j}n$, using ABT39.1's two-step growth. At every $j<k$ it is
at least $2n\ge2A>B$, whereas at $j=k$ it is $n\le B$.
Even the initial count exceeds $B$. Thus the first crossing is exactly
$k$, no parse past the authentic original is attempted, and the
returned labels and physical branch order are exactly $U$. All parsing,
counting and comparisons use finite acquired strings and public advice.
Actual retained writes make $(U,k,n)$ readable on this same run.

Any alternative realization with the same complete physical presence
service gives the same $X$, and this deterministic decoding/crossing
gives the same $U,k,n$. Its semantic original is therefore in $[U]$.
Conversely, fix any ordered $v$ with $[v]=[U]$. A rooted
label-preserving unordered isomorphism assigns local frames at its old
branches so its physical original is exactly $U$. Follow corresponding
leaves through each actual update: matched alpha leaves become matched
beta leaves; matched beta leaves create corresponding beta/alpha
children. Choose their local birth frames to match the physical
placements of the original realization. Old branches keep their
frames. Induction realizes the same complete labelled physical tree
at entrance, not just the same marginal shape, with semantic original
$v$ and the same authentic $k,n$. This proves both directions of
(GPO.64).

Let $E(W)$ count ordered labelled representatives of an unordered
class $W$. A leaf has $E=1$. A branch with distinct child classes
$X,Y$ has $E=2E(X)E(Y)$, because their two physical positions are
distinct choices. With equal child classes it has $E=E(X)^2$:
every ordered pair of representatives occurs, and there is no
additional exchange factor. Induction proves $E([U])=2^{a(U)}$.
For $a(U)=0$, every branch has isomorphic children and both have
zero $a$. Inductively they are perfect monochromatic trees of the
same height and colour. This proves precisely the singleton
classification, with its converse immediate from (GPO.65).

For persistence of ambiguity, take any two different ordered originals
in (GPO.64) with the matched labelled physical entrance trees just
constructed, and common accessible initialization. After entrance choose
the same physical rule, for example beta always placed at $a$, at every
matched new birth in both realizations. This is a legal actual choice
sequence; it needs no changing adversary or future oracle. Equal
physical labelled trees then give equal physical presence replies and
equal labelled successors under each update. Induction on the full
accessible actions gives identical requests, acquired records, local
control, acknowledgements, stopping and outputs for every finite
adaptive controller. Even granting full future physical labels would
leave this pair indistinguishable. The different semantic originals
have different four-valued replies at some original semantic address,
by the finite-tree distinction in Proposition 6.3. Hence no uniformly
correct acquired adapter can serve all those original continuations.
This is fiberwise identifiability; it does not deny that a constant
program can name one source on a separately promised singleton input.
$\square$

**Proposition 23.2 (quotient prediction, views and the actual bill).**
From the acquired record of Theorem 23.1 and the actually counted $e$
subsequent completed updates one can compute
$[\rho^{2k+e}u]$. This predictor agrees with the unordered labelled
current register at every attained finite cut. It predicts neither
arbitrary physical-address replies nor a missing original semantic
adapter.

Proof. A local exchange at an old branch remains an unordered
isomorphism after $\rho$, and corresponding leaf replacements are
unordered-isomorphic. Thus substitution defines a function on these
unordered classes. Apply it $2k+e$ times to $[U]$. The entrance
relation and one-step compatibility prove agreement by induction on
the actual updates. Finite tree evaluation and canonicalization are
ordinary local computations on retained data; they create no source
sensor or second mutable root. $\square$

Here space is the actual current physical rooted incidence
$S_X=\{w:P_X(w)=1\}$; boundary is its terminal physical-address
antichain $\partial_X$; time is the authentic substitution count
$2k$; memory is the acquired $(U,k,n)$ with readable backing, the
same binding and surviving rights. Prefix closure and maximality give
$\partial_X\leftrightarrow S_X$. Their two parsing routes return
the same $U,k,n$ and hence count $2k$. Memory recovers the unordered
labelled current tree and its unordered terminal geometry, and tracks
them as just proved. These routes are on one actual realization.
Memory alone does not recover its current physical layout: for
$u=\alpha,k=2$, the two unequal root-child shapes of $T_4$ may
occupy opposite physical ports while $U,k,n$ stay fixed. Time alone
also fails to determine $U$, since alpha and beta originals with
$n=1$ and the same $k$ have equal advice and time but different labels.

If $X$ has $\Lambda$ leaves, $N=2\Lambda-1$ nodes and height $H$,
the actual stationary scan has exactly

$$
 Q=N,\qquad W=\sum_{p\in S_X}(|p|+1),\qquad
 M_{\rm addr}=H+1,\qquad U_{\rm updates}=0.
 \tag{GPO.66}
$$

Every leaf's failed child query is included. Root/edge-following service
adds at most $W+Q$ traversals. These are one protocol's prices, not
optima. All stack manipulation, parser passes, counting, comparisons,
canonicalization, literal construction, allocation, copying and retained
writes contribute actual finite local work; there is no asserted
uniform local-time or workspace bound. A preorder $U$ uses $3n-1$
shape/label bits, with binary $k,n$, framing, capabilities and advice
additional. The acquired expanded shape and scratch can coexist with
that output. Every future predictor evaluation, actual update, output
and lifetime of backing has its own price. Selecting a semantic original
from the fiber would require at least $2^{a(U)}$ supplementary values;
none is acquired here. Enlarging storage or re-encoding acquired bits
cannot supply that distinction.

## 24. A known alpha seed and the current one-update task

**Definition 24.1 (the prediction cut and its task).** Start instead
with the actual known alpha leaf in the local service of Definition
22.1. Let $T_m=\rho^m\alpha$ denote the semantic paper tree and
$X_n$ its actual physically ordered labelled realization after $n$
completed serial updates, with all actual persistent birth choices.
Write $S=\operatorname{Pos}(X_n)$ for its current physical shape and
$\partial S$ for its terminals. For $n\ge2$, let

$$
 C(S)=\{p:pa,pb\text{ are both leaves of }S\},\qquad
 \chi_p=\mathbf1_{X_n(pa)=\beta}\quad(p\in C(S)).
 \tag{GPO.67}
$$

The task $\mathcal Q_1$ asks, **before** the next update, for its
entire successor presence response map on all finite physical words,
including absent words. It can equivalently serve any later chosen
stationary Read-and-stop request after that one update. This is not
the semantic tree $T_n$, which is already known from the seed and
count. New choices made during the next update do not affect the
unlabelled shape of the new cherries, so $\mathcal Q_1$ is determined
by the current labelled state; it does not ask an observer to predict
unmade choices.

**Theorem 24.2 (complete current fibers and their exact sizes).** With
$F_0=0,F_1=1$, for every attained $n\ge2$ and every attained $S$,
the current labelled fiber over $S$ consists of exactly the independent
choices of $(\chi_p)_{p\in C(S)}$, and

$$
\begin{aligned}
 |C(S)|&=F_{n-1}=:c,\\
 \#\{X_n\text{ over this }S\}&=2^c,\\
 \#\{S\text{ attained at }n\}&=2^{F_n-1},\\
 \#\{X_n\text{ attained at }n\}&=2^{F_{n+1}-1}.
\end{aligned}
\tag{GPO.68}
$$

The $2^c$ states have pairwise different $\mathcal Q_1$ maps.

Proof. The supplied recurrence is $T_0=\alpha,T_1=\beta$ and
$T_m=\langle T_{m-1},T_{m-2}\rangle$ for $m\ge2$, with
$\ell(T_m)=F_{m+1}$. Every branch therefore has a unique rank
$m\ge2$, determined by its leaf count, since these counts are
strictly increasing from rank one onward. At rank $m\ge3$ its
child leaf counts $F_m,F_{m-1}$ are unequal. The physical shape
therefore identifies which child has which rank. Rank two is the
sole exception: both children are leaves, one beta and one alpha.
These are precisely $C(S)$. A rank-zero leaf can only arise as
the child of rank two; every other leaf is known beta. It follows
recursively that all remaining ranks, labels and nonterminal local
orientations are determined by $S,n$, and the displayed terminal
choices describe the whole fiber.

The number $c_m$ of rank-two occurrences has
$c_0=c_1=0,c_2=1$ and $c_m=c_{m-1}+c_{m-2}$ for $m\ge3$.
Thus $c_n=F_{n-1}$. There are $F_{n+1}-1$ actual branches, each
born with one wiring bit. A fully labelled physical tree recovers
every one of those bits: unequal-size child subtrees identify the
nonterminal bits, and the beta position identifies each terminal bit.
Conversely every assignment is realized at the corresponding actual
births. Hence there are $2^{F_{n+1}-1}$ labelled trees, without
identifications. Each shape has exactly the $2^{F_{n-1}}$ states
already described, yielding $2^{F_n-1}$ shapes. These counts concern
one joint tree realization per assignment, rather than products of
separately attainable marginals.

For $p\in C(S)$, after one real update,

$$
 P_{\rm next}(paa)=\chi_p,\qquad
 S_{\rm next}=S\ \cup\
   \{qa,qb:q\text{ is a current beta leaf}\}.
 \tag{GPO.69}
$$

Beta becomes a branch and alpha becomes the leaf beta. The new
branch's orientation permutes only its two new leaves, so neither
identity depends on that new bit. The reconstructed current labels
from $(S,\chi)$ give the entire successor set in (GPO.69), hence
all replies, with no missing absent-word cases. Distinct $\chi$
give different replies at some $paa$. This proves both exact
distinction and sufficiency for the full task. $\square$

**Theorem 24.3 (record criterion and finite-preparation obstruction).**
Conditioned on an attained $S$ at $n\ge2$, a deterministic supplementary
record supports exact $\mathcal Q_1$ recovery if and only if it
separates all $2^c$ terminal vectors. For a finite or countable
randomized supplementary kernel $r(a\mid\chi)$ the condition is

$$
 r(a\mid\chi)r(a\mid\chi')>0\quad\Longrightarrow\quad
                 \chi=\chi'.
 \tag{GPO.70}
$$

The minimum supplementary alphabet is $2^c$, attained abstractly by
the $c$ bits. No presence-only finite adaptive preparation ending at
such a current cut can actually acquire a sufficient supplement,
even if the full current $S$ and authentic $n$ are also disclosed.

Proof. Equation (GPO.69) identifies the task classes with the terminal
vectors. One record used on two different classes cannot return both
different exact reply maps. This proves necessity, including (GPO.70)
for positive supports of randomized records. With that support
condition, select the unique vector attached to a reached value and
use (GPO.69), proving sufficiency. Each vector requires a nonempty
disjoint support, giving the alphabet bound. This is an information
criterion, not an acquisition mechanism.

For the acquisition assertion, fix any finite actual controller run
ending at epoch $n\ge2$. Freeze its actions, accessible randomness
if any, and every physical choice before its last update. The beta
leaves split by that update produce exactly the $F_{n-1}$ current
terminal forks. Vary only their actual birth-wiring bits. The whole
current shape, the previous observations and the update's common
acknowledgement remain identical. Every subsequent stationary presence
answer is also identical. Induction on the accessible controller steps
therefore preserves requests, allocations, stopping and all actually
retained accessible fields across these $2^c$ legal realizations.
Their $\mathcal Q_1$ maps differ by (GPO.69). The run cannot return
a sufficient record uniformly. For randomized zero-error procedures,
couple the same independent accessible randomness; the indistinguishable
record laws cannot have the required disjoint supports. More explicitly,
if stopping is random, choose an attained finite epoch and a finite
pre-last-update birth assignment with positive stopping probability
with respect to the accessible randomness.
Such a choice exists for a terminating procedure: there are countably
many finite epochs and only finitely many birth assignments at each.
For every extension by the last update's terminal bits, the event of
stopping there and the retained-record law on that event are identical.
At least two extensions require different outputs, excluding zero error.
This argument
allows arbitrary finite earlier preparation and adaptive updates; it
is not a finite search limit. The excluded cuts $n=0,1$ have no such
residual and are not used. $\square$

## 25. Sharp historical calibration and renewed current residual

**Theorem 25.1 (one actual update calibrates the preceding boundary).**
Suppose the actual current $S$ of Definition 24.1 has been acquired
and retained stationarily. On the same source perform one completed
update and query $paa$ once for each $p\in C(S)$. The acquired bits
recover the entire **old** labelled physical tree and its old local
semantic address adapter. For this calibration segment the jointly
attained prices are

$$
 U_{\rm updates}=1,\qquad Q=c,\qquad
 W=\sum_{p\in C(S)}(|p|+2),\qquad
 M_{\rm addr}=\max_{p\in C(S)}(|p|+2).
 \tag{GPO.71}
$$

Each of the three Read coordinates is sharp among protocols with
that same acquired $S$, common initialization apart from its data,
no extra old-label information, exactly one actual update and full
old-state recovery. After calibration the newest current state still
has $F_n$ unobserved terminal bits.

Proof. The paid bits are exactly $\chi_p$ by (GPO.69). Theorem
24.2 reconstructs all old labels and nonterminal orientations;
the terminal bits fix the remaining old orientations. Composing
those local correspondences along an old semantic address gives its
old physical address. This is retained historical data, not a new
mutable old register.

For lower bounds fix an arbitrary complete run and flip only one
old $\chi_p$, holding the acquired $S$ and other old choices fixed.
All pre-update presence replies agree. After the one update, support
can differ only strictly below $pa$ or $pb$, inside the incomparable
$p$-cone. Correct old-state output forces a first different Read,
and its length is at least $|p|+2$. The same first-difference
argument can be applied separately to each $p$ on that one fixed
run. Their selected occurrences are distinct, since the terminal-fork
addresses are prefix-incomparable. Summing, counting and taking their
maximum gives all three lower bounds of (GPO.71), jointly attained
by the stated queries. Adaptive queries and additional pre-update
Reads cannot avoid them. The lower bound is scoped to this segment
and these prerequisites; it does not claim optimal cost of acquiring
$S$ or an optimum allowing additional updates or supplementary data.

The update splits the $F_n$ beta leaves at epoch $n$, creating
$F_n$ new terminal forks. Their new wiring bits affect no presence
answer yet. Varying just those choices leaves the calibration queries
and all current stationary observations unchanged, exactly as in
Theorem 24.3. Thus the decoded old state does not remove the newest
residual. Repetition acquires successive historical states while
continually creating this current gap. $\square$

**Proposition 25.2 (independent views and same-source resources).** In
the known-seed model, physical incidence $S$ and terminal antichain
$\partial S$ determine one another by maximality and prefix closure.
For $n\ge2$ either determines $n$ by its Fibonacci leaf count.
They do not determine $\mathcal Q_1$ without the residual of Theorem
24.2. Time $n$ alone does not determine physical incidence for
$n\ge3$: exchanging the unequal root-child shapes gives distinct
physical supports at the same count. The semantic tree $T_n$ is
known from time and the alpha seed, and must be distinguished from
all of these physical recovery statements.

After the actual calibration, either incidence or boundary, together
with the same acquired $\chi$ bits, reconstructs the same old
labelled state; (GPO.69) also gives the correct current unlabelled
state. These routes agree because they use the same old tree and
actual paid replies. Arbitrary physical Reads and stop on that
unlabelled state have the computed replies and outputs. A further
update requires the new current labels and therefore the fresh
residual; the old recovered adapter is not automatically a current
adapter below newly created branches. No cloned historical callable
root or closed transition of the newest labelled state is obtained.

For a concrete acquired prerequisite, the scan of (GPO.66) at epoch
$n$ has exactly $N_n=2F_{n+1}-1$ calls,
$W_{\rm shape}=\sum_{q\in S}(|q|+1)$ and maximum $H(S)+1$.
List its terminal forks by paid local computation and retain their
actual addresses. This scan followed by calibration has, on one run,

$$
 Q=N_n+c,\qquad W=W_{\rm shape}+\sum_{p\in C(S)}(|p|+2),
 \qquad M_{\rm addr}=\max\{H(S)+1,\max_{p\in C(S)}(|p|+2)\},
 \qquad U_{\rm updates}=1.
 \tag{GPO.72}
$$

Its initial scan is an upper bound, not an acquisition optimum. The
source already has $F_{n+1}$ leaves and $N_n$ nodes; the update
allocates exactly $2F_n$ new nodes and $2F_n$ child links, and makes
$F_n$ actual wiring
choices, in addition to tag overwrites and traversal. Internal update
work, hidden writer, root/grants, authentication, literal construction,
stack and address storage, fork extraction, retained bits, reconstruction,
outputs and retention lifetime all retain their actual prices. The
$c$-bit supplement minimum counts a data alphabet, not total memory,
hardware, energy or physical duration. A larger backing or a finite
program cannot read the missing latest wiring through this interface.

## 26. Local-port suppliers, task boundaries and remaining recovery

The common locally wired service in §22 supports two different
source-specific deductions. For arbitrary authentic originals, the
increment is exact local image recognition, physical-order ancestor
acquisition, the complete semantic fiber and its persistent future
ambiguity. For the known alpha seed, it is the exact terminal residual,
its attained shape/state counts, the current-cut obstruction after
every finite preparation, and the sharp one-update historical remedy.
GPO Proposition 6.5's old root-swap pair is a supplier boundary, not
the content of these results. The two tasks are not identified: one
can know $T_n$ and still lack its physical current continuation map.

| Supplier | Use and precise boundary |
| --- | --- |
| ABT12.1, (ABT.30)–(ABT.31), ABT39.1–39.2 | Ordered two-step code inversion, leaf-growth separation and the authentic sharp interval. The new recognizer admits both mixed orientations but checks the exact cherry, and proves the unordered inverse; broad-interval history ambiguity is not removed. |
| GenealogicalFiberTransport and its owning Scribe; pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, `FreeMagma.of/mul/lift` | The same free ordered nonassociative source, homomorphic substitution and composition. They do not acquire physical local frames. |
| ActualFibonacciSupportChain and its owning Scribe, including proof-local recurrence; FiniteSourceMass | The actual Fibonacci recurrence, literal address and guarded support conventions. The new physical correspondence is local, not the ordered semantic interface of these suppliers. |
| NativeErasedSupportKernels and its owning Scribe, including `root_reflection`, `erased_reply_presence`, `two_step_prefix_kernel`, `even_epoch_support_kernel` | The old erased/support kernels retain the same ordered addresses. Their ordered decoder cannot be transported through hidden local swaps without the correspondence supplied in §§22–23. |
| NativeFullSourceProducer and its owning Scribe, including `sourceControl`, `traverse`, `stationary`; NativeSerialMachine | Source-blind acquired-stack assembly and reached-prefix control on one register. Our presence scan tests one child per confirmed node instead of borrowing its hidden full reply. |
| [Native Clocked Recovery and Order](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), §§2,5,8; [Native Paid View Conversion](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md), §§1–2,10 | Their installed deterministic source, order, clocks, completed acquired data, ownership and permitted serializers remain premises. No serializer supplies unobserved fresh actuator inputs. |
| [Native Callable Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md), Definitions 2.1–2.4, §6 and Theorem 11.1 | Its initialized lawful image, actual control/record fields, rights and priced structural basis are retained. Its four-view kernels do not assert that presence acquires the hidden choices of Definition 22.1. |

Kersting–Fischer, [*Measuring tree balance using symmetry nodes*,
arXiv:2105.00719v2](https://arxiv.org/abs/2105.00719v2), §2,
Definition 2.1 and Lemma 3.2, supplies rooted unordered isomorphism,
symmetry-node language and the additive nonsymmetry count. Its fully
balanced zero case concerns uncoloured shapes. Equation (GPO.65) keeps
leaf colours, and the elementary ordered-representative count was proved
explicitly for that coloured case; no new general tree-counting principle
is claimed.

Nilsson, [*On the Entropy of Random Fibonacci Words*,
arXiv:1001.3513v1](https://arxiv.org/abs/1001.3513v1), Introduction
and “Inflated Words”, already treats $0\mapsto1$ and
$1\mapsto01$ or $10$, with $0=\alpha,1=\beta$, and the overlap
of inflated word sets. Thus neither the leaf rewriting options nor
random substitution or word entropy is new here. Our model assigns
no probability and retains nonassociative branching and persistent
node incidences. Different tree choices can flatten to the same word;
Nilsson's word counts are not (GPO.68). Ordered ranked trees and their
child-number navigation in Engelfriet–Inaba–Maneth, §2 of [TWT],
likewise supply an order rather than acquire these local frames.
The finite-state identification comparison in §18 retains its own
finite transition system and observable-response assumptions. The
obstruction here is proved directly for every finite preparation of
the actual unbounded growing tree, without transporting a finite-state
identification theorem. These are repo-derived source-specific proofs,
with no universal alpha/beta obstruction, global novelty or additional
Lean certification claim.

Space is rooted incidence, not a physical metric; time is completed
substitution count, not physical duration or the full chronology.
The local theorems neither remove authentic advice and root/grant
premises nor install a birth-wiring sensor or an endogenous future-wiring
law. The global results in §§1–21 retain their stronger persistent
global correspondence and their exact acquisition tasks. The current,
original-semantic and historical claims above retain their separate
domains. The original fixed-$G_{\rm gc}$, original-Q, parked-consumer
and unchanged-initialization problems, and the PR57/PG/NCR/PVC/Atlas
interfaces, are not repaired by a change of model. No common actual
atomic/quantum/continuous initialization and action map, time-only
inverse, unrestricted four-way recovery or minimum total-resource
implementation is supplied. The bounded acquisition, obstruction and
historical results leave those programme-level directions unresolved.

## 追加锚（本行以下为增补区）

## 27. An autonomous source-owned birth law on the local physical ports

**Definition 27.1 (the alternative law-bearing source).** Retain the
actual alpha initialization and the local service of Definitions 22.1
and 24.1. In particular there is one actual mutable root, persistent
physical child links named $a,b$, total paid literal presence
$\operatorname{Read}(w)=\mathbf1_{w\in\operatorname{Pos}(X)}$ on
all finite physical words, and only the legal serial localStep,
applyRho and stop operations. Updates have their original common
acknowledgement. Labels, writer, allocator, generator state, work and
physical durations supply no additional observation. Actual root
binding, grants, exclusive serialization, reliable completion and
sufficient growing backing are premises of this service, with their
own acquisition, installation and lifetime charges. No reset, cloned
root, semantic-port sensor or read of a private generator is added.

The additional source premise is the following actual actuator rule.
Before update $t$, enumerate the beta leaves of the old physical tree
by lexicographic order of their addresses, with $a<b$. These addresses
are pairwise prefix-incomparable. The actuator really commits their
births in that order; it updates each old leaf once and does not visit
a newborn leaf during that update. At its $j$th birth since the alpha
initialization it consumes the next bit $z_j$. If $z_j=1$, the new
beta child is at $a$ and alpha at $b$; if $z_j=0$, their positions
are reversed. Old branches and their links remain in place.
Alpha-to-beta changes create no birth and consume no bit.

The stream $z=(z_1,z_2,\ldots)$ is produced by an autonomous
source-owned generator. Its initial state and parameters are fixed
before the first birth. It advances exactly once per birth, with no
other input, reset or change of source; presence queries, local
computation, waiting and stopping do not advance it. The public
chronological ordering is a condition on actual births, not merely a
chosen sorting of semantic occurrences. Serial update remains the
observer's action; no interrupt or observation inside it is provided.

Two alternative authentic public promises will be considered
separately in Definitions 29.1 and 30.1. Their respective bounds, this
autonomy rule, the chronological rule and alignment to the first birth
are supplied authentic premises. Coefficients, seed and private machine
data remain initially unknown. None of those premises is certified by
a finite observed prefix. This is a named alternative to arbitrary
birth wiring, rather than an inference about the source of §§22–26.

**Proposition 27.2 (the physical birth clock).** Write $F_0=0,F_1=1$
and $F_{i+2}=F_{i+1}+F_i$. After $n$ completed updates from alpha,
the number of births and the number belonging to updates strictly
before the most recent one are, for $n\ge2$,

$$
 B_n=\sum_{t=2}^nF_{t-1}=F_{n+1}-1,\qquad
 v_n=B_{n-1}=F_n-1,\qquad B_n-v_n=F_{n-1}.
 \tag{GPO.73}
$$

Birth $j$, $1\le j\le B_n$, has an actual update index $t_j$
and parent address $p_j$. The chronological list is ordered first
by $t_j$ and then by physical lexicographic order of $p_j$.

Proof. At cut $e\ge1$ the alpha and beta leaf counts are
$F_{e-1}$ and $F_e$: replacement sends $(A,B)$ to $(B,A+B)$,
starting with $(0,1)$ at cut one. Thus update $t\ge2$ splits
$F_{t-1}$ old beta leaves. Summing gives the first identity; the
last update's batch gives the other two. Definition 27.1 makes the
displayed order the order of actual events. The update index is counted
from the known actual initialization and completed acknowledgements;
it is not an exposed hidden epoch or physical time coordinate. $\square$

## 28. Exactly which ordered birth prefix the current incidence exposes

**Definition 28.1 (independent incidence, boundary and birth time).**
At a completed update cut $n\ge2$, let $S_n$ be the set of actual
physical root-to-node words and let $\partial S_n$ be its terminal
antichain. They discard leaf labels and generator data. Independently,
let

$$
 \mathcal T_n^{\rm birth}
  =\bigl(n;(t_j,p_j,z_j)_{1\le j\le B_n}\bigr)
 \tag{GPO.74}
$$

be the ordered marked word of actual beta-split events. Its mature
restriction $\mathcal T_n^{<}$ keeps only $j\le v_n$, namely births
before update $n$. These are observations of the source process, not
additional accessible read ports or unrestricted observer histories.
There are no localSteps, query words, delays or writer events in these
temporal observations. In particular a reconstruction of (GPO.74)
will reconstruct this particular chronology only.

**Theorem 28.2 (exact ordered-prefix correspondence).** In Definition
27.1, for every $n\ge2$, the following statements hold without any
finite-law promise.

1. $S_n$ and $\partial S_n$ determine one another and determine $n$.
2. For two streams at that cut, equality of physical incidence is
   equivalent to equality of their first $v_n$ birth bits. There are
   explicit finite maps between $S_n$ and $(n,z_1\cdots z_{v_n})$.
   These maps also recover exactly $\mathcal T_n^{<}$.
3. The full labelled physical state $X_n$ is equivalent to
   $(n,z_1\cdots z_{B_n})$. Conditional on $S_n$, only the newest
   batch of $F_{n-1}$ bits remains to specify that state.

Proof. Prefix closure of the terminal words gives $S_n$; maximality
in $S_n$ gives its terminals. The leaf count is $F_{n+1}$ by
Theorem 24.2. This sequence is strictly increasing for $n\ge1$,
so within $n\ge2$ it determines $n$.

A branch born at update $t$ has, at cut $n$, the shape of a rank
$m=n-t+2\ge2$ Fibonacci subtree. Its number of descendant leaves
is $F_{m+1}$. The rank is therefore determined by this number, and
so is its actual birth update $t=n-m+2$. When $m\ge3$, the
child descended from its original beta has $F_m$ leaves and the
child descended from its original alpha has $F_{m-1}$ leaves.
These are unequal. The position of the larger child thus gives the
actual birth bit, even if either descendant was subsequently expanded
many times. The rank-two branches are exactly the newest cherries;
their children both have one leaf, so their bits are invisible.

Consequently $S_n$ determines the bit and update index of every old
branch, at its actual persistent address. Ordering these branches
by recovered update index and then physical parent address yields
exactly $z_1,\ldots,z_{v_n}$ in Definition 27.1's actual birth
chronology. This proves recovery of the mature marked trace as well;
it does not sort by an unavailable semantic frame.

Conversely a prefix of length $v_n=B_{n-1}$ determines the full
labelled physical tree $X_{n-1}$ by forward replacement from alpha,
using exactly the specified chronological assignments. Its beta leaves
determine $S_n$ by (GPO.69), independently of the newest birth bits.
This proves both implications of assertion 2. A full labelled $X_n$
also reveals each rank-two bit by its beta child's position. The same
rank argument then recovers every $z_j$ through $B_n$. Forward
replacement proves the reverse implication of assertion 3. All these
algorithms manipulate finite trees and lists. Their existence is not a
claim that the observer has already scanned or acquired $S_n$.
$\square$

At a fixed $n$, this identifies geometric information with an ordered
prefix of an actual autonomous law. It is stronger than counting
$2^{v_n}$ possible shapes, which alone would provide neither the
ordering nor an acquisition method. The proof uses the known alpha
origin and the actual chronological actuator rule. It supplies no
inverse for an arbitrary original tree or an arbitrary assignment of
unrecorded actuator choices.

## 29. An authentic recurrence-order bound, including singular sources

**Definition 29.1 (the homogeneous binary class).** For a public
integer $d\ge0$, let $\mathscr R_d$ contain every binary stream
$s=(s_0,s_1,\ldots)$ for which there exist $0\le r\le d$ and
$c_0,\ldots,c_{r-1}\in\mathbb F_2$ satisfying

$$
 s_{i+r}=\sum_{j=0}^{r-1}c_j s_{i+j}
       \quad\text{for every integer }i\ge0.
 \tag{GPO.75}
$$

The birth convention is $z_j=s_{j-1}$. At $r=0$, (GPO.75)
means the identically zero stream. For $r>0$, the initial $r$ bits
are arbitrary. No coefficient is required to be nonzero, no state
transition must be invertible, and the presentation need not be minimal.
Lower orders, zero streams, finite transients and eventually periodic
streams are all included. The authentic promise is recurrence from
index zero with this bound; an unspecified recurrence beginning only
after an unbounded transient is a different class.

**Lemma 29.2 (the classical finite separation in this domain).** Any
two streams of $\mathscr R_d$ agreeing in their first $2d$ output
bits agree at every index. From such a prefix there is a terminating
finite algorithm producing a generator for the actual full stream.
It need not recover its private coefficients, register or seed
presentation.

Proof. For a stream of order $r$, let $E$ be forward shift on
one-sided sequences and put
$p(E)=E^r-\sum_{j<r}c_jE^j$. The monic polynomial $p$
annihilates that stream at every nonnegative index. If $q$ similarly
annihilates the other stream of order $r'$, commuting shifts make
$p(E)q(E)$ annihilate their difference. This polynomial is monic of
degree $r+r'\le2d$. A sequence satisfying that homogeneous forward
recurrence and having its first $r+r'$ entries zero has every entry
zero, by induction. Agreement through $2d$ therefore suffices. This
argument includes degree zero, zero trailing taps and singular shifts;
it never runs the recurrence backwards.

For an explicit algorithm when $d>0$, pad any order-$r$ annihilator
to order $d$ by multiplication by $E^{d-r}$. Enumerate all $2^d$
coefficient rows for a monic order-$d$ recurrence. Give each candidate
the observed first $d$ bits as its initial seed, generate its first
$2d$ bits, and retain the first candidate matching the observed word.
At least the padded actual recurrence passes. Every passing candidate
belongs to $\mathscr R_d$, so the separation just proved makes its
entire output equal to the actual stream. A fixed enumeration makes
the returned behavioral description canonical. At $d=0$ simply
return the known zero generator. All operations are finite binary
operations; no exact-real comparison or source oracle is involved.

The separation and shift-register synthesis are classical suppliers,
not new identification results. Massey, *Shift-Register Synthesis and
BCH Decoding*, §II–III, explicitly permits a zero final tap and gives
the $2L$ synthesis boundary; his §IV distinguishes finite transient
numerator degree from denominator degree. Reeds–Sloane, §2 of
*Shift-Register Synthesis (Modulo m)*, retains that finite-length
convention in its broader ring setting. Here only the binary field
and the all-index bounded class (GPO.75) are used. The direct monic
argument verifies their applicability to the stated nonminimal and
singular domain. $\square$

**Lemma 29.3 (sharp uniform prefix separation).** For $d\ge1$ and
every $0\le v<2d$, there are two members of $\mathscr R_d$
which agree at indices $0,\ldots,v-1$ and differ at index $v$.

Proof. If $v<d$, compare the zero stream with the single impulse
$s_i=\mathbf1_{i=v}$. That impulse satisfies the all-zero-coefficient
recurrence of order $v+1\le d$.

If $d\le v<2d$, write $r=v-d$, so $0\le r<d$.
Compare the periodic stream $s_i=\mathbf1_{i\equiv r\pmod d}$
with the single impulse at $r$. The first satisfies
$s_{i+d}=s_i$; the second has order $r+1\le d$. Before index
$v=r+d$ their sole one is at $r$, and at $v$ only the periodic
stream is one. Thus they have exactly the required common prefix.
The transient witness is deliberately included: excluding it would
silently change the class. $\square$

An order bound $d$ is not a state-count bound $d$. The usual binary
order-$d$ register can have $2^d$ states. Conversely a unary finite
output machine need not have the same minimal linear order as its
number of states. Lemma 29.2 identifies an output law; different
private presentations of that law remain indistinguishable here.

## 30. A separately bounded autonomous unary Moore class

**Definition 30.1 (the unary Moore promise).** For a public integer
$K\ge1$, let $\mathscr M_K$ consist of the streams

$$
 s_i=g(f^i(q_0)),\qquad i\ge0,
 \qquad \varnothing\ne Q,\quad |Q|\le K,
 \quad f:Q\to Q,\quad g:Q\to\{0,1\}.
 \tag{GPO.76}
$$

The machine emits $g(q)$ and then changes to $f(q)$ at each birth.
The set, transition, output map and initial state are unknown. Unreachable
states, nonminimal presentations, constant outputs, transient paths and
singular transitions are allowed; strong connectivity is not assumed.
The bound is on this autonomous unary source, not on the growing tree,
the observer or the full service runtime.

**Lemma 30.2 (the classical $2K-1$ separation).** Two members of
$\mathscr M_K$ agreeing in their first $2K-1$ outputs agree forever.
A finite observed word of that length, under the authentic promise,
yields an effective generator for that behavior.

Proof. Take the disjoint union of their state sets, with at most
$2K$ states. Let $R_l$ equate states whose first $l$ outputs agree.
Then $R_1$ is the output partition and

$$
 q\ R_{l+1}\ q'\quad\Longleftrightarrow\quad
     g(q)=g(q')\ \text{ and }\ f(q)\ R_l\ f(q').
 \tag{GPO.77}
$$

These partitions refine. If a refinement stops, (GPO.77) makes it
stable under $f$ and all subsequent refinements stop too. If the
initial states have different infinite outputs, the disjoint union
has at least two output classes in $R_1$. There can be at most
$2K-2$ further strict refinements, since each increases the number
of classes. Thus $R_{2K-1}$ is already the infinite-output relation,
and those states differ within $2K-1$ observations.

Enumerate labelled sets of sizes $1,\ldots,K$, all their transitions,
binary outputs and initial states, in a fixed finite order. Test their
first $2K-1$ outputs and choose the first passing machine. The actual
presentation has an isomorphic labelled candidate, so one passes.
The separation proves equality of its entire stream with the actual
one. There are
$\sum_{r=1}^K r^{r+1}2^r$ candidates before any removal of duplicate
presentations. This deliberately elementary finite algorithm claims no
optimal running time or recovery of the actual state names.

This is Moore's finite partition/direct-sum identification argument:
*Gedanken-Experiments on Sequential Machines*, Theorems 6–7. His
$2n-1$ comparison uses output observations, including the initial
output, rather than $2n-1$ transitions after an uncounted initial
observation. It does not require the strong connectivity assumed by
some later theorems in that source. Formula (GPO.76) fixes the unary
and emission conventions needed here. $\square$

**Lemma 30.3 (unary sharpness at every shorter length).** For every
$K\ge1$ and $0\le v<2K-1$, two streams of $\mathscr M_K$
agree at indices below $v$ and differ at $v$.

Proof. For $v\le K-1$, use the zero stream and $0^v1^\infty$.
The latter uses a path of $v$ zero-output states into a one-output
fixed point, for $v+1\le K$ states. This covers $K=1,v=0$.

For $K\le v\le2K-2$, put $r=v-(K-1)$, so
$1\le r\le K-1$. One source is a $K$-cycle with its unique one
at phase $r$, starting at phase zero. The other has one initial
zero-output transient state, followed by a $(K-1)$-cycle with its
unique one positioned to first occur at index $r$. Both use at most
$K$ states. Both first emit one at $r$. The second's next one is at
$r+K-1=v$, whereas the first's next one is at $r+K=v+1$.
There is no other one before $v$, so the streams agree on precisely
the asserted prefix and differ at its next bit. These are unary
witnesses; multi-input sharpness examples are not being substituted
for them. $\square$

## 31. Current labels, the original mature-cut task and all finite futures

**Definition 31.1 (the three readiness questions).** Fix one authentic
class $\mathscr C=\mathscr R_d$ or $\mathscr M_K$ and the actual
common service of Definition 27.1. At a completed cut $n\ge2$,
consider three recovery tasks from the current incidence, or equivalently
its terminal boundary:

- recover the whole current labelled physical tree $X_n$;
- answer the original $\mathcal Q_1$ of Definition 24.1 at this
  very cut, before making its next update;
- supply the complete finite future presence/update behavior at this
  cut: for every finite serial word of literal presence queries and
  real updates, give all presence replies and the resulting physical
  supports and labelled trees, including absent-word replies. Equivalently
  serve these data along every finite adaptive policy using only actual
  replies and its independently supplied local inputs.

The last task has no bound on the chosen finite number of updates or
query-word length. It includes every such finite continuation of this
same source, rather than a separately chosen law for each experiment.
LocalStep and stop have their usual source-free effect. The specified
successor is the physical tree; private generator state names, its
implementation work, observer program counter, hidden writer and durations
are not additional coordinates of this behavioral task. Equality of
private presentations is not required. Actual execution and payment of
operations remain distinct from a hypothetical evaluator's prediction.

For an attained visible word $w=z_1\cdots z_{v_n}$, write
$\mathscr C[w]$ for its compatible infinite streams. Individual
readiness means that the desired answer is constant over this fiber.
Uniform readiness at $n$ means that one effective recovery rule works
for every source in the promised class at that cut.

**Theorem 31.2 (individual criteria and sharp class-wide thresholds).**
The individual current-label and $\mathcal Q_1$ criteria are both
agreement of all streams in $\mathscr C[w]$ through $B_n$. The
individual complete-future criterion is that $\mathscr C[w]$ contain
only one infinite output stream. For the class-wide questions, each of
the three tasks in Definition 31.1 is uniformly ready exactly under
its separately stated condition

$$
\begin{array}{c|c}
 \text{authentic source class}&\text{necessary and sufficient condition at }n\ge2\\\hline
 \mathscr R_d&F_n-1\ge2d\\
 \mathscr M_K&F_n-1\ge2K-1.
\end{array}
 \tag{GPO.78}
$$

The $d=0$ condition is zero and holds at every such cut. At a
shorter prefix the failure is a uniform class failure; particular
fibers may be ready earlier. These statements assert neither minimum
paid Read count with unknown coefficients nor total-resource minima.

Proof. Theorem 28.2 identifies the current-label fiber with its prefix
through $B_n$. Once $S_n$ is fixed, Theorem 24.2 and (GPO.69)
identify the $\mathcal Q_1$ classes with those very current labels:
a change of a newest terminal bit changes the reply at $paa$ for
that cherry. This proves both individual criteria.

If a compatible fiber has one infinite stream, finite forward replacement
computes every finite continuation in Definition 31.1. Conversely suppose
two compatible streams first differ at a birth $j>v_n$. Before this
birth their physical labelled histories agree, hence its actual parent
address and chronological position agree. If the birth is among the
newest batch, its difference is still invisible now but becomes a
presence difference after one more update at a word $paa$ in its
parent cone. If it is later, perform enough updates to reach its
birth and then one further update. Such an update exists since
$B_e\to\infty$. The same argument makes a finite presence query
distinguish the continuations. Differences in other later birth bits
cannot change that witness: the immediate successor support of a cherry
does not depend on the new orientations. Thus equality of complete
future behavior is exactly equality of the infinite stream within
this fixed current-incidence fiber. The labelled successor coordinate
in the task is consistent with this same criterion.

If $v_n\ge2d$ or $v_n\ge2K-1$, apply respectively Lemma 29.2
or 30.2 to its initial required prefix. Every compatible stream is the
same behavior. The finite synthesis and physical simulation therefore
solve all three questions. The incidence-to-prefix map of Theorem 28.2
provides a finite effective recovery on the attained incidence image.

For necessity, let $v=v_n$ be below the relevant threshold. Use
Lemma 29.3 or 30.3 to choose two lawful streams agreeing in the first
$v$ bits but differing in the next one. They give exactly the same
$S_n$ by Theorem 28.2. Birth $v+1$ is the first birth of the
newest batch, which is nonempty for $n\ge2$. Its differing bit
gives different current labels and different $\mathcal Q_1$ replies
by (GPO.69), and hence different finite future behavior. A single
recovery rule from this incidence cannot work for both. When $d=0$
there is only the zero stream and no such lower-bound case.
This proves the exact class-wide conditions, separately for each task.
$\square$

**Corollary 31.3 (past acquisition cannot beat the update barrier).**
For a common initially source-blind observer in Definition 27.1,
any finite accessible trace ending at cut $n$ is a function of the
actual bits through $v_n$, its public inputs and its accessible
independent randomization. More stationary Reads, arbitrary finite
local computation and retention cannot give class-uniform zero-error
readiness before the appropriate threshold in (GPO.78).

Proof. Every earlier cut $e\le n$ has support determined by the
first $v_e\le v_n$ bits; cuts zero and one are fixed. For a
fixed common acquired history the next local action and query word
are the same, presence replies coincide, and update acknowledgements
are constant. Induction on actual accessible steps proves the trace
assertion, including every requested address, local allocation and
retained field. Couple the same accessible randomness if present.
The witness pairs used in Theorem 31.2 then have identical accessible
record laws but require different exact answers. This is an information
barrier for this native service, not a bound on search effort.
$\square$

## 32. Public coefficients and the authentic-bound boundary

**Theorem 32.1 (the smaller seed-only benchmark).** Suppose instead
that the source supplies authentic public $r\ge0$ and the entire
coefficient row of (GPO.75), with only the arbitrary initial $r$ bits
unknown. No invertibility or minimality is assumed. For this class,
all three class-wide readiness conditions are exactly

$$
 v_n=F_n-1\ge r\qquad(n\ge2).
 \tag{GPO.79}
$$

Reading its first $r$ birth bits suffices to install the known
recurrence with the earned seed. When $r=0$ no read is required.
The number $r$ here is the supplied presentation length, not an
inferred private minimal order.

Proof. The first $r$ bits and the public row determine every later
bit by forward induction. For $v<r$, choose two initial seeds
agreeing below $v$ and differing at index $v$, extending both by
that same public recurrence. Both are lawful regardless of its zero
coefficients. At cut $n$ with $v_n=v$, Theorem 28.2 and (GPO.69)
give identical incidence but different current labels and $\mathcal Q_1$.
The same difference also distinguishes finite futures. This proves both
directions, with the zero-order singleton treated separately.
$\square$

The benchmark supplies coefficients as authentic advice and only learns
the seed. It is not the unknown-coefficient theorem with $2d$
replaced by $d$, and it is not a claim that geometry authenticates the
coefficient presentation. Its acquired-read schedule is the same
construction below with $m=r$.

**Theorem 32.2 (absence of a bound is a different obstruction).**
Replace either bounded promise by merely membership in
$\bigcup_{d\ge0}\mathscr R_d$ or
$\bigcup_{K\ge1}\mathscr M_K$. No finite presence-only
preparation, with common initially source-blind initialization, can
return class-uniform exact readiness at a mature current cut $n\ge2$
for any of the three tasks. There is also no finite-prefix test that
authenticates the bound or autonomy premises against unrestricted
source continuations.

Proof. Every finite binary word $w$ has two eventually zero extensions
$w0^\infty$ and $w1 0^\infty$. They agree on that word and
differ on its next bit. Every finite-support stream is annihilated by
$E^R$ for a sufficiently large $R$, so both extensions are in the
unbounded recurrence union. Each also has a finite unary path through
its finite nonzero prefix into a zero-output fixed point, so both are
in the unbounded Moore union. At any attained cut, take $w$ to be
its whole visible prefix. Theorem 28.2 gives the same current
incidence for these two extensions and (GPO.69) gives different
$\mathcal Q_1$ answers. Corollary 31.3 makes their entire finite
accessible preparation identical. A terminating deterministic procedure
therefore cannot be correct on both. A zero-error randomized procedure
cannot evade this: choose an attained finite epoch and a finite visible
word on which its finite termination event has positive probability.
Such a choice exists by countability if termination occurs almost surely.
The two extensions preserve that event and its accessible record law
but require different answers.

Likewise, any finite observation is consistent with a generator or
actuator which follows the observed prefix and changes afterward.
To see the bound-specific issue even for a lawful bounded prefix,
keep that prefix and any desired sufficiently long continuation and
then insert a later deviation; an unrestricted actuator can do this
without changing any observed reply. A generator with a larger finite
presentation can realize any prescribed finite extension followed by
zeros. Each bounded class contains only finitely many distinct streams:
there are finitely many bounded coefficient/seed rows or labelled Moore
presentations. A sufficiently long binary extension of any fixed observed
prefix can therefore be chosen different from all their continuations,
and then continued by zeros. This gives an actual unbounded-class
alternative outside the claimed bounded class. Thus finite agreement is
not a certificate of the authentic class membership, chronological
installation or absence of unseen inputs.
These are hypotheses of the bounded results, not empirical conclusions
of their synthesis algorithm. Moore's Theorem 2 already supplies the
general missing-state-bound warning; the argument here discharges it
on this actual growing-tree observation fiber. $\square$

The obstruction concerns zero-error finite readiness in this information
interface. It says nothing about statistical identification under a
specified prior, a promise with additional certificates, finite-horizon
approximation or another physical sensor. The arbitrary-wiring results
of Theorems 23.1 and 24.3 remain exactly valid. In particular one
cannot apply the bounded theorem to their sources without the new
source-owned law and public chronology premises.

## 33. An internal paid acquisition with a sharp update deadline

**Definition 33.1 (the installed source-blind acquisition program).**
Let

$$
 m=2d\quad(\mathscr R_d),\qquad
 m=2K-1\quad(\mathscr M_K),\qquad
 m=r\quad\text{for the public-row benchmark}.
 \tag{GPO.80}
$$

Assume the actual common initialization, service binding and authentic
promise of Definition 27.1, with the appropriate public finite integer
input. The program begins with no source bit, an empty acquired word,
the actual update counter zero and the known alpha seed. Its local
working registers, tree/list workspaces, literal buffers and retention
are ordinary accessible owned backing. Its finite instruction scheme
is independent of the unknown stream; loop counters and data capacity
may grow with the supplied bound and run. This specification is an
ideal native local program, not a claim of physical installation or a
new Lean implementation.

For $m>0$, repeatedly execute real updates. At cut $s\ge3$, list
in actual chronological order the births of update $s-1$ and, until
$m$ bits have been obtained, make one stationary literal query
$\operatorname{Read}(p_j aa)$ for each such birth. Append its actual
reply as $z_j$. If the target count is not reached, finish that whole
batch before the next update. When $m$ is reached, stop issuing source
updates, synthesize the canonical behavioral generator of Lemma 29.2
or 30.2, or use the public row, and compute the current labelled tree
and generator phase. The final partial batch need not be read to its
end. All computation, copying and output take their own localSteps.

**Theorem 33.2 (attained prefix acquisition and mature readiness).**
For $m>0$, the program in Definition 33.1 is an actual finite
acquisition on its one source. It ends ready for all three tasks at

$$
 N(m)=\min\{n\ge3:F_n-1\ge m\},
 \tag{GPO.81}
$$

with jointly attained read and update coordinates

$$
\begin{aligned}
 Q&=m,& U&=N(m),\\
 W&=\sum_{j=1}^m(|p_j|+2),&
 M_{\rm addr}&=\max_{1\le j\le m}(|p_j|+2),\\
 W&\le m(N(m)-1),&M_{\rm addr}&\le N(m)-1.
\end{aligned}
 \tag{GPO.82}
$$

No full-support scan or source-law output is an uncounted prerequisite.
Among preparations seeking class-uniform zero-error mature readiness,
$N(m)$ is the sharp worst update deadline for the appropriate class.
The read count and literal coordinates in (GPO.82) are attained upper
bounds for this construction; no unknown-coefficient minimum-Read or
total-resource optimum is asserted.

Proof. A birth at parent $p_j$ in update $t_j$ is a terminal cherry
at that cut. After one further update, (GPO.69) gives exactly

$$
 \operatorname{Read}_{t_j+1}(p_j aa)=z_j.
 \tag{GPO.83}
$$

The next update's fresh orientations affect neither this reply nor the
old parent address. All queries of its batch are stationary at that
same cut. This is the actual one-update read of Theorem 25.1,
applied to known birth parents rather than to a prior full shape scan.

The required parents are internally available. For the first batch,
the only birth of update two is at the known root. Inductively, before
processing the batch at cut $s$, every earlier mature batch has been
fully acquired unless this is the final batch. Those earlier bits
extend through $B_{s-2}$ and reconstruct the labelled physical
$X_{s-2}$. Its beta-leaf addresses are precisely the parents of
births in update $s-1$, and their physical lexicographic order is the
actual order. Finite local traversal of this earned tree therefore
constructs each literal $p_j aa$ before requesting it. No unknown
subtree, hidden label or oracle enters a control operand. During the
final partial batch the whole parent list was already determined by
these earlier bits.

Each update releases exactly the preceding batch for (GPO.83).
Through cut $n$ the total available prefix is $v_n$. Consequently
the first cut reaching $m$ is exactly (GPO.81), and the procedure
makes exactly the first $m$ queries of (GPO.83). Synthesis from these
bits determines the entire behavior by the corresponding lemma.
Generate the remaining bits through $B_N$, including unread bits in
the final mature batch and the newest batch, and reconstruct the actual
$X_N$. These generated values are justified predictions from the
authentic law and actual acquired prefix, not additional paid replies.
This establishes readiness and finite termination on each promised input.

There are exactly $N$ actual updates from alpha and $m$ reads.
A birth parent in update $t$ has depth at most $t-2$:
starting with the first root birth at $t=2$, no update increases
a descendant depth by more than one. Hence each query of that birth
has length at most $t$. Every read birth satisfies $t+1\le N$,
proving the last two bounds in (GPO.82) and all exact sums there.
All traversal, literal writing, candidate tests and reconstruction remain
charged local work.

For sharpness against adaptive stopping, a single difficult source
must remain unready at every earlier possible mature cut. In
$\mathscr R_d$, $d\ge1$, choose the periodic stream whose ones
are exactly at indices $d-1,2d-1,3d-1,\ldots$. Every prefix of
length $v<2d$ has a compatible alternative differing at its next bit.
For $v<d-1$ use an impulse at $v$; at $v=d-1$ use zero.
For $d\le v\le2d-2$, put $k=v-d$ and use initial seed with
its sole one at $d-1$ and the order-$d$ recurrence whose sole
nonzero coefficient is $c_{d-1-k}=1$. Its outputs at indices
$d,\ldots,d+k-1$ are zero, because their selected seed positions
are below $d-1$, while its output at $d+k=v$ is one.
The periodic source is zero there. At $v=2d-1$ instead use the
single impulse at $d-1$. Thus the actual difficult source's own
prefix is ambiguous at every subthreshold length, including $d=1$.

In $\mathscr M_K$, choose the $K$-cycle with its unique one at
phase $K-1$. For $v<K-1$ compare with $0^v1^\infty$;
at $v=K-1$ compare with zero. For $K\le v\le2K-2$, put
$l=v-(K-1)$. Use $K-l$ transient zero states followed by an
$l$-cycle whose one is its last phase. Its first one is at $K-1$
and its second at $K-1+l=v$, whereas the difficult $K$-cycle's
second one is at $2K-1$. It therefore matches the whole prefix and
differs at its next bit, using exactly $K$ states. For $K=1$ the
constant-one difficult source and constant zero handle the sole
shorter length $v=0$.

For the public-row benchmark of length $r>0$, every seed prefix of
length $v<r$ admits an alternative next seed bit under that same
row. Thus any chosen actual seed is unready at all such lengths.
On each of these difficult-source runs, an adaptive program stopping
at any mature cut below $N(m)$ has $v_n<m$ and an alternative
with the identical full accessible trace by Corollary 31.3, but a
different newest bit and $\mathcal Q_1$ answer. It cannot stop
there correctly for all sources. The same argument handles zero-error
randomization: countably many finite cuts/visible words partition a
positive finite stopping event, and an alternative preserves its
record law while changing the required answer. Hence no smaller
worst update deadline works. This proves sharpness for all three
tasks without mistaking a separate fixed-cut witness for an adaptive
stopping lower bound. The other coordinates have not been minimized.
$\square$

For $m=0$ the stream is already fixed in the zero-order recurrence
or zero-length public-row class. Zero reads suffice; the first mature
cut $n=2$ is ready after its two actual updates. Formula (GPO.81)
would give $N(0)=3$ only because it explicitly restricts $n\ge3$;
it is not the optimum in this degenerate case. There is no zero-state
Moore class. If readiness at the nonmature seed itself is allowed, its
known zero law already supplies prediction there without an update;
that is outside the mature-cut deadline comparison.

## 34. Earned memory, birth-time recovery and retained actual use

**Definition 34.1 (the earned memory view and binding).** At the returned
cut of Theorem 33.2, retain the actual first $m$ acquired bits in
readable owned backing, the canonical finite behavioral description
selected by the fixed synthesis, and counters $n,B_n$ synchronized to
the actual source. Retain the source handle/root, surviving Read/update
grants, and the actual exclusive serial invocation path. A current
expanded tree and request workspace may be maintained in additional
backing. Installation completes only when all those real writes and
handoffs have finished. A computed address or a copy of a permission
bit is not a source handle or a live grant.

The selected mathematical memory data are

$$
 M_n^{\rm earned}=(z_1\cdots z_m,\ \widehat L,\ n,B_n),
 \tag{GPO.84}
$$

where $\widehat L$ is the fixed canonical behavioral generator; in
the public-row case it is that row with its earned seed. The genuine
binding and capabilities are separately retained actual relations on
this data and its source. The mathematical view does not contain all
scratch bytes, all earlier observer operations or the private source
machine. Different encodings of the same data are not thereby equal
physical memories. If an audit needs literal acquisition receipts, their
actual words, replies and backing must also be retained and charged;
they are not used as an extra input by the predictor.

**Theorem 34.2 (four recovery routes on the law-ready domain).** Fix
one of the authentic classes and its bound, the actual chronological
rule and one actual binding as above. On the completed, law-ready
cuts $n\ge N(m)$ for $m>0$, separately each of

$$
 S_n,\qquad\partial S_n,\qquad
 \mathcal T_n^{\rm birth},\qquad M_n^{\rm earned}
 \tag{GPO.85}
$$

determines the other three mathematical data views, the same current
labelled tree, and its entire behavior of Definition 31.1. Every
recovery route agrees with the direct route. The result also holds
on $n\ge2$ for the zero-order singleton. It recovers the actual
ordered beta-birth chronology (GPO.74), including its physical parent
addresses and newest bits; it does not recover an arbitrary observer
journal, hidden generator presentation or physical durations.

Proof. From $S_n$ use Theorem 28.2 to recover $n$ and the actual
mature word of length $v_n\ge m$. Its first $m$ bits give exactly
the canonical $\widehat L$ chosen during actual acquisition. This
recovers (GPO.84). The law then generates the stream through $B_n$.
Forward replacement from the known actual alpha origin, with the actual
chronological rule, yields each successive parent address, update index
and birth bit through cut $n$. By induction on updates and on the
within-update birth order these are precisely the actual events, not a
law-equivalent history with a different allocation order. Thus it yields
$\mathcal T_n^{\rm birth}$ and $X_n$.

From the terminal boundary take prefix closure and apply that same
algorithm. From the actual birth trace, execute its specified replacements
from alpha; the result is $X_n$ and its actual incidence. From earned
memory, generate the same finite stream prefix and perform that same
forward replacement; its counters supply the actual cut and phase.
The generator selected from its first $m$ bits is the same canonical
one, even when the hidden source has a different but equivalent
presentation. These explicit operations prove each direction. Every
route returns the views of this same actual stream, chronological rule
and update count. Hence composing routes gives the direct value, and
the round trips are identities on these data images. Theorem 31.2
supplies the common future behavior.

The binding and rights are held fixed as actual prerequisites throughout.
No decoding map constructs a missing root, obtains a grant, verifies
source authenticity or repairs a lost synchronization. Nor does this
proof give a bijection of all material bytes: a scratch allocation or
extra stationary read can change an observer journal without changing
any birth event or source incidence. $\square$

The temporal claim has actual event content beyond its integer $n$.
For example the constant-zero and constant-one birth laws belong to
$\mathscr R_d$ for every $d\ge1$ and $\mathscr M_K$ for every
$K\ge1$. At the same $n\ge3$ their unequal root-child shapes
occupy opposite ports. Thus $n$ alone still cannot recover physical
incidence across either such class. The zero-order singleton is the
explicit exception. Scalar time has not been inverted into arbitrary
space. A known chronological event count also gives no physical duration.

**Theorem 34.3 (callable use and dynamics compatibility).** Under the
continued availability, completion and backing premises of Definition
27.1, the returned memory supports the following installed finite
procedures: answer a current or hypothetical finite presence/update
request locally; actually execute a requested source Read or update
on its retained binding; and continue from every completed call boundary
with the correct current labelled tree and birth phase. These procedures
use no further paid source read to learn the birth law. For every finite
actual serial continuation, their predicted replies, physical tree
successors and the four data routes of Theorem 34.2 agree with that
same continuation of the actual source.

Proof. For local prediction, parse the genuinely supplied finite
request, copy the earned current data to scratch, and simulate its
finite updates using the behavioral generator. A literal Read returns
membership in the simulated support, including zero for any absent
word. Each tree, request and loop is finite. A finite request may also
be generated adaptively by installed source-free control from actual
replies and separately acquired selector inputs. The selector's input,
code, scratch and output are real resources; no unspecified full response
oracle or already acquired future experiment is assumed.

For an actual update $n\to n+1$, use the real source handle and wait
for its completion. Update the local tree by replacing its alpha leaves
with beta and its beta leaves by branches in physical lexicographic
parent order. The next consumed block is exactly
$z_{B_n+1},\ldots,z_{B_{n+1}}$. Advance the local law by precisely
that many births, or recompute its position from the retained prefix
and counter. Commit the new $n,B_n$ and data before exposing the next
callable cut. The authentic autonomous law, the induction invariant
$X_n^{\rm local}=X_n^{\rm actual}$ and the same ordered parent
list give identical bits, persistent links, labels and successor support.
The proof holds even for a singular recurrence or nonminimal Moore
presentation, since it uses stream equality rather than inversion of
private machine state.

A real source Read is still called and charged if requested. Its reply
agrees with the local membership calculation; a prediction does not
pretend that this call was executed. Read and localStep consume no birth
bit and leave the source views unchanged. Stop makes no further source
transition. Induction gives the result for every finite serial action
word, and then for every finite adaptive choice whose inputs are actually
available. The source-view conversions commute with each update because
they all compute this same $X_{n+1}$ and its actual birth events.
They commute with stationary source operations by constancy.

The maintained protocol may use internal busy phases between the actual
acknowledgement and local-data commitment, and within request evaluation.
Its actual phase flags, saved counters, partial acquired batch and
buffers must persist there; a call is exposed only at a synchronized
completed boundary. If an interruption, concurrent writer, revocation
or source replacement breaks this invariant, this theorem gives no
continued-use guarantee. It assumes the real binding and synchronization,
not their inference from an abstract inverse. $\square$

These assertions concern the source projections and completed callable
cuts. They are not a full-state kernel for all observer instruction
cuts. In particular Read/localStep multiplicities are erased by
$\mathcal T^{\rm birth}$, while NCR's fixed initialized controller
and primitive-clock hypotheses supply a different, finer historical
inverse. Nothing here upgrades the birth trace to that unrestricted
observer chronology or to Atlas's full joint field record.

## 35. One-run prices, material generation and retained lifetime

**Proposition 35.1 (source generation is larger than the acquired prefix).**
For a cut $N\ge2$ in this construction, the actual source has

$$
 L_N=F_{N+1},\qquad V_N=2F_{N+1}-1=1+2B_N
 \tag{GPO.86}
$$

leaves and nodes. From alpha through that cut it has allocated exactly
$2B_N$ new child nodes and $2B_N$ new child links and generated
$B_N$ actual birth bits, including the unqueried newest bits. At an
update $e\to e+1$ with $e\ge1$, exactly $F_{e+1}$ old leaf
tags are overwritten and $2F_e$ new nodes and child links are
allocated. The initial update overwrites its one alpha tag and allocates
no child. A straightforward old-node traversal inspects $V_e$ old
nodes per update, with $V_0=1$; it never recursively revisits newborns.
These are separate material and work coordinates, not one unit per
applyRho.

Proof. A full binary tree with $L$ leaves has $2L-1$ nodes.
The leaf counts and birth counts are Proposition 27.2. Each birth
retains its parent and constructs exactly two children and links; every
old leaf changes tag or becomes a branch. Summing these actual additions
gives (GPO.86) and the stated totals. The traversal is a possible
implementation of Definition 27.1's old-leaf rule. Other backends must
price their own traversal and allocation, without replacing the source
by an already expanded paper tree. $\square$

**Definition 35.2 (simultaneous accounting).** For the actual acquisition
and installation run let $J$ count all executed native localSteps,
$Q$ its actual Reads, $U$ its actual updates, $W$ the sum of
literal query lengths and $M_{\rm addr}$ their maximum. Use
(GPO.82), or the zero-order case, for these Read/update coordinates.
Charge the following additional coordinates on this very run.

- All initialization, authentic bound/law supply, binding and grant
  acquisition or installation; every source-service traversal, tag change,
  child/link allocation and actual source-owned law operation. In the
  declared logical recurrence implementation an order-$r\le d$ source
  retains its $r$ seed bits and coefficients, emits all $B_N$ bits
  and performs at most $r$ binary products and $r$ additions for
  each subsequent recurrence bit. A Moore realization emits $B_N$
  outputs and makes $B_N$ unary transitions in its declared emission
  convention. Its table access, state encoding and actual material costs
  still count. These are ideal logical implementations, not tariffs for
  every possible hidden presentation or physical apparatus.
- All accessible local computation: Fibonacci counters, earned-tree
  traversal, parent sorting or ordered traversal, literal construction,
  actual reply appends, recurrence or machine enumeration and comparison,
  generation of unread bits, tree reconstruction, phase changes, request
  parsing, selector work, copying, output and installation handoff. These
  operations contribute to $J$ at their actual native granularity and
  require actual workspace. The recurrence search tests at most $2^d$
  rows, with finite order-$d$ simulation of $2d$ bits each; the Moore
  search tests at most $\sum_{r=1}^K r^{r+1}2^r$ presentations,
  with $2K-1$ generated outputs each. These finite work bounds are
  deliberately not computational optima.
- All simultaneous storage: source nodes and private generator, accessible
  earned bits, the chosen behavioral table, current tree if expanded,
  stacks, literal buffers, candidates, counters, pending phase, output,
  handles and real capability material. A chosen recurrence description
  uses $O(d)$ binary coefficient/seed cells; a chosen labelled Moore
  table uses $O(K\log(K+1))$ bits. Neither figure includes the growing
  physical tree, source backing, trace, expanded local tree, request/output
  storage or the counter widths. Every finite run has finite required
  backing under the service premise; these bounds do not imply bounded
  total memory over all continued use.
- The original hidden writer and its backing. Under Definition 22.1's
  event convention it appends $J+Q+U$ entries, with each literal word,
  actual presence reply, local/update event and required epoch fields.
  Its payload therefore includes all $W$ literal letters as well as
  event/reply/framing and counter material. This writer is inaccessible,
  and no claim that its fields were acquired enters the proof. Any backend
  with finer source-law, allocator or traversal records adds those actual
  records; they are not erased to reduce the bill.
- Read traversal and continued lifetime. On the declared root/child
  implementation the queries use at most $W+Q$ root/edge traversals,
  besides literal handling. Source storage, owned backing, law-table
  readability, root binding and surviving grants must remain available
  throughout acquisition, installation and each later invocation. Their
  retention and service costs coexist with the preceding coordinates.

A local computation step has only its specified ideal native price;
no unit-cost arithmetic, physical time or energy conversion is implied.
The actual source generator's initially unknown seed and coefficients
are material of that source, not free advice to the observer.

**Proposition 35.3 (continued-use addition on the same run).** For any
actual finite continuation after the returned cut, let $Q_c,U_c,J_c$
and $W_c$ count its real Reads, updates, local work and literal traffic,
including computations and writes of Theorem 34.3. The combined
coordinates are

$$
 Q+Q_c,\qquad U+U_c,\qquad J+J_c,\qquad
 W+W_c,\qquad
 \max(M_{\rm addr},M_{{\rm addr},c}).
 \tag{GPO.87}
$$

The source reaches cut $N+U_c$ and has the material count (GPO.86)
there, having generated $B_{N+U_c}$ bits in total. The law predictor
adds no learning Reads, but its computation, scratch and outputs are
included in $J_c$ and their storage. A hypothetical evaluation executes
no source update and creates no actual source Read receipt. Its costs
are its input, local computation and output, not the cost of a second
physical trajectory.

Proof. Concatenate the actual serial event words; each actual call and
literal is counted once in its segment. The maintained source invariant
in Theorem 34.3 gives the final update count and hence the actual material
and generator totals. Simultaneously retained outputs, trees, candidate
records and archives require combined backing; serial scratch may be
reused only after its old contents are no longer needed. Further receipts
and retention intervals add their own material and lifetime charges.
These statements are direct one-run accounts and do not combine separately
attaining optima. $\square$

The sharp coordinate here is the class-uniform mature update deadline,
not a physical completion time: $J$ can be large while the source is
held stationary. The $m$-Read construction does not establish a lower
bound on Read count when one is allowed more updates, longer queries or
a different decoding protocol for the bounded law. The seed-only visible
prefix threshold is likewise an information threshold, not an unproved
unknown-coefficient Read minimum. There is no total price scalar or
minimum over apparatus, storage, computation, energy and lifetime in
these theorems.

## 36. Source subtraction and the unclosed common-process programme

**Definition 36.1 (exact reuse and the native delta).** Repository
sources in this comparison are their published originals at
`03e4663c7a64fb62d1407d102d75685e5981d28c`. The additional content of
§§27–35 is the correspondence between the actual public chronological
birth law and its mature physical incidence, the consequent exact native
readiness/deadline criteria, the source-blind $m$-Read acquisition,
and its earned, synchronized retained use. Classical finite-prefix
identification, finite-map periodicity, generic fiber factorization,
prefix closure, replay and controller synthesis are not new results
of this addition. This is conditional, source-relative `repo-derived`
theory synthesis, without a worldwide priority or new Lean claim.

| Published supplier | Parameter/source correspondence and subtraction |
| --- | --- |
| GPO §§22–26, especially Theorems 24.2–24.3 and 25.1 | The same alpha seed, physical persistent $a,b$ links, literal presence interface, terminal bits, (GPO.69) and one-update historical calibration. Those full fibers and arbitrary-wiring impossibility theorems are reused unchanged. Definition 27.1 adds a genuine autonomous law and actual chronological order; Theorem 28.2 determines its ordered mature prefix and §33 obtains its parents without a full shape scan. |
| `GenealogicalFiberTransport.lean` and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.scribe.cs) | `Source` is the free ordered magma on Bool, with true alpha and false beta; substitution, assembly/decomposition and `sourceEquiv`, including the internal `no_alpha` injectivity argument, concern that semantic ordered source. They supply neither the physical local frames nor a birth-bit acquisition. They are not applied as an identity between semantic and hidden locally wired addresses. |
| `ActualFibonacciSupportChain.lean` and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.scribe.cs) | Its internal `recurrence`, `root`, `presence`, `monotone`, `short` and `spine` arguments supply actual ordered semantic Fibonacci support facts. The leaf/rank correspondence used in §28 is the local physical argument of GPO24.2, with chronological parents added here. Ordered support declarations alone do not expose a newest physical bit. |
| `NativeSerialMachine.lean` and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs); `NativeFullSourceProducer.lean` and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) | `Op`, `nativeStep`, `Run`, `Replay`, `replay_deterministic`, `reached_prefix_replay` and `actual_register_execution` supply the source-free-control/reached-reply architecture. The producer's `sourceControl` and private `traverse`, `production_reads`, `stationary` use full alpha/beta/branch replies on an unchanged source and acquired stack data; they already charge local assembly. Our different source returns presence only and has local actuator wiring. Theorems 33.2 and 34.3 give its own operational induction, without claiming an existing compiled specialization or borrowing the producer's full replies. |
| NCR §§2,5,8; PVC §§1–2,5–6,10; Native Callable Storage Atlas Definitions 2.1–2.4, §§5–8 and Theorem 11.1 | Their fixed initialized controllers, actual code/input/activation data, primitive clocks, serializers, acquired backing, grants and return paths remain exact premises. They already distinguish a mathematical inverse from installed paid use, and complete joint records from source-only views. None supplies an unknown birth-law acquisition or an inverse of arbitrary local observer journals from this source incidence. The selected birth chronology and earned data in §34 have their own narrower domain. |
| Published STR13.1, 13.3, 14.2–15.1 and newest STR17.1 in [Sharp task retained environment memory](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md) | STR's actual all-qutrit input, five-dimensional embedding $B$, fixed known angle, arbitrary rectangular CPTP correction and immediate plus labelled full-$H$ effects supply exact channel rigidity, reference preservation and the finite consumed-flag port consequence. STR13.3 supplies the uniform square-root stability upper, and STR17.1 supplies the matching first-order-invisible family at angle zero, hence optimal worst-case uniform local Hölder exponent $1/2$. These are published results, not unresolved optimization targets. They do not install an atomic birth law or its presence sensor; no constant, menu, exponent or quantum-atomic identification result is proposed here. |
| [Paid point observation tracking](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md), §§60–65, especially Theorems 61.1–64.1 | Its fixed signed nonzero central-noise Brownian source, positive-gap paid wrapped-point service and finite Borel report map have live-volume/face-surface certificate criteria. It already proves the actual no-premature-own-death and bounded-occupation obstruction for boundary-merged reports, including the distinction between null and empty fibers. Those are different stochastic and observation domains from deterministic birth bits; no Gaussian support, death certificate or finite-point tariff is transferred here. |
| Published AQBR10–12, SGPM17–21 and FSPM19–23 | [Arithmetic acquisition return](RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_ACQUISITION_RETURN.md) supplies sharp continuous gcd acquisition with positive modular closing and same-handle arithmetic-behavior return, using its actual natural pair, public modulus and $R/G$ operations. [Self-generated predictive memory](RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md) supplies normalized multi-phase feasibility and the unrestricted initialized minimum for its fixed known five-mode stochastic source; arbitrary real synthesis remains separate from rational witness checking. [Finite-start predictive memory](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md) supplies observable-return categorical acquisition, risky exact catalogue selection and approximate capped-horizon empirical prediction on its original five-mode stream. Their paid retained-use distinctions are suppliers; none authenticates our autonomous law from a prefix, identifies our private presentation, or supplies a universal deterministic exact acquisition theorem. Their original minima and residual risks are not changed. |

The named Lean files are under
`D5/S3/Arith/FibonacciAtomic/`, with the observer files in its
`Observer/` subdirectory. Owning Scribes and internal proofs matter
for reuse: a private proof or supplied definition is not missing merely
because an API name is unavailable. Source inspection is documentary
evidence of those hypotheses, not a fresh compilation or an exhaustive
semantic-coverage claim.

The classical suppliers are James L. Massey,
[*Shift-Register Synthesis and BCH Decoding*](https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI411.pdf),
IEEE Transactions on Information Theory IT-15, pp. 122–127, §§II–IV;
J. A. Reeds and N. J. A. Sloane,
[*Shift-Register Synthesis (Modulo m)*](https://neilsloane.com/doc/Me111.pdf),
SIAM Journal on Computing 14(3), pp. 505–513, §2; and Edward F. Moore,
[*Gedanken-Experiments on Sequential Machines*](https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf),
*Automata Studies*, pp. 129–153, Theorems 2,6,7
([stable source](https://www.jstor.org/stable/j.ctt1bgzb3s.8)).
Their complete-source hypotheses distinguish initial output count,
nonminimality, singular registers, transient numerator terms and missing
machine bounds. The classical separation arguments are included only to
establish this exact parameter match; the new mathematical consumer is
the chronological local-port correspondence and actual native acquisition.
No broader ring, multi-input machine or private-state recovery theorem is
inferred.

**Definition 36.2 (current unresolved scope).** The source-owned law,
authentic finite bound, first-birth alignment, actual public physical
ordering, alpha seed, service/root/capabilities and per-run material
completion remain premises. They have not been derived from bare
alpha/beta constructors, verified from finitely many replies or installed
on a physical backend. A physical implementation must provide precisely
those common-source operations, synchronization, persistent links,
authenticity, retention and prices; a mathematical inverse provides none
of the missing authorities. Recurrence and Moore bounds describe
separate source classes and are not interchangeable resource counts.

The original arbitrary-wiring, original-semantic, historical and
mature-current claims retain their exact scopes. In particular GPO24.3
still excludes acquiring the newest arbitrary actuator choices; the
law-bearing subclass removes their independence as an explicit premise,
not as a consequence of extra computation or memory. The global-port
results in §§1–21 retain their stronger global correspondence and advice.
No unknown-original extension, inference of unrestricted law autonomy,
private presentation identification, unknown-coefficient Read optimum,
minimum total resources, bounded total memory or physical-duration inverse
is supplied here.

The four expressions in (GPO.85) are actual incidence, actual terminal
boundary, the specified actual birth-event chronology and selected earned
memory of one initialized process. Their proved mutual recovery and
update agreement are restricted to the authentic bounded-law ready domain,
with real retained binding. They do not recover a discarded arbitrary
observer journal, a whole material installation or all primitive timing.
Original fixed-$G_{\rm gc}$, original-Q, parked-consumer and unchanged-
initialization obligations remain unchanged. A common actual atomic,
quantum and continuous realization, independent physical spatial or metric
meaning, general recursive gluing, universal alpha/beta reduction and
parsimony of the full programme remain unresolved. This finite theory
addition is author evidence with ordinary proofs, not independent review,
Lean certification, publication or completion of the continuing objective.

## 追加锚（本行以下为增补区）

## 37. Exact paid Read requirement for the full recurrence class

**Definition 37.1 (native preparation and completed future readiness).**
Fix the entire class $\mathscr R_d$ of Definition 29.1, with public
$d\ge0$, and the actual source and service of Definition 27.1.
The source starts at its actual known alpha leaf. Its one autonomous
stream is fixed before the first birth, satisfies (GPO.75) at every
nonnegative index, and is aligned by $z_j=s_{j-1}$. Its actual birth
order is update order followed by physical lexicographic parent order.
No minimality, nonsingularity, positive order or periodicity is added.

A preparation has common initially source-blind code and accessible
initial data at fixed public inputs. It may use arbitrary legal finite
physical-word presence Reads, adaptive serial update schedules, and
arbitrary finite source-free local computation and retention. It must
return after finitely many actual operations on every promised source,
at a completed mature cut $n\ge2$. Write $Q$ for its paid binary
Read count and $U=n$ for its actual updates from alpha. There is no
bound here on finite literal lengths or local work. All requested
words, addresses and schedules must be computed from genuinely
accessible inputs and acquired replies.

Read alone exposes a source-dependent bit. Updates expose only the
common acknowledgement. Labels, generator data, hidden writer,
allocator identities, source backing, work, durations and waiting are
not observation channels. Actual source/root binding, live Read/update
grants, exclusive serialization, completion, persistent physical links,
and sufficient owned growing backing are retained premises, with their
own charges. No reset, clone, historical root, reroot or richer sensor
is allowed. An independently supplied local input or random tape has
no source-dependent advice.

Complete-future readiness means that the returned accessible data and
installed source-free evaluation procedure already determine exactly
the whole task of Definition 31.1 on this same actual source: every
finite presence/update continuation, all its replies, and its physical
support and labelled-tree successors, including absent-word replies.
Each supplied finite request must be evaluable by terminating finite
local work. A finite adaptive request may use actual supplied selector
inputs as in Theorem 34.3. The evaluator does not obtain new source
data while predicting a hypothetical request. A returned handle that
will learn the law by later source calls is not completed readiness.
Actual execution of a requested call is a separate paid operation.

The joint task additionally asks for the current labelled $X_n$ and
the current $\mathcal Q_1$ answer at that same returned cut. Only
these full-future and joint tasks are compared below. A uniform cap
$q$ means $Q\le q$ on every promised source. For independently
randomized preparations the requirements are zero error, almost-sure
finite return, and an almost-sure cap on each source; expected cost
is a different comparison.

**Theorem 37.2 (exact worst-case native Read minimum).** Under all
the premises of Definition 37.1, for each integer $d>0$ the minimum
uniform paid Read cap is exactly $2d$, both for complete-future
readiness and for the joint task. In particular every correct such
preparation has a lawful run requiring at least $2d$ Reads, even
when it may use more updates, longer finite words and more finite local
work. The same minimum cap holds with the independent zero-error
randomization specified there. At $d=0$ the minimum is zero.

Proof. First connect distinct streams to this native task, without
assuming that a full incidence has already been acquired. Fix public
inputs and, for the moment, a deterministic preparation. At any reached
Read or return boundary, its entire accessible state is a function of
the preceding binary reply word. Indeed its next local operations,
literal and update choices are source-free functions of that state;
updates return the same acknowledgement and stationary local operations
reveal no source data. Induction on the actual finite operations gives
the assertion. Thus the return cut $n$, output and retained evaluator
are identical whenever the preceding reply word is identical. Physical
differences in the unobserved source cannot be used as an extra branch
of this accessible computation.

Suppose two different streams $s,s'\in\mathscr R_d$ reached the
same return reply word. They then return at the same $n$. Choose a
birth $j$ at which their bits differ, and a finite $e\ge n$ with
$v_e=F_e-1\ge j$. Such an $e$ exists. By Theorem 28.2 their
actual physical supports at cut $e$ differ, since their first $v_e$
birth bits differ. Choose one physical word in the symmetric difference
of those two finite supports. The continuation consisting of $e-n$
updates followed by a Read of that word has different replies on the
two sources. This is one finite legal request at their common return
cut. Their identical retained local evaluator would have to predict
both values from the same accessible data and same request, which is
impossible. Every distinct stream must therefore occupy a different
return leaf. This argument also applies to the joint task, which
contains the complete-future requirement. It does not require equality
of the two current full incidences.

The number of leaves required here is a classical supplier. Rainer A.
Rueppel, [*Linear Complexity and Random Sequences*](https://link.springer.com/content/pdf/10.1007/3-540-39805-8_21.pdf),
in *Advances in Cryptology — EUROCRYPT '85*, LNCS 219, pp. 167–188
(1986), p. 174, equations (5)–(6), explicitly counts distinct binary
**semi-infinite streams** of linear complexity at most $d$. For the
present class his count is

$$
 D_d=|\mathscr R_d|
     =1+\sum_{\ell=1}^{d}2^{2\ell-1}
     =\frac{2\,4^d+1}{3}.
 \tag{GPO.88}
$$

The added one is the zero stream. This imports the semi-infinite count,
not a count of arbitrary length-$2d$ words, private registers or
primitive periodic generators. Its parameter correspondence is as
follows. An order-$r$ recurrence (GPO.75) is realized by the length-$r$
register with state $(s_i,\ldots,s_{i+r-1})$, output $s_i$, and
successor obtained by shifting and appending
$\sum_{j<r}c_js_{i+j}$. Conversely that register gives (GPO.75)
from index zero for every seed. A zero final feedback tap is legal;
the all-zero row shifts an arbitrary seed out and hence includes finite
transients. Taking the least possible register length identifies the
linear complexity, and allowing any length at most $d$ gives exactly
$\mathscr R_d$. Nonminimal presentations add no distinct streams.

Equivalently, for $r>0$ put $A_s(x)=\sum_{i\ge0}s_ix^i$.
Equation (GPO.75) is equivalent to

$$
 H(x)A_s(x)=P(x),\qquad
 H(x)=1+\sum_{k=1}^{r}c_{r-k}x^k,
 \qquad \deg P<r,\quad\deg H\le r.
 \tag{GPO.89}
$$

The coefficients at degrees $i+r$ give the recurrence in the reverse
direction; the coefficients below $r$ accommodate the arbitrary seed.
Thus a polynomial $A_s$ is retained even when $H=1$: its transient
numerator is not discarded. For a nonzero reduced $P/H$ with $H(0)=1$,
the least permitted length is
$\max\{\deg H,1+\deg P\}$, since every presentation has those
two degree bounds after reduction and this length itself satisfies
(GPO.89). The zero stream has length zero. This is the all-index and
singular convention already used in Lemma 29.2 and its Massey
§§II–IV and Reeds–Sloane §2 suppliers cited in §36. It verifies
the domain match for (GPO.88); it does not restrict the count to
invertible or purely periodic sources, or assert uniqueness of the
actual private presentation.

Now suppose a correct preparation has uniform Read cap $q$. Its
return reply words form a prefix-free binary family of lengths at
most $q$: after a return at a given reply word, source-free control
cannot instead ask another Read on another run with that same word.
The standard binary decision-tree capacity is at most $2^q$ leaves.
For example, extending each leaf word to length $q$ gives disjoint
nonempty sets of binary words, all lying in the $2^q$ length-$q$
words. Arbitrarily many deterministic update or local operations
between branches do not increase that capacity. The preceding native
distinguishability argument and (GPO.88) force $D_d\le2^q$.
For $d>0$,

$$
 2^{2d-1}<\frac{2\,4^d+1}{3}\le2^{2d},
 \qquad \lceil\log_2D_d\rceil=2d.
 \tag{GPO.90}
$$

Consequently $q\ge2d$. These stream counts and binary-tree capacity
are classical inputs; the source-specific deduction is that every
full-future return of this native presence service needs that many
distinct leaves. Query length, query choice, update timing and stored
local computation do not supply further reply letters.

For randomization, choose one lawful source realization per distinct
stream, and fix the common public inputs. There are only $D_d$ such
representatives. For each representative, correctness, finite return
and the asserted cap hold on a measure-one set of independent tapes.
The intersection of these finitely many sets has measure one. Any tape
in it gives a deterministic preparation correct on all representatives,
to which the same leaf bound applies. Hence a uniform almost-sure cap
below $2d$ is impossible. If that cap is absent, the theorem makes no
expected-cost assertion.

For attainment use the actual source-blind preparation of Definition
33.1 with $m=2d$. Theorem 33.2 obtains exactly the first $2d$
birth bits by $2d$ paid binary presence Reads on that source, at cut
$N(2d)$. Its finite synthesis in Lemma 29.2 determines the whole
actual stream. Theorems 33.2 and 34.3 then provide the current
labelled tree, $\mathcal Q_1$, and the installed finite local
evaluator, with completed writes and retained binding as stipulated.
Thus both tasks attain $Q=2d$. For $d=0$ the unique stream is
already known; two actual updates reach a mature cut and local forward
replacement supplies both tasks with no Read. Nonnegativity of $Q$
proves the zero minimum. $\square$

**Proposition 37.3 (the zero and one-order cases, and a pointwise limit).**
The zero-order class has mature attainable coordinates $(Q,U)=(0,2)$.
For $d=1$ the exact class is
$\{0^\infty,10^\infty,1^\infty\}$, and the uniform Read minimum
is two, attained together with $U=4$. Nevertheless a correct uniform
preparation can return on $0^\infty$ with one Read at cut three.
Thus Theorem 37.2 does not assert $Q\ge2d$ separately on every
actual source run.

Proof. Order zero fixes all bits to zero, so the first assertion is
the final case of Theorem 37.2. In order one, the coefficient is zero
or one and the seed is zero or one. The zero seed always gives zero;
the other choices give exactly the impulse and the constant-one stream.
Their first two bits are respectively $00,10,11$. The first birth
has parent the root and is read by $aa$ at cut three. For a second
Read, its earned bit determines the parent $p_2$ of birth two:
$p_2=b$ if $z_1=0$, and $p_2=a$ if $z_1=1$. At cut four the
legal query $p_2aa$ gives $z_2$ by (GPO.83). These are paid
presence queries, with real updates between them. Since $v_3=1$
and $v_4=2$, $N(2)=4$. Three distinct streams exceed a one-bit
tree's capacity, establishing the worst-case two-Read requirement.

A variant terminates after the first query if its bit is zero, because
only $0^\infty$ is then compatible in this class. It installs that
known continuation by finite local computation at cut three. On a one
reply it performs the second query and returns at cut four. This is
uniformly correct with worst-case two Reads, yet uses only one on the
zero source. The example also distinguishes earned information about
an actual behavior from a fixed presentation bound. $\square$

## 38. Joint uniform caps and their earned continuation

**Theorem 38.1 (exact two-coordinate cap region).** For the full
$\mathscr R_d$ and all the premises and readiness requirements of
Definition 37.1, let $\mathcal F_d$ consist of integer pairs
$(q,u)\in\mathbb N_0^2$ for which one uniform preparation has
$Q\le q$ and $U\le u$ on every source. Use the corresponding
almost-sure requirements if independently randomized. For either the
complete-future task or the joint task, exactly

$$
 \mathcal F_d=
 \begin{cases}
 \{(q,u):q\ge2d,\ u\ge N(2d)\},&d>0,\\
 \{(q,u):q\ge0,\ u\ge2\},&d=0,
 \end{cases}
 \qquad
 N(m)=\min\{n\ge3:F_n-1\ge m\}\quad(m>0).
 \tag{GPO.91}
$$

The lower corner in each case is attained on one actual source run
by one uniform preparation, simultaneously in both coordinates.
This is a region of worst-case **caps for $Q,U$ only**.

Proof. For $d>0$, Theorem 37.2 forces $q\ge2d$ regardless of
the permitted update cap. The sharp adaptive-stopping lower bound of
Theorem 33.2 forces $u\ge N(2d)$ regardless of the permitted
Read cap and local work. That proof uses one periodic difficult source
which remains ambiguous at every earlier mature cut, not merely
different witnesses chosen separately for fixed cuts. Its indistinguishable
alternative changes a newest bit and a finite future reply. It therefore
applies to both tasks here and to independent zero-error randomization.

Conversely, Definition 33.1 with $m=2d$ and Theorem 33.2 have
$Q=2d$ and $U=N(2d)$ on the same run, with actual acquisition
and completed installation. This one preparation meets every pair of
larger caps. There is no need to combine two separately attaining
preparations. For $d=0$, maturity itself requires the actual counter
$U\ge2$, and the zero-Read preparation in Theorem 37.2 attains
$(0,2)$. This proves the two regions.

For a competitor, the stream witnessing its worst Read count need
not be the stream witnessing its worst update count. The independent
necessary caps and their common attainment suffice for (GPO.91).
Nothing in the proof identifies a shared hardest input for every
competitor, or compares its local work or total material prices.
$\square$

**Corollary 38.2 (same-source four-view recovery at the attained corner).**
For the attaining preparation in Theorem 38.1, at its completed return
and every later synchronized completed cut under Theorem 34.3's
continued service and retention premises, the four mathematical views

$$
 S_n,\qquad \partial S_n,\qquad
 \mathcal T_n^{\rm birth},\qquad M_n^{\rm earned}
 \tag{GPO.92}
$$

have exactly the mutual recovery and update compatibility of Theorem
34.2, and give the current labelled tree and all finite future behavior
of this same actual source. Real retained binding and grants make the
continued calls of Theorem 34.3 available. No further paid Read is
needed to learn the law; requested real Reads still count.
For $d>0$ this begins at $n=N(2d)$ with $Q=2d$ and
$U=N(2d)$; for $d=0$ it begins at $n=2$ with $(Q,U)=(0,2)$.

Proof. At $d>0$ the attained first $2d$ bits select the very
canonical generator and synchronized counters of Definition 34.1,
with all its genuine retention relations. Theorem 34.2 applies because
$v_n\ge2d$. At $d=0$ its singleton clause applies with empty
earned prefix and the canonical zero generator. Each recovered view is
the view of that same initialized stream, public birth order and actual
cut, so the existing route and round-trip identities apply on their
stated data images. No full-incidence scan is an extra prerequisite:
the acquisition of Theorem 33.2 already constructs each requested
birth parent from earlier earned bits. Theorem 34.3 preserves the
actual tree, phase, binding and completed-call invariant for every
finite actual continuation, and provides each local hypothetical
evaluation without further law-learning Reads. $\square$

All simultaneous prices of §§34–35 remain attached to this attaining
run. In particular for $d>0$ its literal traffic and longest address
are still the actual sum and maximum in (GPO.82), with
$W\le2d(N(2d)-1)$ and $M_{\rm addr}\le N(2d)-1$.
Its source has actually generated $B_{N(2d)}$ birth bits, including
unread bits, and has the nodes and links of (GPO.86). Generator work,
local synthesis, reconstruction, backing, hidden writer, capabilities,
installation and continued lifetime retain the charges of Definition
35.2. Finite continued use adds the coordinates of Proposition 35.3.
The new Read lower bound does not minimize any of those other
coordinates. In particular (GPO.91) is neither a total-price minimum
nor a full-resource Pareto frontier.

The scope of Theorems 37.2 and 38.1 is full-future readiness and the
joint task on the original all-index $\mathscr R_d$. They assert
no standalone paid Read lower bound for the current-label or
$\mathcal Q_1$ task alone, no minimum for $\mathscr M_K$, no
private-parameter recovery, and no deferred-learning replacement for
readiness. Expected costs, richer sensors, empirical authenticity and
physical duration remain outside their claims. The time view in
(GPO.92) is the actual marked birth chronology of §28, and the
memory view is the selected earned data of §34; neither is an
unrestricted observer journal or an entire material installation.
The authentic source law, bound, actual chronology, binding and
synchronization remain premises throughout, with the finite-prefix
authentication limitation of Theorem 32.2 unchanged.

The classical count in (GPO.88) and binary decision capacity are
reused intermediate suppliers inside Theorem 37.2. The new native
consumer is the distinct-behavior return-leaf argument under this
specific presence-only source contract, joined to the existing paid
attainment. This is source-relative `repo-derived` theory with ordinary
proofs and the stated literature attribution, without a worldwide
novelty or Lean-certification claim. The semantic four-valued control
and replay declarations in `NativeSerialMachine.lean` and
`NativeFullSourceProducer.lean`, with the owning Scribes and parameter
boundaries of Definition 36.1, remain documentary suppliers. They are
not an actual compiled binary-presence specialization of this theorem.

## 追加锚（本行以下为增补区）

## 39. A request-sized physical evaluator from an earned recurrence

**Definition 39.1 (birth descriptors and sibling masses).** Keep the
actual source, physical order $a<b$, and stream convention of Definition
27.1. Let $F_0=0,F_1=1$ and $B_t=F_{t+1}-1$. A node born at update $b$ with
initial label $\sigma\in\{\alpha,\beta\}$ has branch time

$$
 \tau=b+\delta(\sigma),\qquad \delta(\alpha)=2,\quad\delta(\beta)=1.
 \tag{GPO.93}
$$

Its number of beta leaves after $e\ge0$ further updates is

$$
 \lambda_\alpha(e)=F_e,\qquad \lambda_\beta(e)=F_{e+1}.
 \tag{GPO.94}
$$

These counts ignore port orientation but retain the initial label. Give
the root descriptor $(b_\varepsilon,\sigma_\varepsilon)=(0,\alpha)$;
then $\tau_\varepsilon=2$. If $q$ is a branch and $z_{j_q}$ is its
orientation bit, the child descriptors at birth $b=\tau_q$ are

$$
 \sigma_{qa}=\begin{cases}\beta&z_{j_q}=1\\\alpha&z_{j_q}=0,\end{cases}\qquad
 \sigma_{qb}=\begin{cases}\alpha&z_{j_q}=1\\\beta&z_{j_q}=0.\end{cases}
 \tag{GPO.95}
$$

For a non-root node $p$, write its successive proper prefixes as $q c$,
where $c\in\{a,b\}$ is the next letter. Once the earlier descriptors
are known, define its one-based rank among beta leaves immediately before
its branch update by

$$
 R_{\tau_p}(p)=1+\sum_{\substack{q c\preceq p\\c=b}}
       \lambda_{\sigma_{qa}}(\tau_p-1-\tau_q),\qquad
 j_p=F_{\tau_p}-1+R_{\tau_p}(p).                 \tag{GPO.96}
$$

The sum is over the earlier sibling subtrees in physical lexicographic
order. The event $(j_p,\tau_p,p)$ is therefore the actual birth event at
which $p$ consumes $z_{j_p}$. For the root,
$R_2(\varepsilon)=1$ and $j_\varepsilon=1$. Formula (GPO.96) is a finite
recurrence, not a random-access tree oracle: each summand is a Fibonacci
mass of an actually specified sibling and every term has a previously
determined orientation bit.

**Proposition 39.2 (the actual index relation).** The descriptors and
(GPO.96) agree with the physical process of Definition 27.1. In
particular, if $p$ is the parent of birth $j$, then

$$
 t_j=\tau_p,\qquad p_j=p,\qquad
 B_{\tau_p-1}<j\le B_{\tau_p},\qquad
 j=F_{\tau_p}-1+R_{\tau_p}(p).                 \tag{GPO.97}
$$

Equivalently, for a given $j\ge1$,
$\tau(j)=\min\{t\ge2:j\le F_{t+1}-1\}$ and
$R(j)=j-(F_{\tau(j)}-1)$; $p_j$ is the unique beta leaf of
$X_{\tau(j)-1}$ whose rank in (GPO.96) is $R(j)$.

For a physical word $w$ of length $\ell\ge1$, every law bit needed to
decide the labels on its prefixes has index at most
$F_{2\ell+1}-1$; at most $\ell$ law bits are needed.

Proof. The two label transitions give (GPO.94) by induction on $e$. A
descriptor born at $b$ is $\beta$ at age $\delta(\sigma)-1$ and is a
branch at age $\delta(\sigma)$, proving (GPO.93). Induction on
the depth of $p$ gives $\tau_p\le2|p|+2$. At update $\tau_p$, the node
$p$ itself is a beta leaf immediately before the update; for non-root $p$,
its parent is already a branch. The beta leaves of the
whole old tree are the disjoint sibling cones encountered along the
root-to-$p$ path, together with $p$ itself. By (GPO.94), the cones
skipped exactly when the path takes $b$ contribute the summands in
(GPO.96). Thus $R_{\tau_p}(p)$ is its actual lexicographic rank. There
are $F_{\tau_p-1}$ old beta leaves, so
$1\le R_{\tau_p}(p)\le F_{\tau_p-1}$ and (GPO.97) follows from
$B_{\tau_p-1}=F_{\tau_p}-1$.

For a word of length $\ell$, only its proper prefixes can supply
orientation bits. A prefix of depth $r<\ell$ has
$\tau\le2r+2\le2\ell$, hence (GPO.97) gives
$j\le B_{2\ell}=F_{2\ell+1}-1$. The recurrence (GPO.96) evaluates one
new bit per depth and stops at the first prefix whose cut time exceeds
the requested cut, so no more than $\ell$ bits are used. The argument
explicitly includes all earlier sibling subtrees; no assumed global
random-access operation is present. $\square$

**Definition 39.3 (direct physical literal evaluator).** Let a completed
cut be a binary integer $n$ together with the retained source binding of
Definition 34.1 and an earned recurrence descriptor
$L=(r,c_0,\ldots,c_{r-1},s_0,\ldots,s_{r-1})$, $r\le d$. The descriptor
is the retained canonical row and seed selected by Lemma 29.2; for the
zero law take $r=0$. It denotes the same stream $z_j=s_{j-1}$.

For a literal word $w$, construct its prefix descriptors by
(GPO.93)--(GPO.96), evaluating each required $z_{j_p}$ from $L$. At a
descriptor $(b,\sigma)$ at cut $n$, return

$$
 E_L(n;b,\sigma)=\begin{cases}
 \mathsf{absent},&n<b,\\
 \sigma,&n=b,\\
 \beta,&n=b+1,\ \sigma=\alpha,\\
 \mathsf{branch},&n=b+1,\ \sigma=\beta,\\
 \mathsf{branch},&n\ge b+2.
 \end{cases}                                      \tag{GPO.98}
$$

The root uses $(b,\sigma)=(0,\alpha)$. Descending a letter is permitted
only after the preceding value is $\mathsf{branch}$; the child descriptor
is then generated by (GPO.95). If a nonempty suffix remains after a prefix
with value $\alpha$ or $\beta$, return $\mathsf{absent}$ for the requested
word. If a prefix is not yet born, return $\mathsf{absent}$ for the whole
word. Define

$$
 P_L(n,w)=\mathbf1_{E_L(n,w)\ne\mathsf{absent}},\qquad
 \partial_L(n,w)=\mathbf1_{E_L(n,w)\in\{\alpha,\beta\}}. \tag{GPO.99}
$$

Thus the empty word, an absent word, a terminal alpha or beta, and a
branch all have direct literal answers. The terminal boundary is the
set $\{w:\partial_L(n,w)=1\}$; asking for the entire finite boundary
enumerates its output and pays that output cost.

**Theorem 39.4 (literal correctness and same-source continuation).**
On every law-ready synchronized cut of Definition 34.1, for every finite
physical word $w$,

$$
 E_L(n,w)=r^\mathrm{actual}_n(w),\qquad
 P_L(n,w)=\operatorname{Read}_n(w),\qquad
 \partial_L(n,w)=\mathbf1_{w\in\partial S_n}. \tag{GPO.100}
$$

The evaluator remains correct after every finite same-source continuation
of actual updates and Reads under Theorem 34.3. It makes no law-learning
Read: actual Reads, updates, grants, root binding, serialization, source
authenticity and writer records retain their original premises and costs.

Proof. The root cases at cuts $0,1,2$ are immediate. Suppose a branch
descriptor is correct. Definition 27.1 creates both children at its
actual event $(j_p,\tau_p,p)$, in the order used by (GPO.96), and
(GPO.95) gives their actual initial labels. The label transition in
(GPO.98) is exactly alpha-to-beta, beta-to-branch, and persistence of a
branch. Induction on word length therefore proves the first equality in
(GPO.100), including early cuts and absent extensions; the other two
are its presence and terminal projections. The same induction on update
count proves that incrementing the binary cut counter and regenerating
descriptors gives the actual successor. At a real Read the evaluator's
projection agrees with the paid source reply, while the call is still
executed and charged. Induction on the serial call word, including
adaptive choices whose inputs are actually supplied, proves continued
agreement. $\square$

**Proposition 39.5 (polynomial request cost).** Put
$b_n=\lceil\log_2(n+2)\rceil$ and let the literal length be $\ell$.
For $\ell\ge1$, Definition 39.3 uses at most $\ell$ law evaluations,
at indices bounded by $F_{2\ell+1}-1$. A forward companion-matrix power
computes one such bit using $O(d^3\ell)$ binary operations and
$O(d^2+d\ell)$ working bits; it uses no inverse and is valid for
singular, nonminimal and both constant laws. Consequently one request
has, for an absolute machine-model constant $C$,

$$
 \operatorname{work}\le C\bigl(d^3\ell^2+\ell^3+\ell b_n+\ell+d^2+d\ell+\ell^2+b_n\bigr),
 \tag{GPO.101}
$$

apart from the supplied literal and any requested output. This is
polynomial in $(d,\ell,\log(n+2))$ and does not iterate through the
$n$ updates or allocate the whole tree.

Proof. For $r>0$, use the binary companion matrix taking
$(s_i,\ldots,s_{i+r-1})$ to
$(s_{i+1},\ldots,s_{i+r})$, with the last coordinate
$\sum_jc_js_{i+j}$, and exponentiate it by repeated squaring to
$j-1$. All arithmetic is over $\mathbb F_2$; the exponent has
$O(\ell)$ bits by Proposition 39.2. The $r=0$ case returns zero, while
$(r,c_0,s_0)=(1,1,1)$ returns the constant-one stream and
$(1,0,0)$ the constant-zero stream. No determinant or final coefficient
is assumed nonzero. Fibonacci fast doubling, the rank sums in (GPO.96),
binary comparisons with $n$, and prefix storage have respectively
polynomial cost in $\ell$ and $b_n$. Summing over at most $\ell$ matrix
powers gives (GPO.101). The bound concerns one literal request; full
boundary or full-tree enumeration keeps its actual output, backing and
source-generation costs from Proposition 35.1. $\square$

The rank recurrence is the source-specific addition. Cover's
[*Enumerative Source Encoding*](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf)
is a documentary analogue for lexicographic prefix blocks, not a free
rank oracle here. Bostan--Mori,
[arXiv:2008.08822](https://arxiv.org/html/2008.08822v1), §§1.1--1.3,
supplies the forward-recurrence term-evaluation setting; the companion
power above deliberately avoids invertibility assumptions. Bille--Landau--Weimann,
[arXiv:1001.1565](https://arxiv.org/pdf/1001.1565v1), studies random
access when a compressed representation is actually given; it does not
replace the retained recurrence, physical rank proof or paid acquisition.
Theorems 28.2, 33.2, 34.2 and 34.3 supply the earned prefix, four views,
binding and continued source use reused here. No acquisition or synthesis
complexity is reduced, and no full-resource optimum is claimed.

## 追加锚（本行以下为增补区）

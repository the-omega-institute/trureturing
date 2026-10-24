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

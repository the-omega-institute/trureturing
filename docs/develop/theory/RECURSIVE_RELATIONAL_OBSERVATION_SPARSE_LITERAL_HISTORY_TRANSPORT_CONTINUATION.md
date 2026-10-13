# Sparse literal history transport: generation-interleaved complete memory

This continuation of [Sparse Literal History Transport][SLH] (SLH) treats
one finite native consumer: recover an original vector of independent
leaf labels while preserving a specified sequence of reads and genuine
generations. SLH §§31–32 supply the ancestor decomposition and acquisition
method; [FIB continuation II][FIB] §§26–27, 30.4, 45–47 supply the complete
control and execution interfaces. The quantitative application below
joins those suppliers without supplying an external runtime epoch.

The statements are ordinary conditional mathematics, not Lean kernel
certification. In particular, mathematical existence of a word encoding
does not establish physical availability of its execution services.

## 1. Original sources and the complete-memory contract

**Definition 1.1 (native tree and observations).** Use the free algebra
of finite nonempty ordered full binary trees

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle a,b\rangle=\langle\rho a,\rho b\rangle.
$$

An address is a word in $\{L,R\}^{*}$, read from the original root;
$\varepsilon$ is the root address. The total observation $r_u(p)$ reports
the root constructor at an empty remaining address, follows the selected
child at a branch, and reports $\mathsf{absent}$ whenever a nonempty
remaining address is submitted at a leaf. Thus its alphabet is
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.
In particular, an absent address is a legal query, and a branch reply is
different from a leaf label.

The two source primitives, as in SLH §1.3, are

$$
\mathsf{Read}(p):u\longmapsto(u,r_u(p)),\qquad
\mathsf{Update}:u\longmapsto(\rho u,\star).
$$

The acknowledgement $\star$ is independent of $u$. Operations are serial
on the same current tree. The interface supplies no reset, copy, move of
the root, inverse update, whole-subtree observation, old-version access,
or observation of size, duration or execution cost. Halt ends the run.
These are logical operation contracts; their physical supply is separate.

**Definition 1.2 (promised original leaf family).** Fix an integer
$h\ge1$, set $m=\lceil\log_2h\rceil$, and fix an ordered list of distinct
words $q_1,\ldots,q_h\in\{L,R\}^m$. Use the complete binary skeleton of
depth $m$. For every $x\in\{0,1\}^h$, let $u_x$ label $q_i$ by $\alpha$
when $x_i=0$ and by $\beta$ when $x_i=1$, and label every other skeleton
leaf by $\alpha$. Free syntax makes these $2^h$ trees distinct. The target
is the entire original ordered vector $x$, delivered once as
$\mathsf{Halt}(x)$; it is not the current vector of replies and is not a
stream accumulated outside the controller.

The skeleton, selected order, $h$ and all installed constants are common
to all sources. The observer starts in one common state, without any
source-dependent advice or free root observation. Membership in this
family is a declared source promise. On an unrestricted unknown tree it
would require separately acquired and certified evidence; the theorem
does not acquire that promise. SLH §31 explains the different contract
in which a common shape is certified by an actual earlier history.
The family here is not restricted to the orbit of $\alpha$: for example,
$\langle\alpha,\alpha\rangle$ is permitted at $h=2$, whereas the only
two-leaf term in that orbit is $\langle\beta,\alpha\rangle$.
At $h=1$, $m=0$, $q_1=\varepsilon$, and the family is $\{\alpha,\beta\}$.

**Definition 1.3 (conditional complete word).** For a fixed $h$, take a
fixed length $\ell\ge1$ and

$$
L_\ell=\{w\in\{0,1\}^\ell:w_jw_{j+1}=0\ (1\le j<\ell)\}.
$$

The Fibonacci cube $\Gamma_\ell$ has vertex set $L_\ell$ and edges
between words at Hamming distance one.

An installed subset $W\subseteq L_\ell$ is the entire mutable observer
state space. Every installed running or halt word counts in $|W|$,
including any installed unreachable word. Ambient words outside $W$
have no instruction rows. A fixed table maps each $w\in W$ to a literal
Read, Update, or $\mathsf{Halt}(z)$ with a fixed full output $z$.
For each primitive reply its response table immediately selects a word
of $W$ at Hamming distance at most one from $w$, and discards the reply.
There is no intermediate instruction or retained response.

This is the conditional service of FIB §45.1. Initialization, immutable
tables including output rows, instruction selection and address delivery,
primitive execution, immediate response writing and output are separately
supplied and charged. The only mutable observer field available to these
services is $w$. In particular, a decoded node pointer, address buffer,
program counter, phase, clock, epoch, history or response latch may not
persist outside it. If such a field is needed, this complete-word claim
does not describe that implementation. The evolving source is a distinct
device with only Definition 1.1's observation ports, not a free observer
register. Support sets, ranks and source labels in a proof are not ports.

## 2. The single quantitative application

**Theorem 2.1 (original recovery with every generation retained).** For
each family in Definition 1.2 consider the prescribed chronology

$$
p_i=q_iR^{\lfloor(i-1)/2\rfloor},\qquad
\mathsf{Read}(p_1),\mathsf{Update},\mathsf{Read}(p_2),\ldots,
\mathsf{Update},\mathsf{Read}(p_h),\mathsf{Halt}(x).
\tag{SLHC.1}
$$

For $h=1$, (SLHC.1) means just Read $p_1$ followed by Halt. The following
conclusions hold under Definitions 1.1–1.3.

1. The actual replies determine $x$. Every source makes exactly $h$
   Reads and $h-1$ genuine Updates, and reaches its first full-target halt
   after $H=2h-1$ primitives. Its unmerged actual-prefix tree, including
   every unary Update position and every first halt, has
   $N=3\cdot2^h-3$ vertices.
2. There is a faithful implementation with exactly $N$ installed words,
   exactly one legal bit change after each primitive, and no added
   primitive. It preserves on each same actual source the instructions,
   raw replies, device successors, original target and first halt. An
   explicit width is $5h-3$. The old FIB §47.2 width is
   $\max(1,N-1)=3\cdot2^h-4$. A classical supplier also yields $2h+5$
   for $h\ge2$, so an available width is

$$
U(h)=
\begin{cases}
2,&h=1,\\
\min\{3\cdot2^h-4,\ 5h-3,\ 2h+5\},&h\ge2.
\end{cases}
\tag{SLHC.2}
$$

3. Every deterministic policy that terminates correctly on every source,
   begins with source-independent memory and uses only the declared
   observations needs at least $h$ Reads on **each** source. This remains
   true with arbitrary deterministic internal computation and memory,
   arbitrary finite literal addresses, adaptive numbers of Updates and
   adaptive stopping. The lower-bound method is the original-cone
   separation of SLH §32.3 and [Graph Resource Separation][GRS] §6.3.
4. Any complete-word controller recovering the full target satisfies

$$
F_{\ell+2}\ge2^h+1,\qquad
F_0=0,\quad F_1=1,\quad F_{n+2}=F_{n+1}+F_n.
\tag{SLHC.3}
$$

   Consequently the minimum width has order $\Theta(h)$, both for this
   prescribed chronology and for the larger class of complete-word
   target-recovery controllers. This does not assert that $N$ is a
   minimum state count, or that an upper-bound constant is optimal.
5. On each prescribed run the submitted literal lengths have sum and
   maximum

$$
A_h=h\lceil\log_2h\rceil+\left\lfloor\frac{(h-1)^2}{4}\right\rfloor,
\qquad
P_h=\lceil\log_2h\rceil+\left\lfloor\frac{h-1}{2}\right\rfloor.
\tag{SLHC.4}
$$

   The displayed representation still has exponentially many installed
   table rows and $h2^h$ explicit target bits. These bills and all services
   of Definition 1.3 are separate from mutable width.

Proof is given in §§3–6. This is a joint quantitative application;
delayed probing, ancestor acquisition, graph state assignment and
operational transport retain the suppliers identified in §7.

## 3. Actual readouts, full chronology and exact supports

**Calculation 3.1 (guarded delayed leaf read).** Write

$$
T_0=\alpha,\quad T_1=\beta,\quad
T_{n+2}=\langle T_{n+1},T_n\rangle.
$$

The native substitution gives $\rho T_n=T_{n+1}$, by the two base cases
and induction through pairing. Every original skeleton branch persists.
Therefore, after $t$ actual Updates, the subtree at $q_i$ is precisely
$T_{t+x_i}$. This is SLH §32.2's original-ancestor decomposition with
free masks at the selected leaves and singleton masks elsewhere.

Put $t=2k+e$, $e\in\{0,1\}$. Before right descent $j+1$, for
$0\le j<k$, its subtree index is

$$
t+x_i-2j\ge2+e+x_i\ge2.
$$

Thus the current node is really a branch and has right child with index
two less. All $k$ descents exist, and the terminal subtree is $T_{e+x_i}$.
The resulting raw reply table is

| Epoch parity | Original bit $0$ | Original bit $1$ |
| --- | --- | --- |
| $t$ even | $\alpha$ | $\beta$ |
| $t$ odd | $\beta$ | $\mathsf{branch}$ |

These are the two-label specializations of SLH §55.2; the odd branch is
the root of $T_2$. None of the prescribed queries is absent. This argument
uses the known original-leaf promise. At an unrestricted original node,
odd-epoch $R^k$ cannot distinguish an original $\beta$ from an original
branch, and it is not the general guarded decoder of SLH §2.2.
Arithmetic alone cannot replace reachedness: descending $L$ from
$T_1=\beta$ is absent, regardless of an attempted index subtraction.

**Construction 3.2 (the actual finite control table).** For a bit string
$s$, introduce the following mathematical names for control vertices:

$$
Q_s\quad(0\le|s|<h),\qquad
U_s\quad(1\le|s|<h),\qquad
Z_x\quad(|x|=h).
$$

Let $K_h$ be the disjoint union of these three vertex sets.

At $Q_s$, Read $p_{|s|+1}$. Decode its two supported replies using the
row of Calculation 3.1 for $t=|s|$. A reply decoding to $b$ leads to
$U_{sb}$ if $|sb|<h$, and to $Z_{sb}$ otherwise. At $U_s$, execute Update
and let $\star$ lead to $Q_s$. At $Z_x$, execute $\mathsf{Halt}(x)$.
All other Read response rows hold the current vertex. Such rows are
legal total completions; correctness and termination are claimed on the
promised sources. No extra rejecting vertex is installed.

Initialization is $Q_\varepsilon$ for every $u_x$. Inductively, before
Read $i$ the current tree is $\rho^{i-1}u_x$ and the acquired prefix is
$x_1\cdots x_{i-1}$. Calculation 3.1 recovers the next original bit.
Read leaves the device untouched; the following Update, when present,
acts on that very tree. The next prefix is therefore correct. Only
vertices $Z_x$ halt, so the first halt follows the final Read, with no
earlier output checkpoint or additional internal action.

Each Update actually changes the tree, not merely its name. The supplied
right-spine quantity

$$
\kappa(\alpha)=0,\quad\kappa(\beta)=1,\quad
\kappa(\langle a,b\rangle)=2+\kappa(b)
$$

satisfies $\kappa(\rho u)=\kappa(u)+1$ by
`DelayedOriginalReadout.right_clock_iterate` at one update. Equality of
the two trees would contradict this equality. This mathematical witness
is not an observed clock. Hence all $h-1$ updates in (SLHC.1) are genuine.

**Verification 3.3 (same-source certificate and counts).** Write
$s\preceq x$ for the prefix relation. Exact supports are

$$
\begin{aligned}
C_{Q_s}&=\{(x,\rho^{|s|}u_x):s\preceq x\},\\
C_{U_s}&=\{(x,\rho^{|s|-1}u_x):s\preceq x\},\\
C_{Z_x}&=\{(x,\rho^{h-1}u_x)\}.
\end{aligned}
\tag{SLHC.5}
$$

Assign ranks $2(h-|s|)-1$ to $Q_s$, $2(h-|s|)$ to $U_s$, and zero to
$Z_x$. Initialization covers all $(x,u_x)$. Every action is legal.
Read preserves the device and restricts the prefix to its actual child;
Update advances the same device and preserves the original target.
Every supported edge decreases rank by exactly one, and each halt support
has its stated target. These are precisely FIB §27.2's obligations.

Every prefix occurs because every binary completion is allowed. There
are respectively $2^h-1$, $2^h-2$ and $2^h$ vertices of types $Q,U,Z$.
Their depths are $2|s|$, $2|s|-1$ and $2h-1$. Thus their union is the
actual primitive-prefix tree of height $H=2h-1$ and size $N=3\cdot2^h-3$.
Every Read vertex has two supported children; every Update vertex has
one. Keeping the latter distinguishes a just-read prefix from the same
prefix after its generation. The finite union of the actual paths is the
finite contract needed by FIB §30.4's tree bridge; the infinite ambient
tree algebra need not itself be made finite.

At $h=1$ this is one empty-address Read and two halts: $H=1$, $N=3$,
no Update. The symbols $s,t$ and these ranks describe the table and proof,
not extra fields supplied to its implementation.

## 4. Complete one-write realizations of this control tree

**Construction 4.1 (explicit width $5h-3$).** Reserve $H$ blocks in
primitive order, of lengths $2,1,2,1,\ldots,2$, with one permanent zero
between consecutive blocks and no outer separators. The initial word is
zero. On a Read edge set its unused block to $10$ or $01$ according to
the decoded bit $0$ or $1$; on an Update edge set its unused singleton to
$1$. Retain earlier blocks and leave later blocks zero. The word length is

$$
2h+(h-1)+(H-1)=5h-3.
\tag{SLHC.6}
$$

Each block has at most one $1$, and a zero separates consecutive blocks,
so every word belongs to $L_{5h-3}$. Each supported edge changes exactly
one bit. At primitive depth $d$, exactly $d$ blocks have been activated,
so different depths cannot share a word. At equal depth, distinct
prefixes differ in some completed Read block, and hence in their words.
This proves injectivity on all $N$ vertices, including unary positions
and halts. It is a level-coordinate state assignment in the classical
sense of Havel–Morávek, specialized to this alternating branching profile;
it is not a separate graph-theory result.

**Construction 4.2 (the classical $2h+5$ option).** Let $B_h$ be the
complete binary tree of all bit prefixes of length at most $h$, with an
edge from $s$ to $sb$. For $h\ge2$, Havel–Liebl's dichotomic-tree theorem
supplies an injective edge-preserving map
$g:B_h\to\{0,1\}^{h+2}$. Their Definition 7 and English summary specify
$2^{h+1}-1$ vertices, so their parameter is this edge depth $h$.
The theorem's hypothesis is $h>1$. Its embedding is a subgraph embedding,
not an induced or isometric one; only its upper direction is needed.

In $h+3$ binary coordinates assign

$$
\begin{aligned}
f(Q_s)&=(g(s),\ |s|\bmod2),\\
f(U_s)&=(g(s),\ (|s|-1)\bmod2),\\
f(Z_x)&=(g(x),\ (h-1)\bmod2).
\end{aligned}
\tag{SLHC.7}
$$

The $g$ coordinates distinguish different prefixes. The only two
vertices with the same prefix are $Q_s,U_s$ for $1\le|s|<h$, and their
last coordinates are opposite. Thus $f$ is injective. A Read from $Q_s$
changes one $g$ coordinate and preserves the last coordinate, since its
child has prefix length $|s|+1$. An Update from $U_s$ to $Q_s$ changes
only the last coordinate. Every original edge, including each unary
edge, is therefore still a one-coordinate edge.

Now use the explicit zero-interleaving map from the proof of
Cabello–Eppstein–Klavžar Proposition 3.1:

$$
z_1\cdots z_{h+3}\longmapsto z_1\,0\,z_2\,0\cdots0\,z_{h+3}.
\tag{SLHC.8}
$$

Its images avoid $11$, it is injective, and it preserves a one-coordinate
change. The length is $2(h+3)-1=2h+5$. The parity coordinate is inside
the counted word. No extra vertices of a binary cube are installed.
Proposition 3.1's isometric-dimension inequality is not being applied to
the nonisometric $g$; its displayed coordinate map is sufficient.

For comparison, the actual tree has $N-1$ edges. CEK Corollary 3.6 gives
its isometric embedding in the Fibonacci cube of dimension $N-1$,
exactly the supplier used by FIB §47.2. This stronger preservation of
distances supplies the old width but imposes no lower bound on our
merely edge-preserving codes. Choose the shortest of the three codes
once, as immutable compilation data. For $h\ge2$, $5h-3<N-1$; the
inequality starts at $h=2$ and its difference increases by $3\cdot2^h-5$
when $h$ increases by one. The $2h+5$ option improves $5h-3$ for $h\ge3$.
For $h=1$, Construction 4.1 uses exactly $00,10,01$ at width two.

**Verification 4.3 (word-only execution and first halt).** For any chosen
code $e:K_h\to L_\ell$, install exactly $W=e(K_h)$. The instruction at
$e(v)$ is the instruction of Construction 3.2 at $v$. For a supported
reply $o$, the immediate write sends it to $e(v_o)$, its encoded child.
For an unsupported reply it stays at $e(v)$. Both choices are legal,
and all table rows are defined on their declared response alphabets.
Only a fixed table depends on $e^{-1}$; there is no saved decoded pointer.
Additional adjacency among codewords creates no permission to jump to
them: the response table selects the sole successor.

Fix one original $u_x$. Initially the source is $u_x$ and the word is
$e(Q_\varepsilon)$. Suppose that its source and encoded vertex agree
with Construction 3.2. Its selected instruction is the same. Executing
that instruction on the same tree gives exactly the same raw reply and
device successor. The response service immediately writes the child's
word and discards the reply. This proves the invariant at the next
primitive, including each fixed-acknowledgement Update. Induction ends
at the same $Z_x$, and no earlier vertex halts. The supports (SLHC.5) and
ranks transport through $e$ as in FIB §45.4; they are never consulted.

All $N$ installed words occur on some source path. There are exactly
$H$ response bit changes per path, no extra state or internal action,
and the first Halt is the next instruction after the last write.
Initialization and output are not included in those $H$ writes.

## 5. Acquisition and memory necessity for the original target

**Argument 5.1 (the supplied cone method on adaptive actual runs).**
Consider any deterministic competitor in Theorem 2.1(3), without imposing
a memory or single-write restriction. Fix a finite common history. The
policy's control, next instruction and number $t$ of completed Updates
are identical on all sources with that history; deterministic internal
work preserves this agreement. The current source is $\rho^t u_x$.

A literal of length less than $m$ reads a skeleton branch and is
constant. Every other literal has exactly one length-$m$ original leaf
prefix. An unselected prefix enters a fixed copy of $T_t$; a selected
prefix $q_j$ enters $T_{t+x_j}$. Its suffix reply consequently depends
on at most $x_j$, even if it is absent or a branch. This is the precise
common-history locality needed from SLH §32.2. It remains valid when
earlier replies determine $t$.

Fix now a terminating run on $u_x$. For each $j$, flip only $x_j$ to
obtain another allowed original source. If no Read on this run separates
that pair at its actual epoch, induction over all its events gives the
same instructions, replies, Updates, internal work and stopping choice
on the flipped source. The full output would agree although its target
differs. Hence every $j$ requires a separating Read on this one run.
Locality says one Read can separate at most one such single-bit flip.
There must be at least $h$ Read occurrences.

This is the per-source argument of SLH §32.3 with all selected leaves
required, and the adaptive-epoch first-separation method of GRS §6.3.
It counts arbitrary literal depths and arbitrary amounts of finite
internal work. Informative update refusals, timing, additional ports or
source-dependent initial information would invalidate the premises;
nontermination is not a successful comparator. No randomized-error claim
is made. For the target alone, reading $q_1,\ldots,q_h$ at epoch zero
already attains $h$ Reads with no Updates. Thus the $h-1$ generations
are requirements of (SLHC.1), not an acquisition advantage or an
unconditional lower bound on Update count.

**Argument 5.2 (full-output word capacity).** A halt word selects one
fixed full vector. All $2^h$ vectors occur, so they require at least
$2^h$ distinct halt words, even if other histories are merged. The common
initial word cannot halt correctly for this nonconstant target; it is
distinct from every halt word. Thus $|W|\ge2^h+1$.

The numbers of no-$11$ words of lengths zero and one are $1,2$.
For $\ell\ge2$, partition them into those starting with $0$ and with
$10$ to get $a_\ell=a_{\ell-1}+a_{\ell-2}$. Hence
$|L_\ell|=F_{\ell+2}$ and (SLHC.3) follows. With
$\varphi=(1+\sqrt5)/2$, the same recurrence and
$\varphi^2=\varphi+1$ give $F_{\ell+2}\le\varphi^{\ell+1}$, so

$$
\ell\ge\log_\varphi(2^h+1)-1>h\log_\varphi2-1.
\tag{SLHC.9}
$$

Together with (SLHC.2), this proves both stated $\Theta(h)$ conclusions.
It also excludes one fixed finite width for all unbounded $h$.
Prefix-injective encodings have the additional capacity obligation
$F_{\ell+2}\ge N$, but the exhibited $N$ is not thereby a minimum over
behavior quotients or different protocols. At $h=1$, capacity rules out
length one and the length-two construction attains the minimum.

## 6. Separate resource coordinates and recovery boundaries

**Accounting 6.1 (logical addresses and installed representation).** Each
Read in (SLHC.1) submits $m+\lfloor(i-1)/2\rfloor$ letters. Pairing the
terms in $\sum_{t=0}^{h-1}\lfloor t/2\rfloor$ gives $r(r-1)$ for $h=2r$
and $r^2$ for $h=2r+1$, namely $\lfloor(h-1)^2/4\rfloor$. The largest
term is the last, proving (SLHC.4), including both zero lengths at $h=1$.
These are submitted address lengths, not execution times or a claim
about an uncounted mutable address buffer.

The explicit table has $N$ instruction rows, of which $2^h$ are full-vector
halt rows. Materializing their targets alone stores $h2^h$ bits. With
typed reply alphabets there are $4(2^h-1)+(2^h-2)=5\cdot2^h-6$ response
rows, including the unsupported Read replies. An inline address table
repeats $p_i$ at $2^{i-1}$ Read rows, for payload

$$
\sum_{i=1}^h2^{i-1}
\left(m+\left\lfloor\frac{i-1}{2}\right\rfloor\right).
$$

A separately charged immutable dictionary can share the $h$ addresses,
whose payload is $A_h$, but needs references and a decoder. Listing word
keys uses $N\ell$ bits before other fields. These are properties of the
displayed representation, not lower bounds on every immutable program.
The choice of code does not reduce its $N$ installed states.

**Accounting 6.2 (source, setup and physical services).** The complete-word
statement has the cost decomposition of FIB §45.2. One may write its
separate service bill as

$$
C_{\rm promise}+C_{\rm source}+C_{\rm compile}+C_{\rm tables}
+C_{\rm init}
+\sum_{d=0}^{H-1}
\bigl(C_{\rm decode,d}+C_{\rm address,d}+C_{\rm primitive,d}
+C_{\rm write,d}\bigr)
+C_{\rm decode,H}+C_{\rm output}(x).
\tag{SLHC.10}
$$

The entries can be resource vectors. Address charges apply to Reads;
primitive charges include real source growth and Updates. No listed
service is inferred free from word length, and initialization may install
the whole common initial word under its separately supplied permission.
Output delivers $h$ target bits; a physical serializer requiring a cursor
or buffer must meet Definition 1.3 rather than quietly add mutable state.
Similarly, finite table existence supplies no efficient discovery,
synthesis, lookup or circuit implementation claim.

For clarity, even the literal tree being updated can be large. The
supplied Fibonacci recurrence gives $F_{n+1}$ leaves in $T_n$. At epoch
$t$, the present free tree has

$$
L_x(t)=(2^m-h)F_{t+1}+\sum_{i=1}^h F_{t+x_i+1}
\tag{SLHC.11}
$$

leaves and $2L_x(t)-1$ nodes. Each original leaf occurrence is replaced
by its own indicated term, which proves the formula by summing leaf
counts. This counts literal occurrences, not minimal physical storage
under possible shared representations. Neither this count nor $H$ prices
the implementation of a global substitution or a physical Read.

**Boundary 6.3 (what is and is not recovered).** The acquired vector and
the supplied skeleton determine $u_x$; with an explicitly supplied epoch
they also determine $\rho^t u_x$. The theorem instead executes each paid
Read and Update, preserving their actual replies, even when a reply
could be predicted from another representation. It does not replace
raw acquisition by computation, or interpret a computed history as
certification that physical events occurred.

The shallow original-leaf menu need not recover original labels after
generation: at $t\ge2$ every $r_{\rho^t u_x}(q_i)$ is a branch. The
suffix probes in (SLHC.1) supply the missing distinctions. Nor does
current geometry alone supply an unknown elapsed epoch: original
$\alpha$ after one Update and original $\beta$ after zero Updates both
present $\beta$ but have different original labels. Here every required
protocol position is already represented by the complete word; no
epoch input is inferred from the device. Arbitrary native four-way
decision trees, optimum constants, total physical space or time, and
recovery outside the declared source and observation contracts are not
consequences of this application.

## 7. Exact suppliers and attribution

**Attribution 7.1 (acquisition and operational suppliers).** The
`repo-derived` contribution is Theorem 2.1's joint quantitative consumer:
the specified evolving-source chronology, its exact primitive tree,
linear complete-word realizations and task capacity are attached to
the same original vectors. The following existing results supply its
mathematical components.

| Supplier | Exact correspondence and limit |
| --- | --- |
| [SLH §§1.1–1.3, 31.1–31.2][SLH] | Free ordered trees, four-valued literal reads, serial same-register substitution, and fixed-shape leaf products. Here the shape is a declared promise; the earlier-history certification service is not acquired for free. |
| SLH §32.2 | Set $C_{q_i}=\{\alpha,\beta\}$ and all other original-leaf masks to $\{\alpha\}$. Every mixed prefix filters only one original cone at a Read; Update preserves original labels. |
| SLH §32.3 | Its per-source leaf-flip proof supplies one required separating Read per independent needed leaf. Argument 5.1 states the correspondence for arbitrary adaptive epochs and the full-vector target. |
| SLH §32.4 | All selected free leaves are used, so the acquired distinctions determine the original vector and, with the known skeleton, the original tree. Evidence values do not certify that events occurred. |
| SLH §32.5 | Finite expansion by acquired prefix, progress and update count; complete memory and installed constants remain distinct costs. Constructions 3.2 and 4.1–4.2 give this consumer's explicit $H,N,\ell$ without external progress fields. |
| SLH §55.2 | At epoch $2k$ use $R^k$ to separate $\alpha/\beta$; at epoch $2k+1$ the same probe gives $\beta/\mathsf{branch}$. This uses the two-label promise, not the unrestricted-tree certificate for an original $\beta$. |
| [Native Discovery §7.1][NDR] | The known-shape stationary benchmark already charges one read per unknown independent leaf label. The present target alone still admits that zero-Update strategy. |
| [Graph Resource Separation §6.3][GRS] | Same-run first separation under adaptive real Updates and arbitrary literal queries. Here the alternatives change one original selected cone each, rather than that supplier's coupled two-copy target. |
| [FIB §§26–27 and 30.4][FIB] | Complete Moore control, supports and ranks, and the finite actual-prefix bridge. In this application $I$ is a singleton, $Z=\{0,1\}^h$, initial pairs are $(x,u_x)$, and (SLHC.5) supplies the exact certificates. |
| FIB §§45.1–45.4 | Entire-word semantics, separately priced services and injective supported-edge encoding. The compiled set is exactly $e(K_h)$; unsupported rows legally hold the word. |
| FIB §§46–47 | Fixed-table encoding is different from solving a task by another table; permitted prefix refinement preserves actual paths. Section 47.2 supplies the unchanged $N$-word, $\max(1,N-1)$-width alternative and same-source first-halt transport. |

**Attribution 7.2 (actual Lean supplier interfaces).** The source
declarations below supply the named definitions and mathematical
interfaces. They do not constitute a Lean implementation of Theorem 2.1.

| Source declarations | Correspondence |
| --- | --- |
| [`ActualTreeReadoutAcquisition.Address`, `Reply`, `readout`][LEAN-READ] | Address `false/true` means $L/R$; source `.of true/.of false` means $\alpha/\beta$. Thus the numerical bit $x_i$ here corresponds to source Boolean $x_i=0$, not to the same Boolean convention. `readout` includes absent strict extensions of leaves. Its original passive policy is not an Update policy. |
| [`DelayedOriginalReadout.right_clock_iterate`, `right_clock_readout`, `address_clock_bounds`][LEAN-DELAY] | $N=t$, `rights k` is $R^k$, and the clock of an original selected leaf is $x_i$. These supply the delayed right-spine intervals, original-node persistence and the witness that Update changes the source. |
| `DelayedOriginalReadout.original_presence_guard`, `original_decoder_correct`, `original_decoder_service` | General original-node recovery has a supplied epoch and its own parent guard and probe list. It is broader than the promised-leaf readout, and does not supply an external epoch to this controller. |
| [`GuardedPhaseExecution.run_transport_iff`, `GuardedPhaseExecution.run_halt_unique`][LEAN-RUN] | These declarations are in `NativeExecutionTransport.lean`. Use the equivalence from vertices to installed image words, the identity address map, and for each fixed original $x$ the observation $\operatorname{obs}_x(t,p)=r_{\rho^t u_x}(p)$. Instruction and observation compatibility must hold; the epoch is a run-semantics coordinate, not an instruction input. The generic halt carries no full target label: output correctness is supplied separately by $C_{Z_x}$ and the word's fixed Halt row. |

**Attribution 7.3 (primary classical suppliers).** All graph results in
this table are `literature-attested`. Their application does not assert
new general graph bounds or worldwide originality.

| Primary source | Used statement and checked parameter match |
| --- | --- |
| Ivan Havel and Jaroslav Morávek, *B-valuations of graphs*, Czechoslovak Mathematical Journal 22 (1972), 338–351, [DOI 10.21136/cmj.1972.101102][HM] | The introduction defines injective binary state assignment with one-coordinate transitions; Propositions 1–2, pp.340–341, give its coordinate-parity and adjacency-preserving embedding interpretation. It is not an induced or isometric requirement. This is the classical state-assignment meaning used in §4 and already consumed by FIB §45.4. |
| Ivan Havel and Petr Liebl, *O vnoření dichotomického stromu do krychle*, Časopis pro pěstování matematiky 97 (1972), 201–205, [primary text][HL] | Definition 7 and the main theorem, p.203, with the explicit prefix-tree definition in the English summary, p.205: the complete binary tree of edge depth $h>1$ embeds in $Q_{h+2}$. Only this upper bound supplies $g$ in (SLHC.7); its minimum-dimension result for that different tree is not transferred to the actual primitive tree. |
| Ivan Havel and Petr Liebl, *Embedding the polytomic tree into the n-cube*, Časopis pro pěstování matematiky 98 (1973), 307–314, [primary text][HL-P] | Remark 4, p.312, uses separate edge-coordinate sets for successive levels. This is attribution for the level-coordinate method behind Construction 4.1, not a new general forest chapter or a native realizability claim. |
| Sergio Cabello, David Eppstein and Sandi Klavžar, *The Fibonacci Dimension of a Graph*, Electronic Journal of Combinatorics 18 (2011), P55, [DOI 10.37236/542][CEK-DOI], [arXiv:0903.2507v1][CEK] | Proposition 3.1's explicit zero-interleaving map supplies (SLHC.8), independently of an isometric hypothesis on $g$. Corollary 3.6, pp.7–8 of the preprint, gives $\operatorname{fdim}(T)=|E(T)|$ for a finite tree, supplying the old width $N-1$. No isometric lower bound is asserted for the new encodings. |

The uniform proofs above discharge the mathematical correspondence under
the declared services. They supply neither physical realization of those
services nor a formal kernel check of this joint consumer. Acquisition
and encoding mathematics remain attributed to the listed owners.

[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[FIB]: FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md
[GRS]: RECURSIVE_RELATIONAL_OBSERVATION_GRAPH_RESOURCE_SEPARATION.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DISCOVERY_AND_RETAINED_CONTEXT.md
[LEAN-READ]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[LEAN-DELAY]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[LEAN-RUN]: ../../../D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.lean
[HM]: https://dml.cz/bitstream/handle/10338.dmlcz/101102/CzechMathJ_22-1972-2_15.pdf
[HL]: https://dml.cz/bitstream/handle/10338.dmlcz/117765/CasPestMat_097-1972-2_9.pdf
[HL-P]: https://dml.cz/bitstream/handle/10338.dmlcz/117800/CasPestMat_098-1973-3_16.pdf
[CEK-DOI]: https://doi.org/10.37236/542
[CEK]: https://arxiv.org/pdf/0903.2507v1

## 追加锚（本行以下为增补区）

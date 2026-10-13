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

## 8. Original parity with complete counted control

**Definition 8.1 (the parity consumer on the same sources).** Retain
Definitions 1.1–1.3, including every free ordered tree $u_x$ for
$x\in\{0,1\}^h$, $h\ge1$, the known complete depth-$m$ skeleton,
$m=\lceil\log_2h\rceil$, the fixed ordered distinct leaves
$q_1,\ldots,q_h$, and the common source-independent initialization.
Only the declared target changes: put

$$
P_0(x)=0,\qquad P_i(x)=x_1\oplus\cdots\oplus x_i,
\qquad \pi(x)=P_h(x),
\tag{SLHC.12}
$$

where $\oplus$ is addition modulo two. Deliver the single original bit
$\mathsf{Halt}(\pi(x))$, once, with no earlier output. The prescribed
chronology is exactly (SLHC.1), with its final target replaced by
$\pi(x)$: Read $p_i=q_iR^{\lfloor(i-1)/2\rfloor}$ and, if $i<h$,
perform one Update before the next Read. In particular, no stationary
replacement is permitted in this prescribed consumer. The full-vector
target of Theorem 2.1 remains a different task.

The source promise admits all $2^h$ assignments, not a single $\rho$
orbit. Its acquisition and certification on an unrestricted unknown
source remain separately supplied. A Read returns the raw constructor
in $\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$; in particular a
strict extension beyond a leaf returns absent, and branch is not a bit
label. Update substitutes in the same actual current tree and returns
only $\star$. All literal depths are allowed by the port. No source
identity, size, duration, reset, copy or other observation is supplied.

The fixed-length no-$11$ word is the entire mutable observer. Its row
selects one fixed, fully materialized literal Read, Update or fixed-output
Halt. Each primitive reply immediately selects a hold or at most one
legal bit change and is discarded. All running and halt words count;
no external PC, epoch, phase, latch, pointer, address buffer, history or
target stream is available. Initialization, immutable instruction,
address and output data, table lookup and literal delivery, source
preparation and growth, primitive execution, immediate writing,
compilation and output are the conditional, separately paid services of
Definition 1.3 and FIB §§45.1–45.2. In particular a service implementation
that retains another mutable field does not satisfy this contract.

**Theorem 8.2 (the native parity and full-vector width comparison).**
For every family of Definition 8.1 there is a complete-word realization
of its prescribed parity chronology with exactly

$$
|W|=4h-1,\qquad
\ell_h=
\begin{cases}
2,&h=1,\\
2\lceil\log_2h\rceil+3,&h\ge2.
\end{cases}
\tag{SLHC.13}
$$

Every installed word is reached on some promised source. On each source
the realization preserves every prescribed instruction, raw reply and
actual device successor. It makes exactly $h$ Reads, $h-1$ genuine
Updates and $2h-1$ response bit changes, with its first fixed-target
Halt immediately after primitive $2h-1$. It inserts no other primitive
or intermediate write phase. All typed response rows, including
unsupported replies, are legal.

For the parity target alone, every deterministic policy that terminates
correctly on every promised source needs at least $h$ actual Reads on
each source. This lower bound permits arbitrary deterministic finite
internal work and memory, arbitrary finite literal depths, adaptive
Updates and stopping, and recurrence of control states at different
source epochs. For a complete-word comparator, additionally require that
its entire counted word select one fixed materialized literal at every
query row and one fixed target at every halt row. Then its installed set
contains at least $h$ distinct query words and two distinct halt words;
consequently

$$
|W|\ge h+2,\qquad F_{\ell+2}\ge h+2,\qquad
\ell\ge\log_\varphi(h+2)-1,
\quad \varphi=(1+\sqrt5)/2.
\tag{SLHC.14}
$$

Thus the least attainable complete mutable width has order
$\Theta(\log(h+1))$, both for the prescribed chronology and for the
larger class of correct complete-word parity controllers that may choose
their own Reads and Updates. Theorem 2.1's full-vector target still has
order $\Theta(h)$ on the identical source family. These statements do
not assert a minimum installed-state count, an optimal width constant,
efficient synthesis, or a bound on total storage or physical time.

The displayed parity table has $2h-1$ Read rows, $2h-2$ Update rows and
two Halt rows, hence $4h-1$ instruction rows and $10h-6$ typed response
rows. Its per-run address sum and peak remain $A_h,P_h$ of (SLHC.4).
Inlining its literals stores $2A_h-m$ address letters; its two fixed
halt payloads store two target bits in total. The remaining separate
resource bills are specified below as part of the same construction.

Proof. First justify the task's history compression; only afterwards
encode the resulting control table injectively.

At the $i$th Read there have been $t=i-1$ Updates. SLH §32.2 and
Calculation 3.1 give the actual subtree $T_{t+x_i}$ at $q_i$. If
$t=2k+e$, all $k$ right descents are reached: before descent $j+1$,
$0\le j<k$, the index is $t+x_i-2j\ge2+e+x_i$. The endpoint is
$T_{e+x_i}$. Thus use precisely the following supported decoder:

| $(i-1)\bmod2$ | Raw reply for $b=0$ | Raw reply for $b=1$ |
| --- | --- | --- |
| $0$ | $\alpha$ | $\beta$ |
| $1$ | $\beta$ | $\mathsf{branch}$ |

This is the promised-leaf specialization of SLH §55.2; it is not a new
general original-node decoder. The odd-epoch branch is the root of
$T_2$, and absent is never supported at these prescribed addresses.
The same raw $\beta$ decodes differently in the two rows. The epoch
used to specify the table is fixed by its control position, not supplied
as a runtime observation.

For any finite bit string $s$, write $P(s)=\bigoplus_{j=1}^{|s|}s_j$,
with $P(\varepsilon)=0$. A previously read prefix's parity determines
the residual target as a function of any unread continuation $y$:
$\pi(sy)=P(s)\oplus P(y)$. At the same protocol position, two prefixes
with equal parity and the same unread continuation produce the same
future raw replies under the prescribed schedule. Indeed, every later
query enters a different, still unread original cone, and its reply
depends only on that cone's bit and the common number of Updates.
Previously read cones may still differ as trees, but are not queried
again by this schedule. Each remaining Update is still performed on
each source itself. This verifies the residual-task identification,
including its future instructions and final output, without identifying
the two device states.

Concretely, take the prefix table of Construction 3.2 with terminal
label changed from $x$ to $\pi(x)$. Project its vertices by

$$
Q_s\longmapsto Q_{|s|+1,P(s)},\qquad
U_s\longmapsto U_{|s|+1,P(s)},\qquad
Z_x\longmapsto Z_{\pi(x)}.
\tag{SLHC.15}
$$

Install the disjoint mathematical state sets

$$
\begin{aligned}
\mathcal Q_h&=\{Q_{1,0}\}\cup
 \{Q_{i,p}:2\le i\le h,\ p\in\{0,1\}\},\\
\mathcal U_h&=\{U_{i+1,p}:1\le i<h,\ p\in\{0,1\}\},\\
\mathcal Z_h&=\{Z_0,Z_1\},\qquad
K_h^\pi=\mathcal Q_h\sqcup\mathcal U_h\sqcup\mathcal Z_h.
\end{aligned}
\tag{SLHC.16}
$$

At $Q_{i,p}$ execute Read $p_i$. A supported reply decoding to $b$
leads to $U_{i+1,p\oplus b}$ when $i<h$, and to $Z_{p\oplus b}$
when $i=h$. At $U_{i+1,p}$ execute Update and let $\star$ lead to
$Q_{i+1,p}$. At $Z_p$ execute the fixed instruction $\mathsf{Halt}(p)$.
Initialize at $Q_{1,0}$. The two unsupported Read replies at each query
row hold its current state. Update has only its acknowledgement row;
Halt has no primitive-response rows.

For each prefix row the next literal and supported decoder depend only
on its length, while adjoining $b$ changes $P(s)$ to $P(s)\oplus b$.
Hence (SLHC.15) respects each Read transition, each actual Update
transition and each unsupported hold. It respects the newly declared
terminal label. Induction on the original actual prefix proves that
this compressed table runs on the same device with the same primitive
history. This is the classical ordered parity residual of
[Randal E. Bryant, *Graph-Based Algorithms for Boolean Function
Manipulation*, Definitions 1–2 and §§3.1–3.2][BRYANT-PARITY]
(author manuscript pp.4, 7–8), whose ordinary decision graph has
$2h+1$ vertices, together with the $2h-2$ required
Update positions. The layer index in that decision graph selects an
input variable; its two possible parity values per layer do not supply
a two-state autonomous literal-address controller here.

Exact supports, with original target and current device kept together,
are

$$
\begin{aligned}
C_{Q_{i,p}}&=\{(\pi(x),\rho^{i-1}u_x):P_{i-1}(x)=p\},\\
C_{U_{i+1,p}}&=\{(\pi(x),\rho^{i-1}u_x):P_i(x)=p\},\\
C_{Z_p}&=\{(p,\rho^{h-1}u_x):\pi(x)=p\}.
\end{aligned}
\tag{SLHC.17}
$$

Each set ranges over all $x\in\{0,1\}^h$ satisfying its condition.
At $Q_{1,0}$ all sources are present; $Q_{1,1}$ is not installed.
Every other listed prefix-parity class and both final parities have
actual completions. Before Read $i$, the actual control is
$Q_{i,P_{i-1}(x)}$ and the device is $\rho^{i-1}u_x$. The decoded
reply is $x_i$, so the post-Read pair belongs to the stated Update or
Halt support. Update sends the same device to $\rho^i u_x$ and enters
$Q_{i+1,P_i(x)}$. This proves both support inclusions and actual
reachability of every listed state.

Give $Q_{i,p}$ rank $2(h-i)+1$, $U_{i+1,p}$ rank $2(h-i)$, and $Z_p$
rank zero. Every supported primitive decreases rank by one. Each action
is legal; each halt support has exactly its fixed output. These are
FIB §§26–27's complete Moore control and support–rank obligations, with
singleton initial-history set, $Z=\{0,1\}$, and initial pairs
$(\pi(x),u_x)$. The finite union of actual paths satisfies FIB §30.4's
finite-prefix premise although the ambient tree algebra is infinite.
Only the final Read enters a halt, after $2h-1$ primitives. Each Update
changes the tree: the right-spine witness in §3.2 obeys
$\kappa(\rho u)=\kappa(u)+1$. This supplies no clock port. Unsupported
holds assert legal completion only; there is no off-promise termination
claim.

It remains to realize all of this control, including instruction type
and progress, in one word. For $h\ge2$ put $d=\lceil\log_2h\rceil$
and let $g_i$, $1\le i\le h$, be the $d$-bit reflected Gray word of
$i-1$. Equivalently it is the padded binary word for
$(i-1)\mathbin{\mathrm{xor}}\lfloor(i-1)/2\rfloor$. These are distinct
and consecutive words differ in one coordinate. This finite path
assignment is supplied by [Havel–Morávek, Example 4, p.343][HM] and
[Frank Gray, *Pulse code communication*, US2632058A, reflected-code
description][GRAY-PATH]. The independent-field
upper construction in [Contextual Zeckendorf, Definition 97 and
Theorem 99][CSZ-GRAY] applies to the containing box with capacities
$(h-1,1,1)$, using $d+2$ binary coordinates. Its separate lower bound
for a full box is not transferred to our control subgraph.

Set $e_i=(i-1)\bmod2$ and $S_i(p)=(p,p\oplus e_i)$, including
$i=h+1$. In those $d+2$ binary coordinates assign

$$
\begin{aligned}
f(Q_{i,p})&=(g_i,S_i(p)),\\
f(U_{i+1,p})&=(g_i,S_{i+1}(p)),\\
f(Z_p)&=(g_h,S_{h+1}(p)).
\end{aligned}
\tag{SLHC.18}
$$

Different stage columns have different $g_i$. At a fixed column $i$,
the query pair has square-coordinate XOR $e_i$, and the post-Read pair
has XOR $e_i\oplus1$. The two pairs are disjoint and each distinguishes
$p$. The initial column omits $Q_{1,1}$; the final post-Read pair is
the pair of halts. Thus $f$ is injective on all
$(2h-1)+(2h-2)+2=4h-1$ states.

On a Read decoding to $b$, the square coordinates change by
$(b,b\oplus1)$, so exactly one coordinate changes and the Gray block
does not. On an Update from $U_{i+1,p}$ to $Q_{i+1,p}$, the square
coordinates are identical, and precisely the one coordinate between
$g_i$ and $g_{i+1}$ changes. This is an injective edge assignment into
the Gray path times a square, in the adjacency-preserving sense of
Havel–Morávek Propositions 1–2. It requires neither induced adjacency
nor preservation of all distances.

Apply the already supplied zero-interleaving map from the proof of
[Cabello–Eppstein–Klavžar, Proposition 3.1][CEK]:

$$
J(z_1\cdots z_{d+2})=z_1\,0\,z_2\,0\cdots0\,z_{d+2},
\qquad E=J\circ f.
\tag{SLHC.19}
$$

Each adjacent pair of positions contains a permanent zero; hence every
image avoids $11$. The map retains every data coordinate, so is
injective and preserves each one-coordinate change. Its width is
$2(d+2)-1=2d+3$. Only the $4h-1$ image words are installed. This uses
CEK's explicit coordinate map, not its isometric-dimension inequality
on the nonisometric Gray assignment.

For $h=1$ use $E(Q_{1,0})=00$, $E(Z_0)=01$, $E(Z_1)=10$.
Here $q_1=p_1=\varepsilon$; raw $\alpha,\beta$ select $01,10$
respectively, and branch and absent hold $00$. This is a legal
width-two, three-word table with one Read, one bit change and no Update.

Install the instruction of $v$ at $E(v)$, and its response successor
$E(v')$ at the row indexed by $(E(v),o)$. Unsupported Read responses
hold $E(v)$; these have zero changes, and all supported rows have
exactly one. No rows are installed at ambient words outside $E(K_h^\pi)$.
Extra adjacencies between installed words do not authorize additional
transitions. The inverse of $E$ only specifies the immutable tables;
there is no retained decoded control or address. This satisfies FIB
§45.4 after the history projection has already been justified. FIB
§47.2's unmerged-prefix construction is an alternative general
existence supplier, not the logarithmic bound in (SLHC.13).

For each fixed original $x$, induction now maintains the pair
$(\rho^t u_x,E(v))$ against the parity table. The word selects the same
instruction; the same device gives the same raw reply and successor;
the immediate table write gives exactly $E(v')$ and discards the reply.
The supports and ranks in (SLHC.17) transport through the bijection
$K_h^\pi\simeq E(K_h^\pi)$. Hence instructions, responses, actual
successors and first halt agree, including every genuine Update. Every
supported edge has different endpoints, giving exactly $2h-1$ bit
changes. Neither initialization nor output is counted among those
response writes.

The interface of [`GuardedPhaseExecution.run_transport_iff`][LEAN-RUN]
has precisely this bijective control parameter, identity address map,
and observation $\operatorname{obs}_x(t,p)=r_{\rho^t u_x}(p)$.
Instruction and observation compatibility are supplied above, and its
`run_halt_unique` concerns halt endpoints. Its unlabeled halt does not
establish the output bit; $C_{Z_p}$ and the fixed output row do that.
The noninjective prefix projection (SLHC.15) is not an instance of that
equivalence interface. Likewise
[`ActualTreeReadoutAcquisition.readout`][LEAN-READ] and
[`DelayedOriginalReadout.right_clock_readout`,
`right_clock_iterate`, `address_clock_bounds`][LEAN-DELAY] retain
§7.2's conventions: address Booleans false/true mean $L/R$, while source
Booleans true/false mean $\alpha/\beta$, the reverse of the numerical
original bit here. These are supplier interfaces, not a Lean
certification of this consumer.

For necessity, adapt Argument 5.1's SLH §§32.2–32.3 and GRS §6.3
original-cone first-separation proof to the changed target. Fix any
correct deterministic policy in the theorem's larger acquisition class
and one actual terminating run on $u_x$. For each $j$, the assignment
$x^{(j)}$ obtained by flipping just $x_j$ is permitted and has target
$\pi(x^{(j)})=1\oplus\pi(x)$.

At any common history the runs have the same internal computation and
number $t$ of Updates. A literal shorter than $m$ sees a fixed skeleton
branch. Any other literal has a unique length-$m$ prefix. An unselected
prefix enters the same $T_t$ on both sources; prefix $q_j$ enters
$T_{t+x_j}$. Thus at a common epoch any literal's raw reply, including
branch or absent, depends on at most one selected original bit.

If no Read on the fixed run separates $x$ from $x^{(j)}$ at that run's
actual epoch, induction over its events gives the same instructions,
replies, Updates, finite internal work and halt on both sources. They
would deliver the same output, contradicting their opposite targets.
Therefore each $j$ has a first separating Read on this very run. That
Read must lie in $q_j\{L,R\}^{*}$. These $h$ original cones are
pairwise disjoint, so their witnesses are $h$ different Read occurrences.
This proves the per-source $h$ bound, uniformly over adaptive epochs,
all finite literal depths and arbitrary allowed internal memory. It
uses parity's sensitivity to each original leaf in place of the
suppliers' different full-vector or coupled-copy targets. The separately
supplied known-shape benchmark in Native Discovery §7.1 retains its own
scope; no unknown-shape discovery cost is imported.

For the width inference, choose one such witness in each cone on the
same actual run. One query word selects one fixed materialized literal,
whose length-$m$ prefix cannot belong to two cones. The witnesses
therefore use at least $h$ distinct query words. Both parity values
occur in the whole promised family; they require two distinct
fixed-output halt words, disjoint from all query words. This proves
$|W|\ge h+2$. Argument 5.2 supplies $|L_\ell|=F_{\ell+2}$ and
$F_{\ell+2}\le\varphi^{\ell+1}$, giving (SLHC.14). In particular,
width one cannot handle $h=1$.

This reasoning imposes no stationary repeated-word exclusion. A word
may recur at a changed source epoch; its literal still belongs to the
same original cone. The width implication even survives additional
finite internal transitions between counted states, provided all their
mutable memory is counted and the entire query or halt state still
selects its one fixed literal or fixed output. Arbitrary source-dependent
address generation from an uncounted field would violate that premise.
Two-valued output capacity alone supplies only two halt words and would
not prove the growing lower bound. No randomized or extra-port claim
is made. The prescribed $h-1$ Updates are not a universal Update lower
bound for parity alone: at epoch zero the $h$ original leaves suffice.
Combining the width necessity with (SLHC.13) proves both claimed orders.

For the separate resource counts, each run submits exactly the same
literals as §6.1, so

$$
A_h=hm+\left\lfloor\frac{(h-1)^2}{4}\right\rfloor,
\qquad P_h=m+\left\lfloor\frac{h-1}{2}\right\rfloor.
\tag{SLHC.20}
$$

Both are zero at $h=1$. Counting the four reply entries of every query
row and the one acknowledgement of every Update row gives
$4(2h-1)+(2h-2)=10h-6$ typed response entries. Of these, $6h-4$ are
supported one-bit transitions and $4h-2$ are unsupported holds. The
halt rows have no reply entries. Listing all word keys explicitly costs
$(4h-1)\ell_h$ bits; listing every response successor as a full word
costs $(10h-6)\ell_h$ further bits, before tags, indexing and framing.
The first literal occurs at one query row and every later literal at
two, so inline address payload is

$$
|p_1|+2\sum_{i=2}^h|p_i|=2A_h-m.
\tag{SLHC.21}
$$

A shared immutable dictionary instead stores the $h$ distinct literals
in $A_h$ letters, plus references, framing and separately paid lookup
and delivery. It does not provide a free mutable address buffer. The
two installed target payloads contain two bits; a run delivers one.
These are displayed-representation bills, not minimum immutable
program-size claims.

The source-size bill is inherited unchanged from §6.2: at epoch $t$,

$$
L_x(t)=(2^m-h)F_{t+1}+\sum_{i=1}^hF_{t+x_i+1}
\tag{SLHC.22}
$$

counts leaves and $2L_x(t)-1$ counts literal nodes. No observer encoding
removes these actual source Updates or their growth. The service bill
is (SLHC.10) with $H=2h-1$ and final term
$C_{\rm output}(\pi(x))$: promise certification, source preparation,
compilation, immutable tables, initialization, each instruction lookup,
literal delivery on Reads, Read or Update execution, immediate writing,
and final lookup/output all retain their own costs. Costs may be
vectors. In particular the displayed address payload is already
$\Theta(h^2)$; logarithmic mutable width is neither logarithmic total
storage nor a physical execution tariff. Finite table existence gives
no efficient compilation, synthesis or hardware realization result.

Finally, compare the targets without changing the sources or operations.
The displayed full-vector table has $3\cdot2^h-3$ installed words and
$h2^h$ explicit target bits, as in §6.1; these are its construction
counts, not a minimum state theorem. Its $2^h$ different full outputs
force the separate $\Theta(h)$ width of §5.2. The parity table forgets
distinctions irrelevant to its residual target while retaining every
acquisition and generation. For $h\ge2$, every parity fiber has
$2^{h-1}$ vectors: choose the first $h-1$ bits freely and the last is
fixed by the requested parity. In particular $00\cdots0$ and
$110\cdots0$ have the same parity and final word, but different
original vectors and trees. Even with the common final epoch $h-1$
given, the native probe $q_1R^{\lfloor(h-1)/2\rfloor}$ distinguishes
their final devices by the displayed raw decoder. This is a statement
about possible observations of those devices, not a resumption of
their absorbing halts.

For $h\ge3$ the same pair of first two bits already merges at
$Q_{3,0}$, while an extra probe into the first original cone would
distinguish its two possible devices. Consequently (SLHC.15) is a
quotient of prescribed controller histories for this task, not equality
under arbitrary future native observations. Existing complete-behavior
quotient results such as [`ControlledBehaviorUniversality`][BEHAVIOR]
and [`ReachableBehaviorMinimality.finite_state_minimality`][BEHAVIOR-MIN]
quantify over all their declared input continuations (and the latter
requires finite carriers and candidate reachability). Their general
principles do not identify these trees or certify a minimum state
count for this restricted task. At $h=1$ the parity and vector targets
coincide. The logarithmic-versus-linear gap for growing $h$ is therefore
task-sensitive complete memory, not mutual recovery of parity and the
original vector. $\square$

The `repo-derived` content of Theorem 8.2 is the quantitative composition
on these native sources: the justified task compression, its explicit
complete one-write realization retaining every generation, and the
query-cone support bound on counted words. Bryant's parity residual,
Gray/Havel–Morávek path assignment, the contextual product construction,
CEK zero interleaving, SLH/GRS acquisition arguments and FIB execution
transport remain their respective suppliers. In particular, FIB §46.2
already prevents inferring single-write realizability from capacity
alone; for $h=2$, suppressing the Update positions of (SLHC.16) yields
the classical parity graph, with two final-query vertices sharing three
neighbors, its initial query and two halts, the same forbidden
$K_{2,3}$ pattern. The actual Update positions and (SLHC.18) discharge
the different edge obligation here. No new standalone Gray, product,
streaming or quotient result, worldwide originality, or Lean kernel
certification is asserted.

[BRYANT-PARITY]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
[GRAY-PATH]: https://patents.google.com/patent/US2632058A/en
[CSZ-GRAY]: CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md
[BEHAVIOR]: ../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean
[BEHAVIOR-MIN]: ../../../D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality.lean

## 追加锚（本行以下为增补区）

## 9. Unknown entry: active and static memory for the same parity task

**Definition 9.1 (unpadded source, unknown entry and complete control).**
Fix a public finite full ordered binary skeleton $S$ with exactly $h\ge1$
leaves, in a fixed order with addresses $q_1,\ldots,q_h$. Every leaf is
independently labelled: for $x\in\{0,1\}^h$ put

$$
u_x=S[T_{x_1},\ldots,T_{x_h}],\qquad
E(x,t)=\rho^t u_x=S[T_{t+x_1},\ldots,T_{t+x_h}],\qquad
\pi(x)=\bigoplus_{i=1}^h x_i.
\tag{SLHC.23}
$$

Here $T_n=\rho^n\alpha$, with the conventions of Calculation 3.1.
All $2^h$ originals are admitted. The original root remains fixed.
Entry lag $t$ is unknown; a bounded installation is given only the
source-independent promise $0\le t\le T$, for an installed integer
$T\ge0$. It receives neither the actual $t$ nor an acquired old record.
The output is one fixed-bit Halt with the original $\pi(x)$.
This changes Definition 1.2's source contract: $S$ need not be complete
or balanced, and there are no spare known-$\alpha$ leaves. In particular,
its actual leaf depths cannot be replaced by $\lceil\log_2h\rceil$.
Establishing and certifying this promise is a separate service, as in
SLH §§31.1–31.3; the promise itself is not an observation history.

Use precisely Definition 1.1's fully materialized literal Read with
four raw replies and same-source genuine Update with constant
acknowledgement, and Definition 1.3's immediate response contract.
One fixed-length no-$11$ word contains all mutable instruction choice,
phase, progress, retained reply information, accumulator and halts.
All installed words count, including unreachable ones. Every typed
response row chooses a hold or one bit change, and discards the raw
reply. No external PC, epoch, address buffer, latch, history or counter
is available. The constructions below have only Read, Update and Halt
rows, with no internal instructions. An ignored root Read is still an
actual Read. For lower bounds the comparison class may additionally
use deterministic internal rows with finitely many actual steps on
each successful run, provided their entire mutable state is counted,
they obtain no source input, and each query word still selects one
fixed literal. Static means zero actual Updates on every promised run;
unreachable installed Update rows do not change that definition.

Write

$$
K=\lceil T/2\rceil,\quad M=h(K+1),\quad
 d_i=|q_i|,\quad D=\max_i d_i,\quad A_S=\sum_i d_i,
\quad c(x,t)=\sum_i\bigl((t\bmod2)\mathbin\oplus x_i\bigr).
\tag{SLHC.24}
$$

The integer $c$ is an analysis coordinate, not a stored count. Immutable
literals and tables, preparation and growth of the source, compilation,
initialization, lookup, address delivery, native operation execution,
response writing and final output remain separate paid services.

**Theorem 9.2 (same-task active/static complete-memory comparison).**
For every $S$ with even $h\ge2$ and every finite $T$, the bounded task
in Definition 9.1 has the following conditional native realizations.

| Quantity | Active realization | Static realization |
| --- | --- | --- |
| Complete mutable width | $2\lceil\log_2(h+1)\rceil+13$ | $2\lceil\log_2(M+1)\rceil+9$ |
| Installed words, including two halts | $8h+8$ | $8M+2$ |
| Actual Reads | $3h+2k+c$ | $3M+c$ |
| Actual Updates | $2k$ | $0$ |
| Internal steps and internal writes | $0$ | $0$ |
| Response bit changes | $3h+4k+c$ | $3M+c$ |
| Submitted address-length sum | $A_S+hK+k(d_1+K)$ | $(K+1)A_S+hK(K+1)/2$ |
| Maximum submitted literal length | $D+K$ | $D+K$ |

Here $k=K-\lfloor(t+x_1)/2\rfloor\ge0$ and $c=c(x,t)$.
All counts are for the actual same-source run through its first Halt,
including every polling and routing Read; initialization and output
are additional. The active maxima for Reads, Updates, response changes
and address sum are respectively

$$
4h+2K,\qquad 2K,\qquad 4h+4K,\qquad
A_S+hK+K(d_1+K).
\tag{SLHC.25}
$$

They are jointly attained at $t=0$, $x=1^h$. The static maxima for
Reads and response changes are $3M+h$, jointly attained on that same
entry; its address sum and maximum are independent of the source.
Thus the active realization uses $O(h+T)$ actual Reads and $O(T)$
genuine Updates, with width independent of $T$.

Every successful complete-word controller on this identical family
has at least $h$ distinct query words and two halts. Every successful
static controller has at least $h\lceil(T+1)/3\rceil$ distinct query
words and two halts. Consequently

$$
\begin{aligned}
F_{\ell+2}&\ge h+2&&\text{in the active comparison class},\\
F_{\ell+2}&\ge h\lceil(T+1)/3\rceil+2&&\text{in the static class}.
\end{aligned}
\tag{SLHC.26}
$$

Under the complete-state and fixed-literal premises, the corresponding
minimum widths therefore have orders
$\Theta(\log(h+1))$ and $\Theta(\log(h(T+1)+2))$.
The upper constructions also recover parity for every $h\ge1$ when
$T=0$. For odd $h$ and $T\ge1$ the full task is impossible by the
existing exact entry collisions. On unbounded lags, every individual
finite even-$h$ source admits finite actual acquisition with growing
addresses and workspace, but no one finite complete fixed-literal
installation succeeds for all $t$, even with adaptive Updates and
counted internal work. These are different quantifiers, not a claim
of a uniform acquisition time. The source and installation bills below
are part of the comparison; no optimal constants or physical time or
total-storage conclusion is asserted.

Proof. The proof first fixes the supplied semantic boundary, then
constructs the two entire native tables and compares their resources.

### 9.3. Supplied fibers and the target's admissible regimes

Apply [Atomic Boundary Trichotomy, Theorems 9.2–9.3 and
Propositions 9.4, 9.6][ABT-ENTRY] with original leaf count $h$, restricted
to the one shape $S$. Its exact whole-current-tree fibers give

$$
E(x,t)=E(y,s)\quad\Longleftrightarrow\quad
 t+x_i=s+y_i\quad(1\le i\le h).
\tag{SLHC.27}
$$

Besides identical histories, the only pairs are
$(1^h,j)$ and $(0^h,j+1)$, when both lags are allowed. This is a
specialization of that owner, not a new collision classification.
Its equality-fiber criterion makes original parity well defined on
current trees exactly in the even-$h$ or $T=0$ regimes stated above.
For odd $h$ the identical entries $E(1^h,0)=E(0^h,1)$ require opposite
outputs. ABT §9.4 already supplies indistinguishability under all future
adaptive current-source experiments: equal complete entries give the
same next action and reply, and every common Update preserves tree
equality. Internal computation supplies no missing historical fact.

In the supplier's mixed case, acquired clocks $n_i=t+x_i$ give
$t=\min_i n_i$ and $x_i=n_i-\min_j n_j$. At a uniform current clock
$n$, the candidates are $(0^h,n)$ and $(1^h,n-1)$, with invalid lags
removed. Thus on $[0,T]$ the interior $1\le n\le T$ is ambiguous,
while $n=0$ and $n=T+1$ are singletons of that restricted domain.
At $h=1$ there are no mixed originals and the collision is simply
$\rho\alpha=\beta$; at $T=0$ the root Read distinguishes both labels.
Uniform-only even-$h$ parity is constant zero, and mixed-only $h=2$
parity is constant one. Neither restricted task supplies a lower bound
for the full independent-label task. This is not a quotient identifying
every mixed vector with its complement.

A genuinely supplied known original label $b$ at a reached reference
leaf gives $t=n_{\rm ref}-b$ after its current clock has actually been
acquired. Adding such a leaf changes $S$; fixing one of the $h$ labels
changes independence. A retained reference requires prior acquisition,
binding to the same source and paid retention. Its public address alone
supplies no reference label or clock. ABT §§9.3–9.4 distinguish this
historical information from a local counter initialized at unknown
entry. Semantic recovery does not authenticate an omitted event history.
The retained/acquired-row interfaces of [Native Alpha Recut Memory,
§§11–13, 16.1][NAR-ENTRY] keep their additional inputs and different
targets; no such row or reference is supplied to Definition 9.1.

### 9.4. One actual alignment and the complete active word

Install $p_i=q_iR^K$. Poll $p_1$; on absence perform exactly two real
Updates and poll again. Stop polling at its first $\alpha$ or $\beta$.
Thereafter read $p_2,\ldots,p_h$ once each, with no more Updates.
This uses [CAR, Theorem 13.3][CAR-ENTRY] and [Native Phase Synthesis,
§§5–6][NPS-ENTRY] as polling suppliers, with the following source
correspondence. Their authenticated acquired fiber and full-row target
are not the source promise or target here.

At the $j$th polling visit the actual first cone is
$T_{t+x_1+2j}$, by SLH §32.2. The supplied right-clock law
$\kappa(T_n)=n$ and right-spine readout of
[`DelayedOriginalReadout`][LEAN-DELAY] give

$$
r_{T_n}(R^K)=
\begin{cases}
\mathsf{absent},&n<2K,\\
\alpha,&n=2K,\\
\beta,&n=2K+1,\\
\mathsf{branch},&n\ge2K+2.
\end{cases}
\tag{SLHC.28}
$$

This includes $K=0$. The original $q_i$ are reached and preserved;
absence refers to a strict extension in their cone, not to a fictional
subtree. SLH §55.2 supplies the corresponding reached leaf separation.
Since $t+x_1\le T+1\le2K+1$, exactly
$k=K-\lfloor(t+x_1)/2\rfloor$ retries occur. Put
$e=(t+x_1)\bmod2$. The first accepted rank is $2K+e$, and the current
common epoch is

$$
\tau=t+2k=2K+e-x_1.
\tag{SLHC.29}
$$

For every cone at this same actual source, the residual
$\tau+x_i-2K=e+x_i-x_1$ lies in $\{-1,0,1,2\}$.
Those values give, respectively, absent, $\alpha$, $\beta$, branch.
Define only for this acquired window

$$
\chi(\mathsf{absent})=\chi(\beta)=1,\qquad
\chi(\alpha)=\chi(\mathsf{branch})=0.
\tag{SLHC.30}
$$

It equals the rank parity on the window. A negative residual at $K=0$
would require a negative actual rank and is unreachable. There is no
claim that $\chi$ decodes parity at an arbitrary saturated branch or
arbitrarily deep absent address. Each accepted bit is
$(t\bmod2)\oplus x_i$, because Updates occurred in pairs. Their XOR
is $\pi(x)\oplus((h\bmod2)(t\bmod2))$, and their integer sum is $c$.
This proves the required target in the stated regimes.

The entire immediate controller is as follows. Let
$d=\lceil\log_2(h+1)\rceil$ and $g_i$ be the padded $d$-bit reflected
Gray word of $i$, for $0\le i\le h$. Use the ordinary binary fields

$$
(g_i,a,L_{0,0},L_{0,1},L_{1,0},L_{1,1},v_1,v_2),
\tag{SLHC.31}
$$

with $d+7$ coordinates. The four $L$ coordinates are either all zero
or have exactly one occupied position, denoted $L_{b,r}$. The phase
$v=v_1v_2$ uses $00,01,11,10$. Apply the credited zero-interleaving
map $J$ of (SLHC.19), giving width $2d+13$ and no adjacent ones.
The tuple below is notation for that one word, not auxiliary state.
Install exactly these sets of tuples:

$$
\begin{aligned}
Q(i,a)&=(g_i,a,0,00),&&0\le i\le h,\ a\in\{0,1\},\\
B(i,a,b)&=(g_i,a,L_{b,i\bmod2},00),
 &&0\le i<h,\ a,b\in\{0,1\},\\
C(i,b)&=(g_{i+1},b,L_{b,i\bmod2},00),
 &&0\le i<h,\ b\in\{0,1\},\\
V(a,v)&=(g_0,a,0,v),&&a\in\{0,1\},\ v\in\{01,11,10\}.
\end{aligned}
\tag{SLHC.32}
$$

Initialize at $Q(0,0)$. At $Q(h,a)$ halt with fixed output $a$.
At $Q(i,a)$ for $i<h$ read $p_{i+1}$. Its four response rows are:

- At $i=0$, absent selects $V(a,01)$, branch holds $Q(0,a)$,
  and $\alpha,\beta$ select $B(0,a,a\oplus\chi(o))$.
- At $i>0$, every reply $o$ selects $B(i,a,a\oplus\chi(o))$.

At $V(a,01)$ perform Update and select $V(a,11)$; at $V(a,11)$
perform Update and select $V(a,10)$; at $V(a,10)$ perform Read
$\varepsilon$, with all four replies selecting $Q(0,a)$.
Every word with a nonzero latch performs Read $\varepsilon$ and
ignores its raw value. For its current stage $i$, accumulator $a$
and occupied $L_{b,r}$, all four replies select the following one change,
in the displayed priority order:

1. If $a\ne b$, change $a$ to $b$.
2. Otherwise, if $i\bmod2=r$, change $g_i$ to $g_{i+1}$.
3. Otherwise clear $L_{b,r}$.

This defines all installed rows, including those with empty actual
support. In the second case $i<h$ by (SLHC.32); thus it never requests
an uninstalled $g_{h+1}$. In the third case it is at a $C$ word and
returns to $Q(i,b)$. Branch at the pilot is an unsupported legal hold;
no off-promise termination claim is made.

For all $h$, including either side of a power of two, the $g_i$ are
distinct and consecutive values differ in one coordinate, by the
reflected-path suppliers [Gray][GRAY-PATH] and [Havel–Morávek,
Example 4][HM]. The new application needs no wraparound edge.
The four sets in (SLHC.32) are disjoint: $Q$ has empty latch and phase,
$V$ has nonzero phase, and at any common stage the $B$ latch index has
$r=i\bmod2$, while a $C$ latch has the opposite index. Within each
set all remaining parameters are retained. Hence there are exactly
$2(h+1)+4h+2h+6=8h+8$ distinct installed words. $J$ retains all data
coordinates and preserves one-coordinate changes, using only the map
in [Cabello–Eppstein–Klavžar, Proposition 3.1][CEK]; its general
isometric-dimension assertion is not applied to this control graph.

Every listed response changes exactly one coordinate except the two
unsupported pilot branch holds. In particular a decoded bit is first
retained in a counted latch position, and the raw reply is discarded.
An accepted query then uses two root Reads to advance and clear, plus
one root Read exactly when the accumulator must flip. The stage-parity
latch index distinguishes before from after the Gray advance without
an external phase. The polling return has four actual edges: absence,
Update, Update, root Read. Omitting that paid Read would contract the
supported triangle of the original polling table, which cannot have
an injective immediate one-bit encoding in a cube. No path is contracted
here, and no source-preserving row is called an Update.

For actual-source correctness, before accepted stage $i+1$ the complete
word is $Q(i,a)$ with $a$ equal to the XOR of the first $i$ accepted
bits. Initially $i=a=0$ and the source is $E(x,t)$. A pilot retry
returns to that same word on $E(x,t+2j)$ after exactly its two genuine
Updates. Equation (SLHC.28) makes the nonnegative remaining retry
count decrease by one. Once it is zero, the pilot accepts; thereafter
all routing Reads leave $E(x,\tau)$ unchanged. Each latch route
terminates after $2+\chi(o)$ root Reads and enters the next $Q$ with
accumulator $a\oplus\chi(o)$. These facts prove the invariant by
induction and make $Q(h,\pi(x))$ the first halt in the stated regimes.
Every Update changes the actual tree, since the supplied all-tree clock
identity is $\kappa(\rho u)=\kappa(u)+1$.

This discharges FIB §§26–27's actual closed-loop obligations: supports
are the reached target/current-tree pairs at each complete word; they
are preserved by the listed actions and successors. The retry descent
and finite latch and stage descents establish termination. Equivalently,
on these supports the deterministic number of remaining primitives is
a natural-valued strictly decreasing rank of the current tree and word.
It is proof data, not an observer clock. FIB §45 then applies to the
already expanded table and its injective encoding. The equivalence
in [`GuardedPhaseExecution.run_transport_iff`][LEAN-RUN] uses identity
addresses and $\operatorname{obs}_{x,t}(j,p)=r_{\rho^{t+j}u_x}(p)$;
its $j$ counts genuine Updates only. Each routing Read remains a Read
at that same $j$. The fixed halt row and invariant supply the output,
while `run_halt_unique` supplies the matching endpoint interface.
Neither this reference nor FIB §47's finite-history alternative provides
a free instruction pointer or certifies a contracted transition.

### 9.5. Same-source costs and the static complete table

There are $h+k$ data Reads, $k$ polling-return root Reads, and
$2h+c$ latch-routing root Reads. There are $2k$ Updates. This proves
the active operation and bit-change counts in the theorem. Only data
Reads contribute address length, giving its sum and maximum. Since
$0\le k\le K$ and $0\le c\le h$, the displayed upper counts follow;
$t=0,x=1^h$ gives $k=K,c=h$, verifying their joint attainment on one
actual realization, including $T=0$.

For the static upper bound, install the ordered list of $M=h(K+1)$
data queries

$$
q_1,q_1R,\ldots,q_1R^K,\quad
q_2,q_2R,\ldots,q_2R^K,\quad\ldots,\quad
q_h,q_hR,\ldots,q_hR^K.
\tag{SLHC.33}
$$

Make every query in this order with no Updates. In cone $i$, put
$k_i=\lfloor(t+x_i)/2\rfloor\le K$. Formula (SLHC.28) shows branch
for $s<k_i$, one $\alpha$ or $\beta$ at $s=k_i$, and absent for
$s>k_i$. Accumulate $\psi(o)=\mathbf1_{\{o=\beta\}}$ at every
query. The cone contributes exactly $(t+x_i)\bmod2$, so the final
accumulator has the same required parity and makes $c$ flips overall.
No reply outside the terminal window is passed through $\chi$.

Here is its complete immediate table, with all progress counted.
Replace $h$ by $M$ in the $Q,B,C$ sets of (SLHC.32), use
$d_s=\lceil\log_2(M+1)\rceil$ Gray coordinates, and omit the phase
coordinates and all $V$ words. At each $Q(i,a)$, $i<M$, read entry
$i+1$ of (SLHC.33); every one of its four replies selects
$B(i,a,a\oplus\psi(o))$. The latch rows use exactly the three
root-Read rules above, and $Q(M,a)$ halts with $a$. Initialize at
$Q(0,0)$. The same disjointness argument, including the opposite
before/after latch indices, proves injectivity on exactly $8M+2$
words and closure of every response row. Zero interleaving gives
width $2d_s+9$. All native transitions on all four rows change one
bit; there are no holds, Updates or internal rows in this table.
The stage/latch invariant gives its actual first halt after $3M+c$
Reads. Thus the static upper bound introduces neither an uncounted PC
nor an internal-path contraction. Summing (SLHC.33) proves the stated
address costs. This deliberately complete scan is a width upper bound,
not a claim of minimum Read count.

The two explicit installations have the following separate data bills.
The active table contains $8h+2$ Read rows, four Update rows and two
Halt rows. Of its Read rows, $2h$ contain the data literals and $6h+2$
contain the empty root literal. It has exactly $32h+12$ typed response
entries. Listing all word keys and response successors in full costs
$(8h+8)\ell_a$ and $(32h+12)\ell_a$ bits respectively, before tags,
framing or indexes. Inline data literals occupy $2(A_S+hK)$ address
letters; a shared immutable dictionary occupies $A_S+hK$ letters,
plus its references and framing. The empty root word contributes zero
letters but has a representation and lookup cost. Two halt payloads
store two bits, of which one is output on a run.

The static table has $8M$ Read rows, two Halt rows and $32M$ typed
response entries. Its $2M$ data-query rows hold two copies of (SLHC.33);
the other $6M$ Read rows are routing rows at the root. Put
$A_s=(K+1)A_S+hK(K+1)/2$. Inline literal payload is $2A_s$ letters,
or $A_s$ letters with a separately charged shared dictionary. Full word
keys and response successors occupy $(8M+2)\ell_s$ and $32M\ell_s$
bits before representation overhead; its halt payloads again occupy
two bits. At $h=1$ a data literal can itself be the empty root word;
these occurrence and payload formulas still hold. Neither table stores
a source-dependent address, lookup cursor or decoded instruction
outside its complete word. The fixed $S,T$ and any other retained
public representation also have an installation charge; these formulas
are for the displayed explicit rows and literals, not a minimum
immutable-storage theorem.

For source storage, at any actual epoch $v$ the exact leaf count and
literal node count are

$$
L_x(v)=\sum_i F_{v+x_i+1},\qquad |E(x,v)|=2L_x(v)-1.
\tag{SLHC.34}
$$

Both constructions start with $v=t$. The active source ends at
$v=\tau$, so its peak is $L_x(\tau)$, since substitution does not
decrease leaf count. A uniform bound is $hF_{2K+3}$ leaves. More
precisely, for $T\ge1$ its exact worst peak is
$F_{2K+2}+(h-1)F_{2K+3}$, attained at $t=1$,
$x=(0,1,\ldots,1)$: (SLHC.29) gives $\tau=2K+1$ when $t$ is odd
and $x_1=0$; then at most $h-1$ labels are one. In all other cases
$\tau\le2K$ and the peak is at most $hF_{2K+2}$, which is no larger.
For $T=0$ the peak is $h$. The run jointly attaining (SLHC.25) has
only $hF_{2K+2}$ leaves at its peak; the larger source maximum for
$T\ge1$ is a different realization and is not a joint extremum of all
coordinates. The coarse $hF_{2K+3}$ bound is not asserted attained.

The static source remains $E(x,t)$, of size (SLHC.34); its worst peak
is $hF_{T+2}$ leaves, attained at $t=T,x=1^h$. When $T$ is even this
also has $c=h$ and attains the static operation maximum. When $T$ is
odd, $c=0$ there; attaining $c=h$ instead requires all bits to have
parity opposite $t$, and gives fewer leaves than $hF_{T+2}$. Thus the
static source and operation maxima are not jointly attained for odd
$T$. Node bounds in each case are twice the leaf bounds minus one.
These literal source sizes do not assert a physical tree-storage
representation or a tariff for executing substitution.

For either table, if the actual nonhalt primitive sequence is
$(w_j,a_j,o_j)_{j<N}$, its remaining service bill has the form

$$
\begin{aligned}
&C_{\rm promise}+C_{\rm prepare}(E(x,t))+C_{\rm compile}
 +C_{\rm install}+C_{\rm init}\\
&\quad+\sum_{j<N}\left(C_{\rm lookup}(w_j)
 +\mathbf1_{\{a_j=\mathsf{Read}(p_j)\}}C_{\rm deliver}(p_j)
 +C_{\rm native}(a_j,E_j)+C_{\rm write}(w_j,o_j)\right)\\
&\quad+C_{\rm lookup}(w_N)+C_{\rm output}(\pi(x)).
\end{aligned}
\tag{SLHC.35}
$$

The terms can be resource vectors. Initial source preparation includes
whatever supplies the entry; entry $t$ is not counted as post-entry
Updates. Compilation is common and source independent, with its work
and workspace charged outside the runtime word. The displayed table
selection and whole-literal delivery are conditional services, not
physical circuits furnished by the code. A serial address emitter or
output mechanism needing a persistent cursor requires another complete
state accounting. There is no inference of physical latency, energy,
total storage or efficient synthesis from the mathematical word width.

### 9.6. Lower bounds on the same parity task

Fix a correct deterministic policy and one actual run at entry $(x,t)$.
Flip only $x_i$, at that same entry lag. SLH §§31–32's original-cone
correspondence applies to this public full skeleton with every leaf
mask equal to $\{\alpha,\beta\}$; no shape-acquisition service is being
transferred. At a common history the actual number $a$ of post-entry
Updates agrees, and cone $j$ contains $T_{t+a+x_j}$. Every literal
either ends at a fixed internal skeleton node or has the unique form
$q_j s$. Thus a query depends on at most one original bit, for arbitrary
suffixes, including absence. If no Read on the chosen run separates
its flipped alternative in cone $i$, induction through all Reads,
Updates and counted finite internal work gives the same complete run
and fixed Halt on both sources. Their parities differ, a contradiction.

Consequently at least one separating Read in each of the $h$ disjoint
cones occurs on this very run. One complete query word selects only
one fixed literal, so these witnesses require at least $h$ different
query words. Both output bits occur, requiring two further halt words.
This is the SLH §32.3 and §8.2 same-run separation argument with the
unknown common entry carried in the actual-source correspondence;
it does not infer a growing bound from two-valued output alone.
Adaptive Updates and recurrence of control words on different current
trees do not invalidate it.

For the stronger static bound, for each $i$ and each $t=0,\ldots,T$
compare the actual entries $E(0^h,t)$ and $E(e_i,t)$, where $e_i$ is
one only at $i$. They differ in target and only in the fillings
$T_t,T_{t+1}$ of cone $i$. A successful zero-Update table must have
some query word in that cone whose literal distinguishes those two
fillings; otherwise all its responses and internal transitions agree
through the first halt. This applies even if unused Update rows are
installed.

Use the existing exact atomic guard [CAR, (CAR.23)] and its monotonicity
argument in Theorem 13.4, (CAR.68), with atomic index $n$ and no
additional shift. For a nonempty suffix $s$ of weight
$w(s)=\#_L(s)+2\#_R(s)$ ending in $e$, it is reached in $T_n$ exactly
when $n-w(s)\ge2-\omega(e)$, with $\omega(L)=1,\omega(R)=2$.
When reached its residual index is $n-w(s)$ and its reply is $\alpha$
at zero, $\beta$ at one, branch above one. In particular, ending in
$L$ skips $\alpha$; zero residual there is absent. The empty suffix
has replies $\alpha,\beta,\mathsf{branch}$ at indices $0,1,\ge2$.
These are actual guarded readouts, not a reached-subtree convention
applied to an absent word.

It follows from this supplier that, as $n$ increases, a fixed suffix's
reply moves monotonically through
$\mathsf{absent}<\alpha<\beta<\mathsf{branch}$, with at most three
changes. Explicitly, a suffix ending in $R$ can separate $T_t,T_{t+1}$
only at $t=w(s)-1,w(s),w(s)+1$; one ending in $L$ only at
$t=w(s),w(s)+1$; the empty suffix only at $t=0,1$. Only nonnegative
$t$ in the promised range count. Therefore one query word covers at
most three of the $T+1$ required comparisons for its one original
cone. Each cone needs at least $\lceil(T+1)/3\rceil$ query words.
Adding the two halts proves the second bound in (SLHC.26), without
any restriction on static literal lengths, Read count or finite
internal work. CAR §13.4's separate deep-comb address-budget premise
is not imported: here cone locality itself isolates the changed bit.

The previously supplied $|L_\ell|=F_{\ell+2}\le\varphi^{\ell+1}$
turns these counts into width lower bounds. Since
$K+1=\Theta(T+1)$, the two explicit complete-word upper bounds give
the asserted matching orders. At $T=0$ the same arguments hold for
odd $h$ as well. The active and static resource vectors need not
dominate one another: at $T=0$ the static displayed word is shorter,
while at $T=2$, $t=0$, $x=1^h$, the active table uses $4h+2$
Reads and two Updates, and the static table uses $7h$ Reads and none.
For $h\ge2$ each saves a different operation coordinate. None of these
construction counts asserts optimal Reads or optimal constants.

### 9.7. Sourcewise acquisition and the unbounded installation boundary

The same clock suppliers give a finite actual protocol on every finite
entry without a lag bound: keep the source stationary and, in each
cone $i$, read $q_i,q_iR,q_iR^2,\ldots$ until the first leaf reply.
At $k_i=\lfloor(t+x_i)/2\rfloor$ that reply is $T_{(t+x_i)\bmod2}$;
all preceding replies are branch. Hence every such finite entry yields
its actual rank $2k_i+((t+x_i)\bmod2)$ after finite Reads. Even-$h$
parity is the XOR of the terminal bits, and on mixed originals the
already supplied minimum-clock decoding additionally gives $x,t$.
The exact costs are

$$
Q=\sum_i(k_i+1),\quad U=0,\quad
A=\sum_i\left((k_i+1)d_i+\frac{k_i(k_i+1)}2\right),\quad
P=\max_i(d_i+k_i).
\tag{SLHC.36}
$$

A direct parity procedure can retain the current materialized address,
its stage and depth counters, and one accumulator, using
$O(D+t+\log(h+1))$ bits of workspace on that input; any retained full
rank vector costs extra. Address production, computation, elementary
writes, initialization and output are charged separately. This is an
algorithm with growing workspace and an unbounded literal repertoire,
not a complete controller of one fixed word length. It supplies actual
acquisition, but no certificate of the original source promise or of
an earlier event history.

Conversely fix any one finite complete fixed-literal observer and let
$W_*=\max(\{0\}\cup\{w(p):p\text{ is an installed Read literal}\})$.
The all-finite-source permanent saturation law in [CAR, Theorem 11.2,
(CAR.47)][CAR-ENTRY] and [Native Resource Frontier,
Theorem 2.1][NRF-ENTRY] gives

$$
t\ge W_*+2\quad\Longrightarrow\quad
r_{\rho^{t+a}u_x}(p)=\mathsf{branch}
\quad\text{for every installed }p,\ x,\ a\ge0.
\tag{SLHC.37}
$$

Choose that same finite entry lag for $x=0^h$ and $x=e_1$.
The targets differ, but every subsequent Read on either evolving source
returns branch, every Update has the same acknowledgement, and every
internal row has no new input. Induction gives identical complete
control and action histories. If the common path halts, its fixed
output is wrong for one source; if it does not, sourcewise termination
fails. This uses permanent equality of the installed response menu,
not equality of the two trees or a stationary repeated-state argument.
It assumes no uniform stopping time. A genuinely supplied reference
leaf does not defeat this fixed-literal saturation when lag is unbounded.

Thus the positive finite-installation assertion is
$\forall T\ \exists C_{S,T}\ \forall x\ \forall t\le T$, whereas the
excluded assertion is $\exists C_S\ \forall x\ \forall t\ge0$.
Native Phase Synthesis §§5–6 already separates installation-dependent
literal costs and durations from state-only bounds; its acquired domain
is not substituted for this one. The growing-address protocol and the
bounded installations respect this quantifier distinction. $\square$

The `repo-derived` content of Theorem 9.2 is the joint quantitative
comparison for Definition 9.1's identical original-parity family:
actual alignment, the complete immediate tables, and the lag-dependent
static query-word requirement with its native resource correspondence.
ABT owns the exact collisions and historical-information boundary;
SLH owns the original-cone and reachedness suppliers; CAR/NPS/NRF own
polling, guarded atomic monotonicity and saturation. The present theorem
does not restate CAR's acquired full-row task or §8.2's known-start
prescribed-generation task. Their hypotheses and conclusions remain
unchanged, as does §2.1's full-vector target and its different output
capacity. No logarithmic full-vector recovery follows here.

Gray/Havel–Morávek adjacency and CEK zero interleaving are
`literature-attested` proof suppliers, as cited in §8.2 and above;
only their indicated maps are used. The finite-state control
interpretation is FIB §§26–27, 45–47, with each native instruction
retained in the expanded table. The Lean interfaces cited in §7.2
retain their Boolean convention: address false/true means $L/R$,
source true/false means $\alpha/\beta$, opposite to the numerical
original bits here. Mathematical source correspondence and conditional
execution do not supply physical services or new Lean kernel
certification. No generic quotient, graph classification, coding theorem,
unrestricted Boolean task framework or worldwide originality claim is
part of this comparison.

[ABT-ENTRY]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md
[CAR-ENTRY]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[NPS-ENTRY]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PHASE_SYNTHESIS.md
[NRF-ENTRY]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RESOURCE_FRONTIER.md
[NAR-ENTRY]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md

## 追加锚（本行以下为增补区）

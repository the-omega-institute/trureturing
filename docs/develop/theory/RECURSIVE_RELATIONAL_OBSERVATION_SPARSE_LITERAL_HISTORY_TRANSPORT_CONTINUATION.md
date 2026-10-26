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

## 10. Unknown shape: matching complete parity memory

**Definition 10.1 (one all-shape task and two comparison classes).**
For public integers $h\ge1$ and $T\ge0$, let $\mathcal G_h$ contain
all finite full ordered binary trees with exactly $h$ leaves, each
independently labelled $\alpha=0$ or $\beta=1$. The allowed histories
are $(u,t)\in\mathcal G_h\times\{0,\ldots,T\}$, with current tree
$\rho^t u$ and target $\pi(u)$, the XOR of the **original** labels.
The substitution is $\rho\alpha=\beta$,
$\rho\beta=\langle\beta,\alpha\rangle$, preserving pairing.
Only $h,T$ are public. Shape, leaf addresses, entry lag, labels and
original identity are not supplied; there are no spare known leaves,
old records, reset, inverse, copy, whole-tree observation or timing port.
Promise establishment and authentication remain separate services.

Use the fully materialized literal Read, four raw replies,
same-source genuine Update with constant acknowledgement, and fixed-bit
Halt of Definitions 1.1–1.3. One fixed-length no-$11$ word is the
entire mutable observer, including instruction and address selection,
progress, phase, retained reply, parity and halts. Every primitive
reply immediately selects a hold or one bit change and is discarded.
One installed query word selects one fixed root-relative literal;
one halt word selects one fixed output. Initialization is common to
all allowed sources and entries. All installed words count, including
unreachable ones. Root Reads used for routing are actual paid Reads.

Let $\ell_{\rm act}^{\min}(h,T)$ minimize the complete width over
correct terminating installations allowed to use genuine Updates;
let $\ell_{\rm stat}^{\min}(h,T)$ minimize it over those executing
zero actual Updates on every promised run. Unreachable Update rows
do not make a static run active. The lower bounds also allow arbitrary
deterministic finite internal work without source input, provided all
mutable control remains in the counted word and each query still has
its fixed literal. Every internal step in such a variant is an
additional operation, not a native Read or Update. Section 11's
attaining observers use no internal instructions or internal writes.

**Theorem 10.2 (comb-cone installed-union bounds).** In the positive
regimes $T=0$ or even $h$, every correct complete installation has
at least $2^{h-1}$ distinct query words and two distinct halt words.
Every correct static installation has at least
$2^{h-1}\lceil(T+1)/3\rceil$ query words and two halt words. Thus,
with $F_0=0,F_1=1$,

$$
\begin{aligned}
F_{\ell_{\rm act}^{\min}+2}&\ge 2^{h-1}+2,\\
F_{\ell_{\rm stat}^{\min}+2}
 &\ge 2^{h-1}\left\lceil\frac{T+1}{3}\right\rceil+2.
\end{aligned}
\tag{SLHC.10.1}
$$

Every successful run also uses at least $h$ actual Reads. The
exponential bounds count the installed union across different allowed
shapes; they do not assert exponentially many Reads on one run.

Proof. Use the shape support of FIB II Lemma 38.40 and the
position–address construction inside Joint Moment Fibers Theorems
40.2–40.3: for every $p\in\{L,R\}^{h-1}$, there is a full ordered
comb $S_p$ whose tip is $p$, with one sibling leaf for each strict
prefix of $p$. It has exactly $h$ leaves. At $h=1$ use the root
leaf and $p=\varepsilon$. Only this shape witness is consumed; the
third-image target and block suffixes of Joint Moment Fibers §40
are not imposed on the present sources.

On $S_p$ choose all labels $\alpha$, and compare the permitted
filling that flips only the tip to $\beta$. Their parities differ.
The original-cone transport of SLH §§31–32, applied to this fixed
shape with every label independently allowed, says that after any
common number $a$ of genuine Updates the two trees can differ only
inside $p\{L,R\}^*$. Every strict ancestor is still a branch and
every other original cone is unchanged. These are proof-wise
restrictions to allowed subfamilies, not supplied shape information
or a request to acquire SLH's old certificate.

Fix the terminating run on the first filling at any allowed entry.
Until a separating Read, deterministic instruction selection,
internal work, raw replies and update acknowledgements agree on the
two sources; the actual counts of Updates agree as well. If no Read
separates them, induction through this finite run yields the same
first fixed-output Halt on opposite parities, a contradiction.
A separating literal must therefore extend $p$. Distinct words $p$
of the same length $h-1$ have disjoint extension cones. One fixed
installed query word cannot witness two of them, even if revisited
at different epochs. This gives $2^{h-1}$ query words across the
whole family. Applying the same first-separation argument to each
of the $h$ independent leaves of any single input gives $h$
different Read occurrences on that run. The two target values both
occur, requiring two halt words disjoint from query words. Arbitrary
finite internal work supplies no separating observation.

For the static strengthening, for each $p$ use those two fillings
at every entry $t=0,\ldots,T$. Their two tip subtrees are
$T_t,T_{t+1}$, where $T_n=\rho^n\alpha$, and remain stationary.
At least one installed literal $ps$ must distinguish this pair for
each $t$. Reuse CAR Theorem 13.4's guarded atomic readout, as applied
in §9.6: put $w(s)=\#_L(s)+2\#_R(s)$. A nonempty suffix ending
in $R$ distinguishes adjacent atomic indices only at
$t=w(s)-1,w(s),w(s)+1$; one ending in $L$ only at
$t=w(s),w(s)+1$; the empty suffix only at $t=0,1$.
Only nonnegative entries in the promised interval count. These are
raw readouts, with absence below a leaf; no unguarded subtraction
at an unreached address is used. Thus one fixed suffix covers at
most three of the $T+1$ comparisons. Each $p$ needs at least
$\lceil(T+1)/3\rceil$ query words, and the equal-depth cones remain
disjoint. This proves the product, including unused installed rows
and adaptive query order. Finally use the already supplied count
$|L_\ell|=F_{\ell+2}$ from §5.2 to obtain (SLHC.10.1).
$\square$

**Theorem 10.3 (matching widths on the original all-shape task).**
Under Definition 10.1's conditional native services, for all $h\ge1$
and finite $T$ with $T=0$ or even $h$,

$$
\begin{aligned}
\ell_{\rm act}^{\min}(h,T)&=\Theta(h),\\
\ell_{\rm stat}^{\min}(h,T)&=\Theta\bigl(h+\log_2(T+1)\bigr).
\end{aligned}
\tag{SLHC.10.2}
$$

The constants are independent of $h,T$; for example each lower
inequality holds with constant $1/4$ and each upper inequality with
constant $64$. The attaining complete native observers are exactly
Constructions 11.4–11.6, with all of Theorem 11.2's actual Read,
Update, response-change and literal-length bounds and §11.6's
installation and source bills. Their native-call bounds are
$O(hT+h^3)$ active and
$O(h(T+1)(h+\log_2(T+1)))$ static. These are polynomial in $h+T$,
not in the encoded length $\log(T+1)$. At $T=0$ both can use the
same direct traversal and zero Updates, for every $h$.

Proof. For the upper bounds apply Theorem 11.2 on precisely
Definition 10.1's source family and parity target. Lemma 11.3
licenses every delayed decoder invocation by induction inside an
actual substitution image. The active root-clock alignment leaves
at most $2h$ licensed candidates without retaining a poll count or
absolute epoch. Construction 11.5 retains the path and parity;
Construction 11.6 implements every response, reset and address
change by its complete two-bank table and paid root Reads.
Its first Halt is the original parity, and every typed row is
installed and immediately one-bit legal. No other realization or
contracted intermediate transition is assumed here.

Using the notation of (SLHC.11.1), the widths are $4k(0)+15$ at
$T=0$, $4k(\lambda(2h))+15$ for active positive $T$, and
$4k(\lambda(T+1))+15$ for static positive $T$.
For $h\ge2$, $\lambda(h)\le h-1$, $\lambda(h+1)\le h$ and
$\lambda(2h)\le h$; also $\lambda(T+1)\le\log_2(T+1)+1$.
These inequalities give the asserted upper constant. The remaining
$h=1,T=0$ case has $k(0)=6$ and width $39$.

For necessity, $F_{\ell+2}\le2^\ell$ and (SLHC.10.1) give
$\ell\ge h-1$ in the active case and
$\ell\ge x-1-\log_2 3$ in the static case, where
$x=h+\log_2(T+1)$. At least three installed words always imply
$\ell\ge2$. If $x\ge4$ then $x-1-\log_2 3\ge x/4$;
if $x<4$ use $\ell\ge2$. The same two-case estimate gives
$\ell\ge h/4$ actively. This proves uniform constants and both
matching orders. $\square$

**Proposition 10.4 (history and installation boundaries).** For odd
$h$ and $T\ge1$ neither comparison class has a solution. For every
fixed $h\ge1$, no one finite complete fixed-literal installation
solves all unbounded entries, even with adaptive genuine Updates
and counted finite internal work.

Proof. The first assertion is the exact ABT Theorem 9.2 fiber
$\{(A_S,1),(B_S,0)\}$ on any $h$-leaf shape $S$. These entries
have the same current tree and, for odd $h$, opposite parity;
ABT's future-experiment indistinguishability applies to all allowed
operations and common initialization.

For the second assertion put
$\Omega=\max(\{0\}\cup\{w(p):p\text{ is an installed Read literal}\})$,
including all routing literals. The permanent saturation supplier
CAR Theorem 11.2 / Native Resource Frontier Theorem 2.1, used in
§9.7, gives branch at every installed literal for every source at
entry $t\ge\Omega+2$ and after every further Update. In terms of
maximum ordinary length $D$, $2D+2$ is also sufficient since
$w(p)\le2|p|$. Choose two same-shape originals differing at one
leaf. All future raw replies, acknowledgements and internal work
agree, whereas their target bits differ. A shared first Halt is
wrong for one source; absence of a Halt violates termination.
Thus the positive quantifier is $\forall T<\infty\ \exists C_{h,T}$
in its stated regimes, not $\exists C_h\ \forall t\ge0$.
$\square$

**Proposition 10.5 (the cost of withholding the supplied shape).**
For an exact-$h$ supplied shape, §9.2's same parity target has
minimum active width $\Theta(\log(h+1))$ and static width
$\Theta(\log(h+1)+\log(T+1))$ in the same positive regimes.
Withholding the shape and requiring a common installation for all
shapes gives (SLHC.10.2). These are conditional mutable-width
comparisons, not total-storage or acquisition optima.

Proof. Section 9 uses every independent original label on exactly
$h$ leaves, with no padding or reference label. Its formulas apply
to any fixed full shape; supplying its literal addresses is precisely
the additional initial information absent here. Theorem 10.2 takes
the union over all possible comb tips, which one shape need not
support. The lower and upper bounds of the two sections therefore
compare the same target under the two stated source-information
contracts. Native Discovery and Retained Context §§1–4, 7.1
separately distinguish unknown-shape full-tree discovery from its
known-shape benchmark; their full-tree factor-two acquisition theorem
is not a parity or complete-width theorem and is not transferred.

Sections 2 and 8 retain their distinct full-vector and parity tasks.
For positive unknown entry even-$h$ parity is constant on ABT's
exact history fibers, whereas the full original label vector and
actual entry can differ on the uniform doubletons. No parity output
recovers those missing distinctions, old records or inverse action.
The current-tree fiber does determine the original shape by ABT;
this identifiability does not supply its addresses to the observer
at initialization. Shape acquisition, parity acquisition, certification
and physical realization remain different services. $\square$

The new quantitative composition is Theorems 10.2–10.3 together with
Section 11's licensed trials and paid native realization. Shape and
leaf-cone support remain owned by FIB II §§38.40–38.42, Joint Moment
Fibers §§40.1–40.3 and SLH §§31–32; SLH §55's delayed leaf certificate
is a known-template supplier, not a free unknown-shape selector.
No classifier, support theorem or general compiler is newly asserted.
The mature encoding and control suppliers are attributed at their
points of use in Section 11. These are repo-derived ordinary
conditional statements, not additional kernel-verified applications
or a worldwide originality claim.

## 11. Unknown-shape parity with polynomial paid acquisition

### 11.1. Source, target and quantitative assertion

**Definition 11.1 (unknown-shape original parity).** Fix public integers
$h\ge1$ and $T\ge0$. The original $u$ ranges over **all** finite ordered
full trees with exactly $h$ leaves, each independently labelled
$\alpha=0$ or $\beta=1$. Its ordered shape is unknown. Entry is
$y=\rho^t u$ for unknown $0\le t\le T$, and the target is
$\pi(u)$, the XOR of the original leaf labels. Use Definitions 1.1 and
1.3's same-source Read, Update and fixed-bit Halt, with a common
source-independent initial word. Every Read submits an entire finite
literal from the original root. The four replies remain
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$, and Update returns only
$\star$. There is no subtree port, old tree, inverse, reset, copy,
reference leaf, shape, supplied epoch, source identity or source-dependent
advice. The source promise and its authentication are separate services.

The whole fixed-length no-$11$ word includes instruction selection,
path, progress, candidate offset, phase, retained reply, counters,
parity and halts. Each primitive response immediately changes at most
one bit and is discarded. All routing Reads below are actual paid root
Reads. The immutable whole-word instruction and typed-response table,
initialization, selection, literal delivery, primitive execution,
response writing and output have Definition 1.3's separately supplied
and charged contracts.

Write $\lambda(n)=\lceil\log_2 n\rceil$ for $n\ge1$, and set

$$
d=\lambda(h),\qquad c=\lambda(h+1),\qquad
k(e)=h+3+d+2c+e,\qquad
\ell(e)=4k(e)+15,\qquad R(e)=2k(e)+7.
\tag{SLHC.11.1}
$$

A zero-width field represents its sole value zero. Define the following
bounds; $H$ counts the intermediate table's source instructions, not
the final observer's actual instruction count.

| Regime | Candidate bits $e$ | $H$ | Maximum literal length $P$ | Submitted address-sum bound $A_*$ |
| --- | --- | --- | --- | --- |
| Every $h$, $T=0$ | $0$ | $2h-1$ | $h-1$ | $(2h-1)(h-1)$ |
| Even $h$, static $T\ge1$ | $\lambda(T+1)$ | $(T+1)(4h-2)$ | $h-1+\lceil T/2\rceil$ | $(T+1)(4h-2)P$ |
| Even $h$, active $T\ge1$ | $\lambda(2h)$ | $2B+1+2h(4h-2)$ | $h-1+B/2$ | $(B+1)B/2+2h(4h-2)P$ |

In the last row the source-independent installed integer is

$$
B=2\left\lceil\frac{T+2h}{2}\right\rceil.
\tag{SLHC.11.2}
$$

**Theorem 11.2 (polynomial native acquisition).** In the conditional
native services of Definition 11.1, each row of the table above has a
complete observer of width $\ell(e)$, with

$$
Q+U\le R(e)H,\qquad
\text{response bit changes}=Q+U,\qquad
\sum_{\text{actual Reads}}|p|\le A_*,
\qquad \max_{\text{actual Reads}}|p|\le P.
\tag{SLHC.11.3}
$$

The $T=0$ and static rows have $U=0$. In the active row, writing
$\kappa(\alpha)=0$, $\kappa(\beta)=1$ and
$\kappa(\langle v,w\rangle)=2+\kappa(w)$, the exact update count is

$$
U=B-t-\kappa(u),\qquad 1\le U\le B.
\tag{SLHC.11.4}
$$

All counts end at the first fixed-bit Halt and include failed trials,
polling, decoder second Reads, word resets and every bank/phase
transition. There are no internal instructions or internal writes.
Thus active complete width is $O(h)$ with
$Q+U=O(hT+h^3)$; static complete width is
$O(h+\log_2(T+1))$ with
$Q=O(h(T+1)(h+\log_2(T+1)))$.
Both call bounds are polynomial in $h+T$.

The explicit installation below contains exactly
$2^{2k(e)+8}$ words, including unreachable words and all halts.
Its immutable table, literals and source-growth costs are stated in
§11.6. No polynomial immutable-storage or physical-time bound is
asserted. For odd $h$ and $T\ge1$ the task is impossible; no single
finite fixed-literal installation solves its unbounded-entry version
even when $h$ is even. These boundaries use the suppliers in §11.7.

### 11.2. Certified increasing trials on a stationary current tree

**Lemma 11.3 (a bounded trial inside a genuine image).** Suppose, as
proof data, that the current tree is $y=\rho^\tau u$, where $u$ has
exactly $h$ leaves. If $0\le N\le\tau$, set
$v_N=\rho^{\tau-N}u$. A left-first preorder traversal of $v_N$, cut off
on encountering its $h$th branch, either rejects at that branch or
finishes the complete tree with exactly $h$ leaves. It visits at most
$2h-1$ nodes and queries only addresses of depth at most $h-1$.
Each virtual node reply can be obtained with at most two actual
stationary Reads on $y$ using SLH §2. The whole trial therefore uses at
most $4h-2$ actual source Reads before word-routing expansion.
At $N=\tau$ it finishes. On finishing, the XOR of its leaf replies
equals $\pi(u)$ whenever $h$ is even.

Proof. The equality $y=\rho^N v_N$ is an actual image witness, not a
guessed certificate. ABT §9's leaf-growth facts give
$L(v_N)\ge L(u)=h$. Reuse the source-total producer's preorder of actual
nodes: read a reached branch before descending, visit its left subtree
before its right subtree, and never descend from a leaf. This is the
Read order supplied by
[NativeFullSourceProducer.native_source_producer][SLHC11-PRODUCER].
Its full producer also builds subtrees and performs two local steps
per branch. Those extra outputs and operations are not presumed to fit
here. The path-only realization below proves this consumer's reduced
control and pays for every one of its transitions.

After $b$ branch and $l$ leaf visits a proper preorder prefix has
$1+b-l>0$ pending slots. Before the $h$th branch, $b\le h-1$; immediately
before that branch, $l\le h-1$. Hence a rejected trial has at most
$h+(h-1)$ visits. If the traversal finishes first, fullness gives
$l=b+1\le h$; since the complete $v_N$ has at least $h$ leaves, necessarily
$l=h$ and $b=h-1$, with $2h-1$ visits. A queried node has one distinct
previous branch for each strict ancestor, so its depth is at most
$h-1$. A cutoff branch is not expanded.

For precision, the actual decoder used here is the following
specialization of SLH Definitions 2.1–2.2. For $N=0$, read $p$ directly.
For $N>0$ and $p\ne\varepsilon$, first read

$$
g=p^-R^{\lfloor N/2\rfloor+1}.
\tag{SLHC.11.5}
$$

The guard accepts a non-absent reply for even $N$, and a
$\beta$ or branch reply for odd $N$. Then read
$pR^{\lceil N/2\rceil}$. At the root omit the guard. At even $N$ the
second reply is the virtual reply; at odd $N$ use

| Raw second reply | $\mathsf{absent}$ | $\alpha$ | $\beta$ | $\mathsf{branch}$ |
| --- | --- | --- | --- | --- |
| Virtual reply | $\alpha$ | $\beta$ | $\mathsf{branch}$ | $\mathsf{branch}$ |

A failed guard or an even-offset absent value enters an error control,
which never halts. On the actual traversal both are excluded by
$y=\rho^N v_N$ and reachedness. Even when the two displayed coordinates
coincide, this implementation performs both Reads and charges both.
Each literal has length at most $|p|+\lceil N/2\rceil$.
An absent *raw* odd-offset value is a valid virtual $\alpha$ and is
not an error.

At $N=\tau$, $v_N=u$, so there is no $h$th branch and the traversal
finishes. If an earlier trial finishes, the two histories
$(u,\tau)$ and $(v_N,N)$ have the same current tree and the same
original leaf count. ABT Theorem 9.2, on its full unknown-shape domain,
says that they are identical or the same-shape uniform
$\alpha/\beta$ pair at adjacent epochs. That pair has equal parity for
even $h$. This invokes the supplied fiber theorem; it does not repeat
its classification or certify that $N$ was the original epoch.
$\square$

Start at any certified $N_0\le\tau$ and increase $N$ by one after a
cutoff. The first trial is licensed. If a licensed trial rejects, it
cannot have $N=\tau$, because that trial would finish; hence
$N+1\le\tau$ licenses the next trial. Induction proves that every decoder
invocation in every actual trial is inside its image. Success occurs
by $N=\tau$, and no actual trial crosses it. This argument establishes
image membership before decoding, rather than interpreting finitely
consistent replies as membership.

For the static observer take $N_0=0$ and try $N=0,1,\ldots$ up to $T$.
Since $\tau=t\le T$, there are at most $T+1$ trials. For $T=0$ there is
exactly one direct traversal of $u$ and no decoder guard, for every
$h$, including odd $h=1$. Its parity is the original parity without
using a historical-fiber ambiguity.

### 11.3. Active alignment without storing an absolute epoch

**Construction 11.4 (paid alignment and short offset interval).**
Assume $T\ge1$ and even $h$. Repeatedly read the single installed
literal $R^{B/2}$. On absent, execute one genuine Update and repeat.
On $\alpha$, stop updating and start the increasing trials at

$$
N_0=B-2h+1,\qquad N=N_0+j,\qquad 0\le j\le2h-1.
\tag{SLHC.11.6}
$$

The other polling replies enter the nonhalting error control.
The actual controller retains neither the number of polls nor the
number of Updates.

Proof of alignment. The rightmost original leaf has depth at most
$h-1$, whence $0\le\kappa(u)\le2h-1$. SLH §2's right-clock and raw-ray
laws give

$$
\kappa(\rho^{t+a}u)=t+a+\kappa(u),\qquad
r_w(R^{B/2})=
\begin{cases}
\mathsf{absent},&\kappa(w)<B,\\
\alpha,&\kappa(w)=B,\\
\beta,&\kappa(w)=B+1,\\
\mathsf{branch},&\kappa(w)\ge B+2.
\end{cases}
\tag{SLHC.11.7}
$$

At entry $t+\kappa(u)\le T+2h-1<B$. Each Update increases this clock
by exactly one. Therefore the first non-absent poll is precisely
$\alpha$, after $U=B-t-\kappa(u)$ Updates and $U+1$ polling Reads.
All routing Reads leave the source unchanged, so they do not affect
this argument. The stationary tree at the end is $\rho^\tau u$ with

$$
\tau=t+U=B-\kappa(u)\in[B-2h+1,B].
\tag{SLHC.11.8}
$$

Consequently $N_0\le\tau$ and at most $2h$ increasing trials suffice
by Lemma 11.3. The proof knows $\tau$; the observer only stores $j$.
The large integer $N_0$ and each expanded literal are fixed installed
constants. The observed clock threshold certifies this interval, not
the historical value $t$ or an original reference label. $\square$

### 11.4. The finite parity table before one-bit realization

**Construction 11.5 (all counted fields and source rows).** Encode an
intermediate control $z$ using the following $k(e)$ ordinary bits in
the displayed order. Binary integers use a fixed common significance
order; path bits are $L=0,R=1$, followed by zero padding.

| Field | Bits | Meaning |
| --- | --- | --- |
| $p$ | $h-1$ | Current virtual address, padded after its length |
| $s$ | $d$ | Path length $0\le s<h$ |
| $b,l$ | $2c$ | Branches and leaves already visited in this trial |
| $j$ | $e$ | Candidate index |
| $a$ | $1$ | XOR of leaves already visited |
| $\mu$ | $3$ | VALUE, GUARD, POLL, UPDATE, HALT0, HALT1, ERROR |

Use mode codes $0,\ldots,6$ in that order. HALT0, HALT1 and ERROR have
all other fields zero. POLL and UPDATE also have all other fields zero
and are available only in the active $T\ge1$ case. In the static case
$N=j$ and $j\le T$; in the active case use (SLHC.11.6) and
$j\le2h-1$. GUARD requires $N>0$ and $p\ne\varepsilon$.
Normal fields obey $b<h$, $l\le h$ and the displayed bounds; nonzero
path padding, code 7 or a violated condition is invalid.

Here is the entire intermediate instruction/response rule, denoted
by instruction $I(z)$ and successor $\delta(z,r)$. This table is an
installation specification, not permission to execute wide writes.

- POLL uses Construction 11.4: absent goes to UPDATE, $\alpha$ starts
  a fresh root VALUE trial with $j=0$, and the other replies go to ERROR.
  UPDATE executes Update and its $\star$ goes to POLL.
- GUARD reads (SLHC.11.5); an accepted guard changes only the mode to
  VALUE. A rejected guard goes to ERROR.
- VALUE reads $p$ at $N=0$, and $pR^{\lceil N/2\rceil}$ otherwise.
  Decode by Lemma 11.3. An invalid virtual absent goes to ERROR.
- On a decoded branch, if $b+1=h$, reject the trial: increment $j$,
  reset $p,s,b,l,a$ to zero and use root VALUE. If the candidate range
  would be exceeded, go to ERROR. Otherwise, for $b+1<h$, increment
  $b$, replace $p$ by $pL$, increment $s$, and use GUARD when $N>0$
  or VALUE when $N=0$. A path overflow goes to ERROR.
- On a decoded leaf bit $x$, if $l=h$ go to ERROR; otherwise put
  $l'=l+1$, $a'=a\oplus x$. If $p$ contains an $L$, take its rightmost
  $L$, replace it by $R$, and delete everything after it. Set $s$ to
  the new length and zero the discarded path padding. This is the next
  preorder node; preserve $b,j$, store $l',a'$, and use GUARD
  when $N>0$ or VALUE when $N=0$. If $p$ has no $L$, traversal is
  complete: go to the canonical HALT$a'$ exactly when
  $l'=h$ and $b=h-1$, and otherwise go to ERROR.
- HALT0 and HALT1 have the respective fixed-bit Halt instructions.
  ERROR and every invalid code read $\varepsilon$ and send every
  raw reply to the canonical ERROR.

These rules specify every typed reply, including replies outside
actual supports. Every nonhalting intermediate instruction is an
actual source primitive. The next-address rule is precisely preorder:
a branch opens its left child; completion of a subtree finds the
deepest ancestor whose right child is pending. Its pending ancestors
are encoded by the $L$ positions of $p$, so no stack of subtrees is
retained. This is a consumer of the published source-total traversal,
not a claim that its full acquired-tree workspace has width $O(h)$.

The common initial $z$ is root VALUE with zero fields for static or
$T=0$, and canonical POLL for active $T\ge1$. Every actual transition
in the preceding proof is one of these rows. The branch cutoff bounds
every actual path by $h-1$; the counter bounds and the exact completion
test follow from the pending-slot invariant. Trial resets and the
possibly long path truncation remain to be implemented and charged.

### 11.5. One word, immediate replies, and paid bitwise routing

**Construction 11.6 (the complete installed word).** For the particular
table of Construction 11.5 let $k=k(e)$. The logical word has two
$k$-bit banks $A,B'$, five one-hot reply flags
$f_\alpha,f_\beta,f_{\mathsf{branch}},f_{\mathsf{absent}},f_\star$,
and three phase bits. Its logical length is $m=2k+8$.
The source-independent initial word has phase 000, bank $A=z_{\rm init}$,
bank $B'=0^k$ and zero flags. No bank, phase or flag exists outside this
word. The actual physical word is

$$
J(x_1\cdots x_m)=x_1\,0\,x_2\,0\,\cdots\,0\,x_m,
\qquad W=J(\{0,1\}^m),\qquad \ell=2m-1=4k+15.
\tag{SLHC.11.9}
$$

All $2^m$ such words are installed. The inserted zeros never change.
The following rows give their fixed instruction and typed responses.
A deterministic row always executes Read$(\varepsilon)$, ignores
which of its four raw replies arrived, and makes the single stated
bit change. It is not an internal instruction. "Least" refers to the
fixed bit order of the bank.

| Phase and word condition | Instruction | Immediate response action |
| --- | --- | --- |
| 000, flags zero, $B'=0$ | $I(A)$ | For Read reply $r$, set $f_r$; for Update acknowledgement, set $f_\star$; a Halt outputs its fixed bit |
| 000, exactly one flag $f_r$, $r$ typed for $I(A)$ | Root Read | If $B'\ne\delta(A,r)$, flip the least differing bit of $B'$; otherwise change phase to 001 |
| 001, exactly one flag | Root Read | If $A\ne0$, clear its least one; otherwise change phase to 011 |
| 011, $A=0$, exactly one flag | Root Read | Clear that flag |
| 011, $A=0$, flags zero | Root Read | Change phase to 010 |
| 010, flags zero, $A=0$ | $I(B')$ | For Read reply $r$, set $f_r$; for Update acknowledgement, set $f_\star$; a Halt outputs its fixed bit |
| 010, exactly one flag $f_r$, $r$ typed for $I(B')$ | Root Read | If $A\ne\delta(B',r)$, flip the least differing bit of $A$; otherwise change phase to 110 |
| 110, exactly one flag | Root Read | If $B'\ne0$, clear its least one; otherwise change phase to 111 |
| 111, $B'=0$, exactly one flag | Root Read | Clear that flag |
| 111, $B'=0$, flags zero | Root Read | Change phase to 101 |
| 101, $B'=0$, flags zero | Root Read | Change phase to 100 |
| 100, $B'=0$, flags zero | Root Read | Change phase to 000 |
| Any remaining installed word | Root Read | Hold the word for each of the four replies |

For a Halt, no reply is typed; its flagged case therefore does not
match a filling row. The phase cycle is

$$
000,\ 001,\ 011,\ 010,\ 110,\ 111,\ 101,\ 100,\ 000,
\tag{SLHC.11.10}
$$

whose adjacent terms differ in one bit, including the final edge.
The table treats the letters of $I(z)$ and all values $\delta(z,r)$
as fixed finite data expanded at installation. In particular,
$\delta$ and least-bit selection are not an uncharged runtime
algorithm or a second mutable controller: each entire word has one
already installed literal instruction and each typed response has one
already installed hold/flip choice.

To verify a transfer, begin in phase 000 with $(A,B')=(z,0)$ and no
flag. One actual $I(z)$ response sets exactly one counted flag; the
raw response is then discarded. The $A$ bank and flag retain precisely
what selects $\delta(z,r)$ until $B'$ equals that target. Each root
Read reduces the number of differing destination bits by one. After
phase 001 clears $A$, phase 011 clears the flag and enters 010.
The ready state is now $(0,\delta(z,r))$. The reverse transfer follows
the last half of the table and returns to phase 000 with
$(\delta(z,r),0)$. All source changes occur only at the selected
intermediate Update; every extra instruction is a source-preserving
root Read. No intermediate phase halts.

If $|z|_1$ is a bank's Hamming weight, the exact primitive counts for
these two transfers, including the original source instruction, are

$$
c_{A\to B'}(z,r)=|z|_1+|\delta(z,r)|_1+5,\qquad
c_{B'\to A}(z,r)=|z|_1+|\delta(z,r)|_1+7.
\tag{SLHC.11.11}
$$

The constants count the reply-flag setting, phase changes and flag
clearing. Both are at most $2k+7$. Resetting counters or addresses,
setting the output, filling a zero target, and erasing a bank are all
covered by this formula. Every actual nonhalting row changes one
logical bit, hence one physical bit. Every other typed row either
holds or changes one bit as well. Zero interleaving proves no-$11$
for every installed word and every successor, without an assumption
about which rows are reachable.

The ready-state correspondence, proved transfer by transfer, matches
Construction 11.5's controls and the actual current source. It yields
exactly its first Halt and fixed output. Its raw chronology additionally
contains all the charged root Reads; it is not claimed to equal the
intermediate chronology. FIB §47's unchanged-instruction finite-prefix
refinement alone would not give this width or this chronology.

For FIB §§26–27, let $C_w$ contain exactly the pairs
$(\pi(u),y)$ actually reachable at word $w$ from the promised entries.
Every actual primitive is legal, the typed rows give same-source
successor closure, and the two halt instructions have the proved
original target on their supports. Lemma 11.3 and Construction 11.4
prove finite intermediate termination, and (SLHC.11.11) proves finite
routing between ready states. Thus the deterministic future from each
reachable $(y,w)$ has a finite number of primitive calls left. Take
that number as the natural rank on $C_w$; it decreases by one at every
call and is zero at Halt. If two histories yield the same $(y,w)$,
their futures coincide, so the rank is well defined. Supports and rank
are proof data, never selector inputs. This supplies the precise
complete-control obligations of FIB §27.2 and the explicit adjacency
required by §45, rather than inferring a one-write implementation from
a count of names.

### 11.6. Full native, installation and source bills

We now complete the resource assertions of Theorem 11.2. The direct
$T=0$ traversal has exactly $2h-1$ intermediate Reads. Each stationary
trial has at most $4h-2$, including every guard and second Read.
The static case has at most $T+1$ trials. The active case has at most
$2h$ trials, $U+1$ polling Reads and $U$ Updates, hence at most

$$
2U+1+2h(4h-2)\le2B+1+2h(4h-2)
\tag{SLHC.11.12}
$$

intermediate source instructions. Applying (SLHC.11.11) to **every**
such instruction gives (SLHC.11.3); specifically
$Q\le RH-U$. There is no free preparation between instructions.
The only extra Reads have empty addresses. Trial literals obey
$|p|+\lceil N/2\rceil$, with $|p|\le h-1$; active polling literals
have length $B/2$. Summing their lengths proves exactly the advertised
uniform $A_*,P$ bounds, without charging a shortened suffix instead
of its root-based literal.

Here is one fully explicit, deliberately redundant immutable
representation. Let

$$
W_* = 2^{2k+8},\qquad
g=\lambda(P+1),\qquad q=\lambda(\ell+1).
\tag{SLHC.11.13}
$$

There are $W_*$ instruction rows and, if their numbers of Read and
Update rows are $n_R,n_U$, exactly $4n_R+n_U\le4W_*$ typed-response
entries. There are exactly four halt rows, two for each fixed output
across the two ready phases. There are exactly two Update rows in the
active $T\ge1$ installation and zero in the static or $T=0$ installation;
all other rows are Reads. Thus $n_R=W_*-4-n_U$. Halt rows have no
response entry. Store each row with its
$\ell$-bit word key, a two-bit opcode for Read/Update/Halt0/Halt1, a
$g$-bit literal length, $P$ bits holding the entire literal with padding,
and four $q$-bit response slots. A response slot is 0 for hold or a
physical bit index in $\{1,\ldots,\ell\}$ to flip. Unused opcode fields
and response slots have fixed zero padding. This gives the explicit
storage bound

$$
S_{\rm tab}
 =W_*(\ell+2+g+P+4q)\ \text{bits}.
\tag{SLHC.11.14}
$$

The common initialization word adds $\ell$ immutable bits. There are
at most $W_*$ installed literal copies, with actual unpadded total
length at most $W_*P$. Duplication is allowed and fully charged.
The full table can be produced by enumerating all $m$-bit words and
the finite cases in Construction 11.6, expanding each literal.
Table generation and delivery are finite installation services with
their own costs; (SLHC.11.14) bounds stored bits, not the physical
time for generating or selecting them. Source-specific information
is not used to choose a table, initial word or installed literal.

If the run has $n=Q+U$ primitive calls, there are exactly $n+1$
instruction selections including the final Halt, $Q$ literal
deliveries (including empty routing literals), $n$ immediate response
selections/writes, and one output. Initialization occurs once.
Following FIB §45.2, an appropriate cost vector has the form

$$
\begin{aligned}
C={}&C_{\rm promise/auth}+C_{\rm source/entry}
 +C_{\rm compile/install}+C_{\rm init}\\
 &+\sum_{i=0}^{n-1}
   \bigl(C_{\rm select}(w_i)+C_{\rm deliver}(I(w_i))
       +C_{\rm primitive}(I(w_i),y_i)
       +C_{\rm response}(w_i,r_i)\bigr)\\
 &+C_{\rm select}(w_n)+C_{\rm output}(\pi(u)).
\end{aligned}
\tag{SLHC.11.15}
$$

Delivery for Update has no address payload. Immutable storage and
complete mutable width remain distinct coordinates. Initialization
can write the whole initial word under its separately supplied
service; it is not one of the response writes in (SLHC.11.3).
A physical table lookup or literal-delivery implementation requiring a
persistent external cursor or latch does not meet Definition 11.1.
The stated conditional service must implement those selections with
this word as its entire mutable observer.

For source growth, let $b_\beta$ be the original number of $\beta$
leaves, and $F_0=0,F_1=1$. The original-cone decomposition of SLH §32
and $|T_n|_{\rm leaves}=F_{n+1}$ give the exact current node count at
absolute epoch $s$:

$$
V(s)=2\bigl((h-b_\beta)F_{s+1}
                    +b_\beta F_{s+2}\bigr)-1.
\tag{SLHC.11.16}
$$

The static source stays at $s=t\le T$, with peak at most
$2hF_{T+2}-1$ nodes. The active source passes through epochs
$t,t+1,\ldots,\tau$ with $\tau=B-\kappa(u)\le B$ and has peak
$V(\tau)\le2hF_{B+2}-1$. The direct $T=0$ source has $2h-1$ nodes.
For an implementation that traverses the whole materialized source
once per Update, its node-volume sum is bounded, for example, by
$(B+1)(2hF_{B+2}-1)$ over the active versions; costs of allocating or
rewriting nodes belong to that implementation, not to the one-bit
observer response count. The mathematical model supplies no timing
observation of these costs. Polynomial **native calls** can coexist
with exponential source size and an exponentially large installed
table. These bounds, the preceding correctness proof and the boundary
argument below prove Theorem 11.2. $\square$

### 11.7. Obstructions, comparisons and supplier correspondence

ABT §§9.2–9.4 already supply the odd-$h$ obstruction: for any one
$h$-leaf shape, the all-$\beta$ original at lag zero and all-$\alpha$
original at lag one give the identical entry but opposite original
parities when $h$ is odd. Every future adaptive native experiment from
a common initial word has the same replies and same-source successors.
This excludes $T\ge1$, including $h=1$, while the direct $T=0$ table
covers both one-leaf labels. The restriction to even $h$ at positive
$T$ is therefore semantic, not a limit of the alignment construction.

The accepted earlier representative in Lemma 11.3 need not have an
epoch in the originally promised $[0,T]$ after active Updates. This
does not assert a new allowed initial history: ABT's unbounded
same-leaf-count fiber theorem is applied to the two mathematical
histories at the **current** tree. Its even-parity consequence is
enough for the actual original target. No template is guessed, no
finite compatibility check is used as image authentication, and exact
leaf count is proved by complete traversal or rejected at the
$h$th branch.

For a concrete failure outside that invariant, let
$u=\langle\alpha,\beta\rangle$ at lag zero and incorrectly invoke the
decoder with $N=1$. Its root value at $R$ is $\beta$, decoded as branch;
the two child guards also accept the reply at $R$. Values at $LR$ and
$RR$ are absent, both decoded as $\alpha$. The resulting virtual
two-leaf tree has parity zero, whereas $\pi(u)=1$.
This is an ordinary wrong-image counterexample; the certified
increasing runs never make this trial.

The positive quantifier is

$$
\forall h\ \forall T<\infty\
 \bigl(T=0\ \text{or }h\text{ even}\bigr)
 \ \Longrightarrow\ \exists C_{h,T}\ \forall(u,t)
 \text{ satisfying Definition 11.1}.
\tag{SLHC.11.17}
$$

It is not $\exists C_h\ \forall t\ge0$. Restricting unknown shapes
to any one fixed $h$-leaf shape embeds §9.7's unbounded-entry
fixed-literal obstruction as a subproblem. Its permanent-saturation
argument applies to the entire finite installed menu, including
routing root Reads, and survives adaptive Updates. Thus no finite
complete fixed-literal installation handles all lags. This does not
exclude sourcewise termination with growing workspace and literals.

The same fixed-shape restriction permits reuse of §9.6's original-cone
separation: a successful observer must actually separate each of the
$h$ independent original labels. Its static installed-union requirement
of at least $h\lceil(T+1)/3\rceil$ query words, plus two halt words,
also applies under that section's complete-state, fixed-literal and
zero-Update hypotheses. An installed-union count is not a lower bound
on that many queries in every run. These fixed-shape suppliers alone do not establish the unknown-shape
width lower bound. The equal-depth comb-cone union in Theorem 10.2
supplies that additional bound, and Theorem 10.3 combines it with the
present construction. The installed-union requirement does not assert
that a run visits all those words, or that this construction minimizes
acquisition or immutable storage.

The nonduplicated quantitative content is the combination of a
source-driven clock alignment, induction-certified branch-cutoff
trials, and the paid complete table (SLHC.11.9)–(SLHC.11.11).
The alignment reduces the number of candidate bits without giving
away an epoch; cutoff makes every failed trial small even when the
current tree is large; the actual one-bit routes preserve polynomial
calls when path and counter changes reset many logical bits.

| Supplier | Exact use and retained boundary |
| --- | --- |
| [ABT §§9.2–9.4][ABT-ENTRY] | Unknown-shape, fixed-original-leaf-count history fibers and future-experiment indistinguishability. Only the parity consequence and monotone leaf-count facts are consumed; no new fiber classification is claimed. |
| [SLH §§1–2][SLH] | Same-source literal primitives, right clock, guarded historical decoder, and its image hypothesis. Every actual invocation has the witness $v_N$ proved before decoding. |
| [SLH §§31–32][SLH] and §§8–9 of this volume | Original-cone transport, parity and complete-response boundaries, Fibonacci growth and static suffix comparisons. A known skeleton or reference is not supplied here. |
| [NativeFullSourceProducer][SLHC11-PRODUCER] and [NativeEffectiveSourceProducer][SLHC11-EFFECTIVE] | Source-total preorder and the effective selector on acquired control, on their stationary-source contracts. Full subtree output, retained trace and numeric workspace are not free fields in the present observer. The bounded path consumer and its explicit paid rows establish the new resource correspondence. |
| [DelayedOriginalReadout][SLHC11-DECODER] | The declarations right_clock_iterate, right_clock_readout, original_presence_guard, original_decoder_correct and original_query_bounds use the same source and delayed-image domain. Address false/true means $L/R$; source true/false means $\alpha/\beta$, opposite to the numerical parity convention here. |
| [FIB §§26–27, 45–47][FIB] | Complete Moore control, exact reachable supports, descending rank and conditional one-bit services. The present explicit table proves adjacency; the unchanged-prefix alternative is not assigned its new width bound. |

[Gray's *Pulse Code Communication*, US2632058A][GRAY-PATH], supplies the
classical reflected binary code whose adjacent words differ in one
digit; (SLHC.11.10) explicitly checks the needed three-bit cycle.
[Cabello, Eppstein and Klavžar, *The Fibonacci Dimension of a Graph*][CEK],
Proposition 3.1, supplies the zero-interleaving map used in
(SLHC.11.9). Their proposition is stated for isometric graph embeddings;
here its displayed map is used directly on binary words, where
one-coordinate adjacency and no-$11$ follow coordinatewise.
Their Corollary 3.6 concerns the isometric dimension of finite trees
and supplies FIB §47's alternative, not a lower bound for this table.
The Havel–Morávek adjacency formulation is used through the FIB §45
interface; no induced or isometric encoding is needed.

These are attributed mature suppliers. The parity acquisition and
resource combination here is repo-derived ordinary conditional
mathematics. It is not new Lean kernel verification, an assertion of
worldwide novelty, a general-purpose compiler theorem, or a claim
that the stated physical services have been constructed.

[SLHC11-PRODUCER]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean
[SLHC11-EFFECTIVE]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.lean
[SLHC11-DECODER]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean

## 追加锚（本行以下为增补区）

## 12. Supplied shape: Fibonacci capacity and the unknown-entry width leading coefficient

This appendix refines the supplied-shape width orders in Proposition 10.5
under Definition 9.1's contract. Its fixed public skeleton distinguishes
this comparison from the unknown-shape tasks of §§10–11.

**Definition 12.1 (width minima for the full unknown-entry task).**
Fix Definition 9.1's public full ordered skeleton $S$, with even
$h\ge2$ independently labelled leaves, and a finite integer $T\ge0$.
Keep all $2^h$ assignments and all entry lags $0\le t\le T$, with
source-independent deterministic initialization and no reference leaf.
Let $`\ell_a^*(S,T)`$ be the least complete no-$11$ word length among
correct controllers in that definition's comparison class, which allows
adaptive genuine Updates. Let $`\ell_s^*(S,T)`$ be the corresponding
least length with zero actual Updates on every promised run. The active
class also allows zero-Update runs. Both classes retain the permitted
finite deterministic internal work: all its mutable state is counted,
it obtains no source input, and every query word selects one fixed,
fully materialized literal. Each halt word has one fixed output.
Every actual primitive reply immediately selects a hold or one legal
bit change and is discarded. These minima concern word length alone,
without minimizing the other resource coordinates.

Use $K,M,d_i,D,A_S,c$ from (SLHC.24), and set

$$
d_F(n)=\min\{d\in\mathbb N_0:F_{d+2}\ge n\}\quad(n\ge1),
\qquad r=\left\lceil\frac{T+1}{3}\right\rceil.
\tag{SLHC.38}
$$

Thus $d_F$ inverts the capacity of the complete no-$11$ word space,
not the size of a selected supported subgraph. The constructions below
make both width minima well defined.

**Theorem 12.2 (full-table native width at Fibonacci leading order).**
Under Definition 12.1, the entire expanded active and static controllers
of §§9.4–9.5 have faithful immediate encodings with respectively

$$
\begin{aligned}
\ell_a&=d_F(h+1)+7,& |W_a|&=8h+8,\\
\ell_s&=d_F(M+1)+7,& |W_s|&=8M+2.
\end{aligned}
\tag{SLHC.39}
$$

Each encoding is injective on every installed state, including those
with empty actual support. It preserves the instruction, literal,
successor on every typed response row, and fixed halt output of that
state. On every same actual entry $E(x,t)$ it consequently preserves
every primitive, raw reply, source successor, exact support, remaining
primitive rank and first halt. Both constructions have zero internal
instructions. The minima over the full comparison classes satisfy

$$
\begin{aligned}
d_F(h+2)&\le\ell_a^*(S,T)
 \le d_F(h+1)+7\le d_F(h+2)+7,\\
d_F(hr+2)&\le\ell_s^*(S,T)
 \le d_F(M+1)+7\le d_F(hr+2)+9.
\end{aligned}
\tag{SLHC.40}
$$

In particular, with $\varphi=(1+\sqrt5)/2$,

$$
\begin{aligned}
\ell_a^*(S,T)&=\log_\varphi h+O(1),\\
\ell_s^*(S,T)&=\log_\varphi\!\bigl(h(T+1)\bigr)+O(1).
\end{aligned}
\tag{SLHC.41}
$$

The constants are uniform over all these $h,T$ and all supplied
skeletons, including unbalanced skeletons with their actual leaf depths.

Proof. Use the mathematical state names $Q,B,C,V$ of (SLHC.32) and
§9.5 for the already expanded tables. No two of these states are
identified. Write $N=h$ for the active table and $N=M$ for the static
table; the static table has no $V$ states. Set $d=d_F(N+1)$.

The classical ingredient is a spanning path of $\Gamma_d$. It is
supplied by Sandi Klavžar, *Structure of Fibonacci cubes: a survey*,
Proposition 3.1, pp.5–6 of the [author manuscript][KLAVZAR-PATH],
published in *Journal of Combinatorial Optimization* 25 (2013),
505–522, [DOI 10.1007/s10878-011-9433-z][KLAVZAR-PATH-DOI].
The survey attributes the construction to Cong, Zheng and Sharma
(1993); that attribution is through the survey. The assertion used is
a Hamilton path for every dimension, with consecutive words differing
in one bit; no Hamilton cycle or prescribed endpoint is required.
Since $F_{d+2}\ge N+1$, choose its first $N+1$ words
$z_0,\ldots,z_N$. They are distinct members of $L_d$ and
$d_H(z_i,z_{i+1})=1$ for $0\le i<N$. This path is an immutable
choice in the installed table, not a runtime path generator.

Order four latch coordinates as
$(L_{0,0},L_{0,1},L_{1,0},L_{1,1})$, and denote their one-hot
words by $e_{b,r}$, where $b,r\in\{0,1\}$. For a four-bit word
$\lambda$, concatenate

$$
H(i,a,\lambda)=z_i\,0\,a\,0\,\lambda.
\tag{SLHC.42}
$$

Define the images of all $Q,B,C$ states by

$$
\begin{aligned}
\eta(Q(i,a))&=H(i,a,0000),
 &&0\le i\le N,\quad a\in\{0,1\},\\
\eta(B(i,a,b))&=H(i,a,e_{b,i\bmod2}),
 &&0\le i<N,\quad a,b\in\{0,1\},\\
\eta(C(i,b))&=H(i+1,b,e_{b,i\bmod2}),
 &&0\le i<N,\quad b\in\{0,1\}.
\end{aligned}
\tag{SLHC.43}
$$

For the active table additionally set, for both $a=0,1$,

$$
\begin{aligned}
\eta(V(a,01))&=H(0,a,0100),\\
\eta(V(a,11))&=H(0,a,0101),\\
\eta(V(a,10))&=H(0,a,0001).
\end{aligned}
\tag{SLHC.44}
$$

All these words have length $d+7$ and avoid $11$. Indeed, each
$z_i$ avoids $11$, the two displayed zeros separate the accumulator
from both its neighbors, and each used latch word is either empty,
one-hot, or $0101$, which also avoids $11$.

Here is injectivity on the whole installed set. Distinct $z_i$ separate
distinct stages. At any fixed stage $j$, the $Q$ words have empty
latch. A $B$ word there has latch index $r=j\bmod2$; a $C$ word
there has index $r=(j-1)\bmod2$. Thus $B$ and $C$ cannot collide,
even when their accumulator and latch value $b$ agree. Within each
of these sets the remaining displayed parameters distinguish the words.
At stage zero there is no $C$ word, and the $B$ words use only
$r=0$. The two one-hot polling words in (SLHC.44) use $r=1$, so
cannot collide with those $B$ words. The two-hot polling word is
different from every $Q,B,C$ word and from both one-hot polling
words. Its two choices of $a$ are distinct. No polling word occurs
at any other stage. This covers the initial and final stages as well
as the interior ones, including states unreachable from $Q(0,0)$.
Therefore (SLHC.43) has $2(N+1)+4N+2N=8N+2$ words, and
(SLHC.44) adds exactly six in the active case. Install exactly these
images; all other ambient Fibonacci words have no instruction rows.

For completeness the transported instruction tables are specified on
every typed reply below. In the tables a state name means its full
image under $\eta$, with no retained decoded state. Initialize at
$\eta(Q(0,0))$ in either construction, independently of $x,t$.
At $\eta(Q(N,a))$ the fixed instruction is $\mathsf{Halt}(a)$,
and there are no primitive-response rows at a halt.

At each nonhalt active $Q(i,a)$ execute the fixed literal
$\mathsf{Read}(p_{i+1})$, $p_{i+1}=q_{i+1}R^K$. Its complete
response table is

| State range | $\alpha$ | $\beta$ | $\mathsf{branch}$ | $\mathsf{absent}$ |
| --- | --- | --- | --- | --- |
| $Q(0,a)$ | $B(0,a,a)$ | $B(0,a,a\oplus1)$ | $Q(0,a)$ | $V(a,01)$ |
| $Q(i,a)$, $1\le i<h$ | $B(i,a,a)$ | $B(i,a,a\oplus1)$ | $B(i,a,a)$ | $B(i,a,a\oplus1)$ |

At static $Q(i,a)$, $0\le i<M$, execute entry $i+1$ of the
literal list (SLHC.33). Its four rows are

| State range | $\alpha$ | $\beta$ | $\mathsf{branch}$ | $\mathsf{absent}$ |
| --- | --- | --- | --- | --- |
| $Q(i,a)$, $0\le i<M$ | $B(i,a,a)$ | $B(i,a,a\oplus1)$ | $B(i,a,a)$ | $B(i,a,a)$ |

The common routing rows and the active polling rows are

| State | Fixed native instruction | Successor on each declared reply |
| --- | --- | --- |
| $B(i,a,b)$, $a\ne b$ | $\mathsf{Read}(\varepsilon)$ | $B(i,b,b)$ for each of the four Read replies |
| $B(i,b,b)$ | $\mathsf{Read}(\varepsilon)$ | $C(i,b)$ for each of the four Read replies |
| $C(i,b)$ | $\mathsf{Read}(\varepsilon)$ | $Q(i+1,b)$ for each of the four Read replies |
| $V(a,01)$ | $\mathsf{Update}$ | $V(a,11)$ on $\star$ |
| $V(a,11)$ | $\mathsf{Update}$ | $V(a,10)$ on $\star$ |
| $V(a,10)$ | $\mathsf{Read}(\varepsilon)$ | $Q(0,a)$ for each of the four Read replies |

These are precisely §§9.4–9.5's expanded rows: the three routing
cases are its accumulator correction, stage advance and latch clearing
in that order. In particular, every $B$ advancing its stage has
$i<N$, and $C(N-1,b)$ clears into the installed halt $Q(N,b)$.
Every successor in these tables is installed. The actual root reply
on this $h\ge2$ family is branch, but the other three root-response
rows remain present and have their specified successors. The two
pilot branch holds, including the row at $Q(0,1)$, also remain
unchanged. No unsupported row is replaced by a different completion.

Every nonhold response is an edge of the new Fibonacci cube. Each
accepted data response adds one latch bit. The first routing case
changes only $a$ to $b$; the second changes only the one differing
coordinate of $z_i,z_{i+1}$, leaving its latch untouched; the third
clears just that latch. For a polling retry, the four latch patterns
are

$$
0000\ \longrightarrow\ 0100\ \longrightarrow\ 0101
\ \longrightarrow\ 0001\ \longrightarrow\ 0000.
\tag{SLHC.45}
$$

In order these four changes follow an absent data Read, an Update,
another Update, and a paid root Read. The stage and accumulator stay
fixed on this square. Each change is one bit and every intermediate
word is legal. The active branch holds change zero bits. These are
all typed rows, so the edge requirement is the full $G_{\rm all}$
requirement of FIB §§45.4–45.5, not only its supported-edge version.
Extra cube adjacencies supply no additional table transitions. The
lookup table chooses the entire next instruction from the complete
word; the immediate response service chooses the indicated successor
and discards the raw reply. There is no internal instruction, free
stage counter or separate polling phase register.

To check the actual-source transport, denote the old table's instruction
and response functions by $I_9,\delta_9$, and the new ones by
$I_{12},\delta_{12}$. The displayed rows establish, at every installed
nonhalt $v$ and every reply of its instruction's declared type,

$$
I_{12}(\eta(v))=I_9(v),\qquad
\delta_{12}(\eta(v),o)=\eta(\delta_9(v,o)).
\tag{SLHC.46}
$$

The first equality includes the literal itself and the instruction
type, and holds also at each halt with its fixed output. Fix one
original assignment and entry $(x,t)$. Initially both devices are
exactly $E(x,t)$, with old control $Q(0,0)$ and new control
$\eta(Q(0,0))$. If the devices agree at an event and the controls
correspond by $\eta$, (SLHC.46) selects the identical primitive.
The same device then gives the identical raw reply and device
successor. Read leaves that device unchanged. Update applies $\rho$
to that very device and gives its same constant acknowledgement;
it is genuine by the clock identity used in §9.4. The second equality
in (SLHC.46) gives the corresponding next control immediately.
Induction proves equality of the entire actual primitive history and
of the number of completed Updates at every event. It does not
replace a source by another member of an observational fiber.

For explicit support transport let $\mathcal C_v^{(9)}$ contain exactly
the pairs $(\pi(x),E(x,t+j))$ attained at old state $v$ on a promised
run, where $j$ is the number of actual post-entry Updates at that
position. Let $\mathcal C_w^{(12)}$ be the corresponding definition
for the new table. The induction, in both directions on the installed
image, yields

$$
\mathcal C_{\eta(v)}^{(12)}=\mathcal C_v^{(9)}.
\tag{SLHC.47}
$$

This also holds for empty supports; their installed words were not
deleted. Sections 9.4–9.5 prove finite completion of each old run.
On an old supported triple $(z,u,v)$ define $R_9(z,u,v)$ to be its
deterministic number of remaining primitives to the first halt.
It is well defined: the same current device and complete control have
the same future, even if more than one history reaches them. It is
finite on exact supports by those sections. Set

$$
R_{12}(z,u,\eta(v))=R_9(z,u,v).
\tag{SLHC.48}
$$

Each actual primitive decreases this rank by exactly one. Initial
coverage, legal actions and same-source successor closure follow from
(SLHC.46)–(SLHC.47). Each halt retains its fixed payload, and only
$Q(N,a)$ halts. Therefore the first halt occurs at exactly the old
event and outputs the old correct bit $\pi(x)$; there is no earlier
output or intervening halt. This supplies FIB §27.2's full support–rank
certificate. It also gives the control equivalence and identity
address map for the run-transport interface of §7.2, with
$\operatorname{obs}_{x,t}(j,p)=r_{\rho^{t+j}u_x}(p)$ and $j$
counting Updates only. Output correctness uses the fixed payload and
§9's invariant; halt-endpoint uniqueness alone does not supply it.
Neither $j$, the supports, nor the rank is an observer input.

In particular the native readout and parity arguments of §§9.4–9.5
apply without a new acquisition proof. The active table makes exactly
$k=K-\lfloor(t+x_1)/2\rfloor$ polling retries and thereafter stays
at epoch $\tau=t+2k$. Each accepted contribution is
$(t\bmod2)\oplus x_i$. The static scan has exactly one leaf reply
in each cone and the same contribution. Even $h$ cancels the common
entry-parity term, giving the required original parity. These facts
concern the same $x,t$ as in (SLHC.46); no source-independent
normalization or acquired reference is added. Injectivity, word length
and row legality now prove (SLHC.39) and the constructive sides of
(SLHC.40).

For the lower sides reuse §9.6's bounds (SLHC.26) on this exact
comparison class. Its same-run leaf-flip witnesses require $h$
distinct fixed-literal query words. Its static comparisons of
$E(0^h,t)$ and $E(e_i,t)$ for each cone and each $0\le t\le T$
require $r$ query words per cone, because one fixed suffix separates
at most three adjacent atomic ranks. In both cases the two fixed
outputs require two additional halt words. Those arguments explicitly
allow arbitrary finite counted internal work; in the static case
unused Update rows remain allowed. The capacity
$|L_\ell|=F_{\ell+2}$ therefore gives
$`d_F(h+2)\le\ell_a^*(S,T)`$ and
$`d_F(hr+2)\le\ell_s^*(S,T)`$. No lower bound here is inferred
from the two-valued target alone or from a restriction to the exhibited
tables.

Monotonicity of $d_F$ gives the last active inequality. For the static
one, $r\ge1$ and $T+1\le3r$ imply
$T\le3r-1\le4r-2$, hence $K+1\le2r$. Thus
$M+1\le2hr+1\le2(hr+2)$. The Fibonacci recurrence gives

$$
F_{d+4}=2F_{d+2}+F_{d+1}\ge2F_{d+2},\qquad
d_F(2n)\le d_F(n)+2.
\tag{SLHC.49}
$$

Apply this with $n=hr+2$ to obtain the final $+9$ in (SLHC.40).
For the leading coefficients, induction using
$\varphi^2=\varphi+1$ gives
$\varphi^d\le F_{d+2}\le\varphi^{d+1}$ for all $d\ge0$.
Consequently
$\log_\varphi n-1\le d_F(n)\le\lceil\log_\varphi n\rceil$.
Together with $(T+1)/3\le r\le T+1$, these inequalities and
(SLHC.40) prove (SLHC.41) with absolute additive constants. No
leaf-depth term entered this width estimate. The classical spanning
path is the cited ingredient; the full-table injection with the
seven-bit control block and its native transport is the application
proved here. $\square$

**Corollary 12.3 (exact resources of the narrower installations).**
For the encodings of Theorem 12.2, every per-source resource coordinate
of Theorem 9.2 and §9.5 is retained, with the new word lengths in
(SLHC.39) used for word storage. Specifically, set
$A_s=(K+1)A_S+hK(K+1)/2$. Through the first halt on $(x,t)$,

| Quantity | Active encoding | Static encoding |
| --- | --- | --- |
| Installed words | $8h+8$ | $8M+2$ |
| Actual Reads | $3h+2k+c$ | $3M+c$ |
| Actual Updates | $2k$ | $0$ |
| Internal instructions and internal writes | $0$ | $0$ |
| Response bit changes | $3h+4k+c$ | $3M+c$ |
| Submitted address-length sum | $A_S+hK+k(d_1+K)$ | $A_s$ |
| Maximum submitted literal length | $D+K$ | $D+K$ |
| Typed successor entries | $32h+12$ | $32M$ |
| Full word-key bits | $(8h+8)\ell_a$ | $(8M+2)\ell_s$ |
| Full successor-word bits | $(32h+12)\ell_a$ | $32M\ell_s$ |
| Fully inlined data-literal letters | $2(A_S+hK)$ | $2A_s$ |
| Installed fixed halt-payload bits | $2$ | $2$ |

The source peaks are exactly $L_x(\tau)$ and $L_x(t)$ leaves, where
$\tau=t+2k$ and $L_x(v)=\sum_iF_{v+x_i+1}$. The worst peaks
over the full promised family are

$$
\begin{aligned}
\max_{x,\,0\le t\le T}L_x(\tau)
 &=\begin{cases}
h,&T=0,\\
F_{2K+2}+(h-1)F_{2K+3},&T\ge1,
\end{cases}\\
\max_{x,\,0\le t\le T}L_x(t)&=hF_{T+2}.
\end{aligned}
\tag{SLHC.50}
$$

The literal node count is twice the corresponding leaf count minus
one. All setup and execution services remain separately charged as in
(SLHC.35).

Proof. Theorem 12.2 transports each actual primitive and each fixed
literal without adding or deleting a step. Its nonhold rows change
exactly one bit, as did the old table; its two pilot holds still have
zero changes and are unsupported on the promised family. Therefore
§9.5's counts of $h+k$ active data Reads, $k$ polling-return root
Reads and $2h+c$ routing root Reads transfer exactly. So do the
$2k$ genuine Updates and the $3M+c$ static Reads. First halt is
after $3h+4k+c$ active primitives or $3M+c$ static primitives.
The address counts use $d_i=|q_i|$ and their actual sum and maximum,
without replacing the supplied skeleton by a balanced one.

The row bijection gives the same $8h+2$ active Read rows, four
Update rows and two halt rows, and the same $8M$ static Read rows
and two halt rows. Four successors per Read and one per Update give
the stated typed-entry counts. Full keys and full successor words
now each have the lengths (SLHC.39); multiplying by these unchanged
row counts gives the displayed word-storage bills, before tags,
framing or indexes. The data literals still occur twice each, while
the empty root literals still require their representation, lookup
and execution despite having zero letters. An explicitly shared
immutable dictionary instead has $A_S+hK$ active or $A_s$ static
address letters, plus separately paid references and framing. The
two fixed halt payloads occupy two bits, of which a run outputs one.

Equality of actual source histories gives the same peaks and extremizers
as §9.5, proving (SLHC.50) without replacing them by the coarse bound
$hF_{2K+3}$. In the active case the maxima of Reads, Updates, response
changes and address sum are still respectively
$4h+2K$, $2K$, $4h+4K$ and $A_S+hK+K(d_1+K)$, jointly
attained at $t=0,x=1^h$. For $T\ge1$ the largest source peak
instead occurs at $t=1,x=(0,1,\ldots,1)$; the former entry has
peak $hF_{2K+2}$ and is not a joint maximizer of the source coordinate.
The static Read and write maxima remain $3M+h$. Its source maximum
occurs at $t=T,x=1^h$; it also attains these operation maxima when
$T$ is even, whereas for odd $T$ the source and operation maxima
are not jointly attained, exactly as in §9.5.

The service decomposition (SLHC.35) still charges promise establishment,
source preparation, compilation, installation, initialization, every
lookup, literal delivery, native execution, response write and final
output separately. The chosen $z_i$ are compiled constants; their
existence supplies neither free compilation nor free lookup. Numerical
tariffs for these services are not identified between implementations
merely because the primitive histories agree. All retained $S,T$ data,
dictionary indexes and fixed output representations retain their
installation bills. A service needing a persistent cursor, decoded
stage, accumulator or response buffer outside the counted word would
require a different complete-state accounting. The source leaf and
node counts describe literal occurrences, not a physical storage tariff.

The constructive quantifiers remain
$\forall S\ \forall T<\infty\ \exists C_{S,T}\ \forall x\ \forall t\le T$
in the even-$h$ domain. The collision obstruction for odd $h,T\ge1$
in §9.3 and the absence of one finite installation for unbounded lag
in §9.7 retain their original scopes. Although $\ell_a$ is independent
of $T$, its installed literals contain $R^K$ and therefore depend on
the finite promise. The estimates (SLHC.40) determine the leading
coefficients and additive intervals; they do not determine the exact
integer minimum widths, minimum installed-state counts or optimal
joint resource costs. The conditional ordinary mathematical result
does not establish physical service availability, a total-cost or
Pareto optimum, kernel certification or worldwide originality.
$\square$

[KLAVZAR-PATH]: https://www.fmf.uni-lj.si/~klavzar/preprints/FibonacciCubesRevised.pdf
[KLAVZAR-PATH-DOI]: https://doi.org/10.1007/s10878-011-9433-z

## 追加锚（本行以下为增补区）

## 13. Bounded genuine Updates and binary-size native acquisition

**Definition 13.1 (the capped task and its resource coordinates).**
Retain exactly Definition 10.1's all-shape family $\mathcal G_h$,
entry $\rho^t u$ with $0\le t\le T$, and original parity $\pi(u)$.
The literal, response, complete-word and common-initialization contracts
are those of Definitions 1.1, 1.3 and 11.1. In particular, a query word
selects a whole installed root-relative literal, and a Halt word selects
one fixed bit. No source-dependent initial field, old record, origin,
shape, reference label, epoch or address-generation service is supplied.
All routing operations below are paid native Reads, with their replies
immediately discarded after a hold or one bit change.

For a finite installation let $M$ be the number of **distinct** installed
Read literals, $n_R$ its number of query words, and $W$ its complete
installed word set. Repeated copies of one literal count once in $M$
and separately in $n_R$. On one run let $Q,U,A,P_{\rm run}$ respectively
count actual Reads, genuine post-entry Updates, total submitted address
letters, and maximum submitted literal length. Let
$\ell_{\le v}^{\min}(h,T)$ be the minimum complete no-$11$ width among
correct terminating controllers with $U\le v$ on every promised run,
where $v$ is a nonnegative integer. Entry lag is not a post-entry Update.

The lower comparison may also contain deterministic source-free internal
steps: they receive a separate count $I$, have no observation, and keep
all their mutable state inside the counted word. Each such step may
change arbitrarily many counted bits. Each Read state still selects one
fixed literal, and each Halt state one fixed bit. The native upper
construction has $I=0$ and no internal writes. Thus allowing the larger
class in a lower bound supplies no free internal work to the upper bound.

**Theorem 13.2 (one clock-cell controller and its simultaneous bills).**
Suppose $h\ge2$ is even and $T\ge1$. For any even integer $\Delta\ge2$
put, with $\lambda(n)=\lceil\log_2 n\rceil$,

$$
\begin{aligned}
J&=\left\lceil\frac{T+2h}{\Delta}\right\rceil,
&g&=\lambda(J),&e&=\lambda(2h+1),\\
k&=h+3+\lambda(h)+2\lambda(h+1)+e+g,
&\ell&=4k+15,&R&=2k+7,\\
C_h&=(2h+1)(4h-2)=8h^2-2,
&P&=h-1+J\Delta/2,&W_*&=2^{2k+8}.
\end{aligned}
\tag{SLHC.13.1}
$$

There is one common complete controller $C_{h,T,\Delta}$ of width
$\ell$ and $W_*$ installed words, with the following bounds on each
actual promised run. Define only for the proof

$$
K=t+\kappa(u),\qquad j=\lfloor K/\Delta\rfloor,
\qquad B_j=(j+1)\Delta-2.
\tag{SLHC.13.2}
$$

Then

$$
\begin{aligned}
U&=\max(0,B_j-K)\le\Delta-2,\\
Q+U&\le R\bigl(g+2U+1+C_h\bigr),\\
A&\le P\bigl(g+U+1+C_h\bigr),\qquad P_{\rm run}\le P,\\
\text{response bit changes}&=Q+U,\qquad I=0.
\end{aligned}
\tag{SLHC.13.3}
$$

Every actual Update acts on the same current source and is genuine.
The first Halt outputs $\pi(u)$. Every installed typed response row,
including an unreachable one, is a legal hold or one-bit change.

A bound on the distinct installed menu, including routing, is

$$
M\le 2J\bigl(1+(2h+1)(2^h-1)\bigr).
\tag{SLHC.13.4}
$$

The displayed installation has exactly $n_U=2J$ Update words,
four Halt words and $n_R=W_*-4-2J$ query words. Some of these words
have empty actual support; in particular at $\Delta=2$ no Update word
is visited. For $b_P=\lambda(P+1)$ and $b_\ell=\lambda(\ell+1)$,
one explicit padded table representation uses

$$
S_{\rm tab}=W_*(\ell+2+b_P+P+4b_\ell)
\tag{SLHC.13.5}
$$

bits, with $\ell$ further immutable initialization bits. It has
$4n_R+2J$ typed response entries. There are $n_R$ installed literal
copies, including empty literals, and at most $n_RP$ unpadded address
letters. These are upper construction costs, not optimal storage claims.

If $b_\beta$ is the original number of $\beta$ leaves and
$\tau=t+U$, the same run's source has peak node count exactly

$$
V(\tau)=2\bigl((h-b_\beta)F_{\tau+1}
                         +b_\beta F_{\tau+2}\bigr)-1
\le 2hF_{T+\Delta}-1.
\tag{SLHC.13.6}
$$

The bounds in (SLHC.13.3)–(SLHC.13.6) hold together for this controller;
no assertion that their separate maxima have a common attaining input
is needed.

Proof. The source laws, decoder and traversal are those of SLH §§2, 6,
31–32, 36 and Lemma 11.3. The extra acquisition is a finite ordered
search of the current right clock, followed by a bounded alignment.
All comparisons specified below are actual literal Reads. Ordered
halving is the classical method already used in SLH §§6, 36; see
[Nowak, *The Geometry of Generalized Binary Search*, §I][SLHC13-NOWAK]
for its hypothesis-partition formulation. No generalized-search
coherence theorem or free comparison oracle is assumed.

The original rightmost leaf has depth at most $h-1$, so
$0\le\kappa(u)\le2h-1$ and $0\le K<T+2h\le J\Delta$.
Partition the possible clocks into cells
$[j\Delta,(j+1)\Delta-1]$, $0\le j<J$. Install the balanced ordered
binary tree of these $J$ cells. At a node whose cell interval is
$[a,b]$, $a<b$, set $m=\lfloor(a+b+1)/2\rfloor$ and read

$$
R^{m\Delta/2}.
\tag{SLHC.13.7}
$$

By `right_clock_readout`, absence means $K<m\Delta$, and each of the
other three replies means $K\ge m\Delta$. Recurse into $[a,m-1]$
or $[m,b]$ respectively. Each surviving cell interval has at most
$\lceil(b-a+1)/2\rceil$ elements. Hence at most $g$ actual search
Reads reach the correct cell. Every one of these Reads leaves the
same current tree unchanged. A tree with $J$ leaves has $J-1$ internal
nodes, so its internal-node identifier fits in $g$ bits; when $J=1$
there is no search and the sole identifier has zero width.

Having acquired the cell $j$, poll the fixed literal $R^{B_j/2}$.
On absence execute one genuine Update and poll again. On $\alpha$
or $\beta$ begin the trials; branch goes to a nonhalting error control.
The known entry cell gives $K\le B_j+1$. After $a$ such Updates the
clock is $K+a$, by `right_clock_iterate`; routing Reads do not change it.
Thus precisely $U=\max(0,B_j-K)$ Updates occur, followed by an accepted
poll. Since $K\ge j\Delta$, $U\le\Delta-2$. The final clock is
$B_j$ or $B_j+1$. There are exactly $U+1$ polling Reads and $U$
Updates. This acquires an endpoint on the same source; it is not an
origin marker. Every Update changes the source because it increases
$\kappa$ by one.

Set the installed candidate origin for this cell to

$$
N_0(j)=\max(0,B_j-2h+1),\qquad N=N_0(j)+r,
\quad 0\le r\le2h.
\tag{SLHC.13.8}
$$

At the stationary post-poll source $y=\rho^\tau u$ the clock identity
and its acquired endpoint imply

$$
N_0(j)\le\tau\le B_j+1,\qquad \tau-N_0(j)\le2h.
\tag{SLHC.13.9}
$$

For the last inequality, if $B_j\ge2h-1$, subtract $B_j-2h+1$;
otherwise $N_0=0$ and $\tau\le B_j+1\le2h-1$.
Start Lemma 11.3's cutoff trial at $N=N_0(j)$, incrementing $r$ only
after rejection. Before every decoder invocation there is the actual
image witness

$$
v_N=\rho^{\tau-N}u,\qquad y=\rho^N v_N.
\tag{SLHC.13.10}
$$

The first witness follows from (SLHC.13.9). A licensed rejection
implies $N<\tau$, since the trial at $N=\tau$ traverses $u$ and
finishes. Therefore the next $N+1$ is also licensed. This induction,
not finite compatibility of raw replies, precedes every later trial.
No trial goes beyond $\tau$, and at most $2h+1$ trials occur.

For an explicit parameter correspondence to Lemma 11.3, its $y,h,\tau$
are the actual post-poll source, the unchanged promised leaf count,
and $t+U$; its $N$ is (SLHC.13.8). Its virtual address $p$ is the
counted preorder path below. At $N=0$ its Read is $p$. For $N>0$,
its nonroot guard is $p^-R^{\lfloor N/2\rfloor+1}$ and its value
Read is $pR^{\lceil N/2\rceil}$, with the exact guard and odd/even
reply table of (SLHC.11.5) and Lemma 11.3. At the root only the value
Read occurs. Both Reads are executed and charged even when their
literals coincide. The virtual node is reached because the traversal
only descends from a decoded branch. A rejected guard or an even-offset
absent value cannot occur on (SLHC.13.10); an odd-offset absent value
is the valid virtual leaf $\alpha$.

Each trial visits at most $2h-1$ nodes, at depths at most $h-1$,
and uses at most $4h-2$ intermediate Reads. Finishing gives a complete
$h$-leaf $v_N$. Apply ABT Theorem 9.2 to the two same-current histories
$(u,\tau)$ and $(v_N,N)$ on its unbounded-epoch, fixed-original-leaf-count
domain. They are identical or its uniform adjacent-epoch pair; even
$h$ gives equal parity in either case. This proves the target even
when the representative's $N$ is outside the initial promise $[0,T]$.
The original entry still lies in that promise. The wrong-image
$\langle\alpha,\beta\rangle$, $t=0$, $N=1$ example of §11.7 violates
(SLHC.13.10) and is never licensed by this construction.

It remains to specify the entire control and its complete realization.
Extend Construction 11.5's intermediate fields in its stated bit order
by a $g$-bit field $c$. Its old candidate field $j$ is here named $r$
and has $e=\lambda(2h+1)$ bits. The other fields are exactly
$p,s,b,l,a,\mu$, of widths $h-1,\lambda(h),\lambda(h+1),
\lambda(h+1),1,3$. This is precisely the $k$ in (SLHC.13.1).
Use old mode codes 0 through 6 unchanged and code 7 for SEARCH.

In SEARCH, $c$ identifies one of the $J-1$ internal search nodes in
any fixed enumeration, with its two children and threshold installed
in that row; all other nonmode fields are zero. If its selected child
is internal, the response replaces $c$ by that node's identifier.
If it is a leaf $j$, the response changes to POLL and sets $c=j$.
Absence selects the lower child; $\alpha,\beta,$ branch select the
upper child. No interval bounds, midpoint, path through the search,
raw response or address-generation counter persists outside these
fields. When $J=1$ the common initial intermediate state is POLL
with $c=0$; otherwise it is the root SEARCH identifier. All remaining
initial fields are zero and independent of the actual source.

In POLL and UPDATE retain only $c=j<J$ and the mode; all other
fields are zero. POLL reads $R^{B_c/2}$. Absence selects UPDATE in
the same cell, $\alpha,\beta$ start root VALUE with $r=0$ in that
cell, and branch selects canonical ERROR. UPDATE performs the native
Update and returns to POLL in that cell. Normal VALUE and GUARD states
retain $c<J$, $0\le r\le2h$ and the old path/counter bounds. Substitute
$N=N_0(c)+r$ for the old candidate formula in every old literal and
response rule. A cutoff increments $r$ and resets precisely the old
path, length, branch, leaf and parity fields while retaining $c$.
An increment beyond $2h$ selects ERROR. All preorder advancement,
parity accumulation, guard acceptance and overflow rules are exactly
Construction 11.5's rules with this substitution.

HALT0, HALT1 and ERROR are canonical: all nonmode fields, including
$c,r$, are zero. Completion selects the appropriate canonical Halt.
Every malformed intermediate code, including an out-of-range search
identifier or nonzero field required to vanish, reads the root and
sends every reply to canonical ERROR. ERROR reads the root forever.
This specifies all four responses of every Read and the sole constant
acknowledgement of every Update. At $\Delta=2$ absence at POLL is
unreachable; its installed Update successor is still legal.

Denote this particular total finite table by $I_{13},\delta_{13}$.
Use Construction 11.6 with the following exact row substitution:

$$
(k(e),I,\delta,z_{\rm init})
\longmapsto(k,I_{13},\delta_{13},z_{13,\rm init}).
\tag{SLHC.13.11}
$$

The two banks each have $k$ bits, the same five flags encode the four
Read replies and Update acknowledgement, and the same three phase bits
follow (SLHC.11.10). The installed set is exactly
$J_{\rm sep}(\{0,1\}^{2k+8})$, where $J_{\rm sep}$ is §11.5's
zero-interleaving map; its use here is distinct from the integer $J$.
The old table's ready phases 000 and 010 execute respectively
$I_{13}(A)$ and $I_{13}(B')$. Their immediate responses set the one
typed flag. In the corresponding flagged filling rows the destination
is respectively $\delta_{13}(A,r')$ or $\delta_{13}(B',r')$, where
$r'$ denotes that flag's reply, not the candidate counter. Every other
row of the phase/erase/clear/hold table is unchanged.

These substitutions preserve each hypothesis used in the transfer
proof: a ready destination bank is zero; its source bank and one typed
flag remain fixed while the destination is filled; $\delta_{13}$ is a
fixed $k$-bit word on every typed input; and source instructions have
only the same four replies or constant acknowledgement. Hence for
one intermediate edge $z\to z'$ the two alternating transfer costs are
exactly

$$
c_{A\to B'}=|z|_1+|z'|_1+5,\qquad
c_{B'\to A}=|z|_1+|z'|_1+7\le R.
\tag{SLHC.13.12}
$$

Here the first expression too is at most $R$. The initial primitive
sets its counted flag and discards the raw reply. Each following row
executes one root Read and flips the stated destination, source, flag
or phase bit. It has no free silent transition. For unmatched installed
words the old completion holds on all four replies. Thus every word
in the installed set has its specified instruction and every typed
row remains one-bit legal. This is the old explicit row proof applied
to the specified table, rather than an inference from state capacity.
The classical zero-interleaving map is the map in CEK Proposition 3.1,
used exactly as in §11.5, without an isometric hypothesis on this
control graph.

At each ready state the bank code and actual current tree agree with
the intermediate execution. The first source primitive has its actual
reply and source successor; root routing Reads preserve that successor;
the finite transfer ends at the next ready code. This proves the
correspondence inductively, including the precise genuine Update count.
Search intervals shrink, each absent poll's remaining clock gap decreases
after its one Update, and licensed trials terminate by Lemma 11.3.
The finite Hamming-distance transfers then give native termination.
Only a ready canonical Halt outputs, with the established parity;
there is no earlier output or extra state. As in §11.5, actual reachable
$(\pi(u),y,w)$ supports and the deterministic remaining-call rank satisfy
FIB §27.2. For the expanded logical table's transport through
$J_{\rm sep}$, `run_transport_iff` uses the identity address map and
$\operatorname{obs}_{u,t}(a,p)=r_{\rho^{t+a}u}(p)$, where $a$ counts
only genuine Updates. Routing Reads are retained in that expanded
chronology. The fixed Halt rows supply the output bit separately from
`run_halt_unique`'s endpoint assertion.

Let $s\le g$ be this run's search Read count and let $d_*$ be its
actual total trial Reads. Then $d_*\le C_h$ and the intermediate
execution has exactly $s+U+1+d_*$ Reads and $U$ Updates. For its
successive controls $z_0,\ldots,z_H$, with
$H=s+2U+1+d_*$, the **exact same-run** native count is

$$
Q+U=\sum_{i=0}^{H-1}
 \bigl(|z_i|_1+|z_{i+1}|_1+5+2(i\bmod2)\bigr).
\tag{SLHC.13.13}
$$

Every summand includes its original intermediate primitive; its other
operations are root Reads. This proves (SLHC.13.3)'s operation and
bit-change bounds without conflating Reads with Updates.
Search rays have length at most $(J-1)\Delta/2$ and polling rays at
most $J\Delta/2-1$. Even in installed but unreachable trial rows,
$N\le\max(2h,J\Delta-1)=J\Delta-1$, since $T\ge1$.
Trial literals therefore have length at most $P$. Only the
$s+U+1+d_*$ intermediate Reads contribute nonempty address letters;
all added root Reads have length zero. This proves the two address
bounds, while still charging every root Read in $Q$.

There are at most $J-1$ search literals, $J$ polling literals, one
routing literal, and at most two decoder literals for each of $J$
cells, $2h+1$ candidate values and $2^h-1$ possible virtual paths.
Their union gives (SLHC.13.4); overlaps can only reduce $M$.
There is one canonical UPDATE bank code per cell, two canonical Halt
codes overall, and two ready phases. Thus there are exactly $2J$
Update words and four Halt words in the full installed set; all other
words read. Using §11.6's padded representation with the new $k,\ell,P$
gives (SLHC.13.5), including full word keys, opcodes, lengths, literal
payloads and four hold/flip slots. It does not posit a mutable address
buffer. The installed integer constants and all expanded literals
are common finite data; their construction, selection and delivery
retain separate costs.

Finally $\tau=t+U\le T+\Delta-2$, and the old exact original-cone
Fibonacci count (SLHC.11.16) gives (SLHC.13.6). The source passes through
exactly the versions at $t,t+1,\ldots,t+U$; source-preserving Reads
and all routing steps add no versions. If a physical Update traverses
its input tree, its input-node-volume bill is
$\sum_{a=0}^{U-1}V(t+a)$, with zero sum when $U=0$; allocating each
output version has its corresponding separate bill. No unit physical
Update cost follows from counting a native Update once.

The service vector remains (SLHC.11.15) on this very run, now with
$n=Q+U$: one initialization, $n+1$ instruction selections, $Q$ full
literal deliveries, $n$ immediate response selections/writes and one
bit output, besides promise authentication, source entry and table
construction/installation. A service requiring any additional retained
cursor, latch or phase must include it in the complete word. Width,
call counts, transmitted letters, table storage and source service
are distinct coordinates. $\square$

**Theorem 13.3 (adaptive separation windows and a same-run address bill).**
In the positive regimes of Definition 13.1, every correct controller
with at most $v$ genuine Updates on each promised run satisfies

$$
M\ge 2^{h-1}\left\lceil\frac{T+1}{v+3}\right\rceil,
\qquad
F_{\ell+2}\ge |W|\ge n_R+2\ge M+2.
\tag{SLHC.13.14}
$$

The menu bound also holds without a memory restriction, provided the
installed literal menu is finite. Every successful run has $Q\ge h$.
For every controller there is a single promised run with

$$
\begin{aligned}
P_{\rm run}&\ge h-1+L_T,\\
A&\ge\frac{(h-1)(h+2)}2+hL_T,
\qquad L_T=\left\lceil\frac{\max(T-1,0)}2\right\rceil.
\end{aligned}
\tag{SLHC.13.15}
$$

The latter bounds need no cap on Updates and hold in the larger
source-free internal-work comparison of Definition 13.1.

Proof. Reuse Theorem 10.2's equal-depth comb witnesses. For each
$p\in\{L,R\}^{h-1}$ use the $h$-leaf comb with tip $p$, all leaves
$\alpha$, and its permitted alternative with only that tip changed to
$\beta$. At each initial lag $t\in\{0,\ldots,T\}$ their targets
differ. Before their first separating Read the two runs have identical
control and an identical actual Update count $a$, with $0\le a\le v$.
SLH's original-cone transport makes every observation outside the tip
cone equal. A separating literal therefore has form $ps$, and at that
moment compares $T_{t+a}$ with $T_{t+a+1}$ in the tip cone.

Write $w(s)=\#_L(s)+2\#_R(s)$ and
$D_s=\{n\ge0:r_{T_n}(s)\ne r_{T_{n+1}}(s)\}$.
The guarded atomic law used in §9.6 and CAR §13.4 gives exactly

$$
\begin{aligned}
D_\varepsilon&=\{0,1\},\\
D_s&=\{w(s),w(s)+1\}&&\text{if }s\ne\varepsilon\text{ ends in }L,\\
D_s&=\{w(s)-1,w(s),w(s)+1\}
 &&\text{if }s\ne\varepsilon\text{ ends in }R.
\end{aligned}
\tag{SLHC.13.16}
$$

The left-ending law skips $\alpha$ because that zero-residual address
is not reached. Thus these are consecutive windows of two or three
integers, not unguarded subtree-index formulae.
At first separation $t+a\in D_s$, so all initial lags which this
one installed literal can witness lie in

$$
\bigl(D_s-\{0,\ldots,v\}\bigr)\cap\{0,\ldots,T\}.
\tag{SLHC.13.17}
$$

Its cardinality is at most $v+3$. The subtraction is a union over
possible actual $a$, not permission to assign separate optimal $a$
values to one run. It remains an upper cover of every adaptive first
separation. Each of the $T+1$ required lag comparisons must be
witnessed, so at least $\lceil(T+1)/(v+3)\rceil$ different literals
extend each $p$. The $2^{h-1}$ equal-depth tip cones are disjoint;
summing proves the first inequality. Source-free internal steps add no
separation: induction over the common history still applies. All their
mutable control is counted for the width consequence.

One query word has only one literal, and both parity values occur.
Two distinct fixed-output Halt words are necessary and are disjoint
from query words. The supplied no-$11$ count $|L_\ell|=F_{\ell+2}$
then gives the remaining inequalities. These count installation across
shapes and entries; they do not say that any run executes $M$ Reads.
The per-run bound $Q\ge h$ is the original-leaf-flip argument of
§§9.6, 10.2: on one fixed run, the $h$ alternative single-leaf flips
must each have a separating Read in its own disjoint original cone.

For the stronger address assertion take the all-$\alpha$ comb itself
at entry $T$ and keep its one actual run fixed. For each of its leaves
$q_i$, compare the original with only that leaf flipped. Its first
separating Read on the fixed run is $q_i s_i$ at a common update count
$a_i\ge0$. Equations (SLHC.13.16) imply
$T+a_i\le w(s_i)+1$, including the empty suffix. Since
$w(s_i)\le2|s_i|$, every such suffix has length at least $L_T$.
These are $h$ different Read occurrences on this same run, so their
lengths may be summed. The comb's leaf depths are
$1,2,\ldots,h-2,h-1,h-1$, with sum $(h-1)(h+2)/2$ and maximum
$h-1$. At $h=1$ the singleton root instead has depth zero and the
same sum formula is zero. This proves (SLHC.13.15). Additional
Updates can only increase the needed atomic index, and additional
Reads add nonnegative letters. No combination of separately attained
runs enters this argument. $\square$

**Corollary 13.4 (binary-size static calls and the capped minimum width).**
For even $h\ge2$, $T\ge1$, $v\ge0$, the original task has

$$
\ell_{\le v}^{\min}(h,T)
=\Theta\!\left(h+\log_2\!\left(1+\frac{T+1}{v+1}\right)\right)
\tag{SLHC.13.18}
$$

with constants independent of all three parameters. Constants $1/4$
and $64$ suffice for its lower and upper inequalities. This remains
a matching order if the minimum permits the explicitly counted
source-free internal steps of Definition 13.1.
There is a zero-Update native controller with

$$
\ell=O(h+\log_2(T+1)),\qquad
Q=O\bigl((h+\log_2(T+1))(h^2+\log_2(T+1))\bigr).
\tag{SLHC.13.19}
$$

All other costs for that same controller are (SLHC.13.3)–(SLHC.13.6)
at $\Delta=2$. For $T=0$ and every $h\ge1$, the direct traversal
and complete table of Section 11 give $U=0$, width $O(h)$ and
$Q=O(h^2)$; minimum width is $\Theta(h)$ for every cap $v$.

Proof. Choose in Theorem 13.2

$$
\Delta=2\min\!\left(
 \left\lfloor\frac{v+2}{2}\right\rfloor,
 \left\lceil\frac{T+2h}{2}\right\rceil\right).
\tag{SLHC.13.20}
$$

Then $2\le\Delta$, $\Delta$ is even and $\Delta-2\le v$.
Thus the exhibited actual observer respects the cap. If the second
argument of the minimum is selected, $J=1$ and $g=0$.
Otherwise $\Delta\ge v+1$, whence, with
$x=(T+1)/(v+1)$,

$$
J\le1+\frac{T+2h}{v+1}\le2h(1+x),\qquad
 g\le h+1+\log_2(1+x).
\tag{SLHC.13.21}
$$

The same upper estimate on $g$ holds when $J=1$. For $h\ge2$,
$\lambda(h)\le h-1$, $\lambda(h+1)\le h$ and
$\lambda(2h+1)\le h+1$. Hence $k\le5h+3+g$ and
$\ell\le24h+31+4\log_2(1+x)$, which is at most
$64(h+\log_2(1+x))$.

For necessity use $F_{\ell+2}\le2^\ell$ and
$v+3\le3(v+1)$. Then

$$
\left\lceil\frac{T+1}{v+3}\right\rceil
\ge\max(1,x/3)\ge(1+x)/4.
$$

Put $X=h+\log_2(1+x)$. Theorem 13.3 yields $\ell\ge X-3$.
At least three installed words require $\ell\ge2$. If $X\ge4$,
$X-3\ge X/4$; if $X<4$, use $\ell\ge2$.
This proves the uniform lower constant, including the boundary caps.

For $v=0$ or $v=1$, (SLHC.13.20) chooses $\Delta=2$.
The acquired cell has $K\in\{B_j,B_j+1\}$ before any Update,
so its very first poll accepts and $U=0$ on every run. Here
$g=O(\log(h+T))$, $k=O(h+\log(T+1))$ and
$H\le g+1+C_h$. Formula (SLHC.13.13), not just the binary-search
comparison count, proves (SLHC.13.19).
When $v\ge2\lceil(T+2h)/2\rceil-2$, the same formula chooses
$J=1$: initialization is POLL, the actual Updates are still exactly
$\max(0,\Delta-2-K)$, and the resulting width is $O(h)$ with
$Q+U=O(hT+h^3)$. Intermediate caps use the identical cell table.

At $T=0$, Theorem 10.2's comb union lower bound and Section 11's
zero-offset direct traversal give the last assertion, including both
labels at $h=1$. No historical fiber identification is needed there.
The matching result concerns width only: it claims no optimal Reads,
installed-state count, table bits, literal traffic or leading constants.
In particular (SLHC.13.15) forces a worst-run
$\Omega(hT+h^2)$ address bill for even $h\ge2$, $T\ge1$ even when
the number of native calls is polynomial in $h+\log(T+1)$. $\square$

**Proposition 13.5 (finite boundary and the recovered coordinate).**
For odd $h$ and $T\ge1$ the original task remains impossible. For
fixed $h$ there is no single finite complete fixed-literal installation
correct for all unbounded entry lags, even with adaptive Updates.
For fixed $h$ and a fixed width limit $L$, any family of correct capped
controllers over growing $T$ must obey

$$
v+3\ge\frac{2^{h-1}(T+1)}{F_{L+2}-2}.
\tag{SLHC.13.22}
$$

Consequently a width bound depending only on $h$ cannot uniformly
coexist with native calls polynomial in $h+\log(T+1)$ over all $T$.
The acquired coordinate in Theorem 13.2 is a current right-clock cell
and its post-poll endpoint. For even $h\ge2$, $T\ge1$ and even
$\Delta\ge2$, that endpoint determines both the entry clock $K$ and
the actual post-entry Update count $U$ on the entire promised family
if and only if
$\Delta=2$ or $(h,T,\Delta)=(2,1,4)$.
The pointwise recovery condition is (SLHC.13.24) below.
Recovering these two coordinates does not imply recovery of the
original historical epoch or an omitted log. The final fixed output
preserves only original parity.

Proof. ABT §§9.2–9.4 give identical current trees from all-$\beta$
at lag zero and all-$\alpha$ at lag one on the same shape. For odd
$h$ their targets differ. Common initialization and every future native
experiment preserve indistinguishability, so neither more memory nor
Updates solve this case. For unbounded lags, Proposition 10.4's CAR/NRF
permanent saturation applies to the entire installed menu. Alternatively,
(SLHC.13.15) contradicts its finite maximum literal length on arbitrarily
large $T$ in the even-$h$ regime. Equation (SLHC.13.22) follows directly
from (SLHC.13.14). With $h,L$ fixed it requires $v=\Omega(T)$;
actual native calls dominate actual Updates. Applying the bound with
the achieved worst-run Update count excludes the asserted uniform
polynomial call bound. It does not exclude width $O(h)$ and polynomial
calls on a restricted range such as $\log(T+1)=O(h)$.

At the accepted poll the retained cell and the counted $\alpha/\beta$
response flag determine the endpoint $E=\kappa(y)=B_j$ or $B_j+1$;
the raw reply itself is immediately discarded. The existing right-clock
law makes a finite tree's complete right-ray reply profile and its clock
mutually recoverable: a clock $2d+e$ gives branch before $d$, the
corresponding leaf at $d$, and absence afterwards. This is SLH §2's
coordinate correspondence.

For the precise entry-clock boundary, the attained clock domain of
Theorem 13.2 is
$\mathcal K_{h,T}=[2,T+2h-1]\cap\mathbb Z$.
Indeed the rightmost original leaf has depth $d\in\{1,\ldots,h-1\}$
and label $e\in\{0,1\}$, giving $\kappa(u)=2d+e$.
Every such depth is attained: start with a right comb of $d+1$ leaves
and expand one of its left leaves to a full tree with $h-d$ leaves.
Both rightmost labels are allowed independently. Thus $\kappa(u)$
attains every integer from $2$ to $2h-1$, and adding every allowed
$t\in\{0,\ldots,T\}$ gives exactly $\mathcal K_{h,T}$.

Equation (SLHC.13.3) gives the endpoint map on this actual domain:
for $j=\lfloor K/\Delta\rfloor$,

$$
E=f_\Delta(K)=\max(K,B_j),\qquad U=E-K,
\qquad B_j=(j+1)\Delta-2.
\tag{SLHC.13.23}
$$

The cell can be recovered from $E$ as $j=\lfloor E/\Delta\rfloor$,
so different cells never share an endpoint. Within a cell the exact
sets of possible entry clocks are

$$
\begin{aligned}
f_\Delta^{-1}(\{B_j\})
 &=\mathcal K_{h,T}\cap[j\Delta,B_j],\\
f_\Delta^{-1}(\{B_j+1\})
 &=\mathcal K_{h,T}\cap\{B_j+1\}.
\end{aligned}
\tag{SLHC.13.24}
$$

Intervals here contain integers only. At an attained endpoint, $K$
is recoverable exactly when its displayed set is a singleton; the
same condition is necessary and sufficient for recovering $U$, since
$U=E-K$. In particular, the upper endpoint always gives $K=E,U=0$.
At a lower endpoint the condition is precisely
$\max(2,j\Delta)=\min(T+2h-1,B_j)$.
Two distinct clocks in that interval give the same endpoint and
different Update counts, and both are attained by promised histories.
This concerns recovery from the endpoint, equivalently the cell and
accepted reply, without a retained polling history.

At $\Delta=2$ each lower interval has at most one integer, and
$E=K,U=0$ on the entire domain. At $\Delta=4$, the first lower
interval meets $\mathcal K_{h,T}$ only at $2$; the next contains both
$4,5$ exactly when $T+2h-1\ge5$. Since $T+2h-1\ge4$, global
recovery holds in this case exactly when $h=2,T=1$.
For every even $\Delta\ge6$, the first lower interval already
contains the attained clocks $2,3$, so global recovery fails.
These cases prove the stated if and only if.

For attained examples, at $h=2,T=1,\Delta=4$ the entire clock domain
and its endpoints and Update counts are

$$
\begin{array}{c|ccc}
K&2&3&4\\
E&2&3&6\\
U&0&0&2
\end{array}
$$

The three columns are attained respectively by
$(\langle\alpha,\alpha\rangle,0)$,
$(\langle\beta,\beta\rangle,0)$ and
$(\langle\beta,\beta\rangle,1)$.
Thus the endpoint recovers both coordinates on this full promised
domain, including at caps $v=2$ or $3$ under (SLHC.13.20).
For comparison, at $h=2,T=2,\Delta=4$ take the same mixed original
$u=\langle\alpha,\beta\rangle$ at entry lags $1,2$.
Their entry clocks are $4,5$ and their Update counts are $2,1$;
both reach $E=6$ and the same post-poll tree $\rho^3u$.
This is an attained failure of endpoint recovery. Even in the first,
globally recoverable example, the histories
$(\langle\beta,\beta\rangle,0)$ and
$(\langle\alpha,\alpha\rangle,1)$ have the same entry tree,
$K=E=3$ and $U=0$, while their historical entry epochs differ.

The complete observer retains the cell only while needed and
ultimately merges into its canonical parity Halt; it does not output
the clock, Update count or a traversal log.

Even an acquired complete current tree and known original leaf count
retain ABT's uniform adjacent-history doubletons. A new local Update
counter would not separate their entry epochs. The trials determine
a parity-correct representative on those fibers, not an authentic
choice of the older history. At a mixed original, ABT makes the complete entry
tree determine $(u,t)$ and the complete post-poll tree determine
$(u,t+U)$. The latter need not determine $t$ without $U$, as the
mixed-original collision above shows. This controller's one-bit
output is neither of those complete trees and does not provide their
recovery.
A separately acquired, same-source historical record would retain
ABT §9.3's own necessary and sufficient separation condition.

The quantitative composition here links original address cones,
actually advanced relative time, finite literal boundaries and complete
task memory on one source family. Its input promises and conditional
selection/delivery services are precisely those in Definition 13.1;
it asserts no physical spacetime identification. The shape-supplied
comparison in §9 remains different: it installs one shape's cones,
whereas (SLHC.13.14) uses the union over all unknown comb shapes.
CAR §§11–13 and NRF/NPS retain their acquired-fiber, whole-row and
physical-service hypotheses; their feasibility conclusions are not
substituted for this parity construction. The `repo-derived` new
composition is clock-cell localization with capped alignment and the
Update-expanded first-separation windows. SLH's decoder/ordered
acquisition, ABT's fibers, Section 11's cutoff and bitwise transfer,
and CEK's coordinate map retain their existing mathematical roles.
The D5 interfaces are `DelayedOriginalReadout.right_clock_iterate`,
`right_clock_readout`, `original_presence_guard`,
`original_decoder_correct`, `original_decoder_service`,
`NativeFullSourceProducer.native_source_producer` and
`GuardedPhaseExecution.run_transport_iff`, `run_halt_unique`.
Their addresses use false/true for $L/R$ and their source constructors
use true/false for $\alpha/\beta$, opposite to the numerical parity
bits. The private `clock_step`, `original_query_bounds`, `traverse`
and `production_reads` remain parts of those suppliers, not missing
lemmas or new general results. $\square$

[SLHC13-NOWAK]: https://arxiv.org/abs/0910.4397v5

## 追加锚（本行以下为增补区）

## 14. Unknown-shape parity with no added routing calls

**Definition 14.1 (the entire intermediate table as the input).** Keep
Definition 11.1's original domain: every ordered full $h$-leaf tree $u$,
every independent original leaf assignment and every unknown entry
$y=\rho^t u$, $0\le t\le T$. The target is the original $\pi(u)$.
Public data are $h,T$ and the chosen static or active regime, not the
shape, labels, actual entry lag, current clock or a reference leaf.
The positive regimes are $T=0$ for every $h\ge1$, and finite $T\ge1$
for even $h$. Initialization is common and source independent.

Take $e,k=k(e),B,H,P,A_*$ exactly from (SLHC.11.1)–(SLHC.11.2).
Thus $k=h+3+\lambda(h)+2\lambda(h+1)+e$, where
$\lambda(n)=\lceil\log_2 n\rceil$, and the active constant is
$B=2\lceil(T+2h)/2\rceil$. The three choices of $e$ are displayed
in Corollary 14.3.
The controller to be realized is **Construction 11.5 in §11.4**, with
its entire state set

$$
Q_I=\{0,1\}^k,\qquad K_0=2^k.
\tag{SLHC.14.1}
$$

Every bit pattern is installed. In particular this includes noncanonical
halt-mode patterns, invalid padding, out-of-range counters and candidate
indices, the unused mode code, and modes unavailable in the chosen regime.
Their instructions are the specified Read$(\varepsilon)$ and each of their
four responses goes to canonical ERROR. Canonical ERROR has that same
instruction and four self-transitions. These are real typed completion
rows, even though the promised runs never reach them.

There are exactly two canonical halt states, HALT0 and HALT1, each with
its own fixed output and no replies. Put $u_0=1$ for the active positive-$T$
regime, and $u_0=0$ otherwise. There are exactly $u_0$ Update states, with
one $\star$ successor each. All remaining $K_0-2-u_0$ patterns are Read
states with four typed replies. The mode rules fix the instruction and
successor from $z$ and the raw reply alone, including replies outside
actual supports. No acquired input besides the original common setup is
used. The original current tree is updated in place by each actual Update.

The two-bank, flagged, paid-routing controller of Construction 11.6 is a
different realization of this input table. Its inserted root Reads are not
part of the trace specified here. The present realization uses the same
conditional whole-word services of Definition 1.3 and does not add a new
observation, internal instruction or response-retention service.

**Theorem 14.2 (all-pattern redundant realization).** Define

$$
m_0=2^k-1,\qquad f_0=2^{2^k-1-k},\qquad
M_0=2^{2^k-1},\qquad \ell_0=2^{k+1}-3.
\tag{SLHC.14.2}
$$

There is a complete no-$11$ realization of Definition 14.1 with width
$\ell_0$ and exactly $M_0$ installed words. Every one of the $2^k$
intermediate bit patterns has exactly $f_0$ aliases. Its complete table has

| Installed item | Exact count |
| --- | --- |
| Word keys and instruction rows | $M_0=2^kf_0$ |
| Fixed Halt0 words | $f_0$ |
| Fixed Halt1 words | $f_0$ |
| Update words | $u_0f_0$ |
| Read words | $(2^k-2-u_0)f_0$ |
| Typed response entries | $(4\cdot2^k-8-3u_0)f_0$ |

For every typed response at every installed word, including all aliases
of invalid and error patterns, the response immediately holds or flips one
legal bit, and its logical successor is exactly Construction 11.5's
successor. For each original allowed $(u,t)$, every original instruction,
literal, raw reply, current-tree successor and first fixed-bit Halt is
preserved. In particular the result halts correctly with $\pi(u)$.
All actual response steps on these promised runs flip exactly one bit;
ERROR's typed self-loops hold.

Proof. Apply [FIB continuation IV, Theorem 51.2][SLHC14-LIFT] to the
whole $Q_I$, not merely its reachable part. Here the theorem's parameter
$r$ is $k$. Label $z$ by the $k$-bit vector
$a(z)=z\mathbin\oplus z_{\rm init}$, so the common initial word is
$0^{\ell_0}$. All syndrome labels are used, and the installed set is
exactly $J(\{0,1\}^{m_0})$. The theorem gives $f_0$ aliases per pattern,
$2^kf_0=M_0$ words and width $2m_0-1=\ell_0$. No other ambient
no-$11$ word is installed. Multiplying the complete input row counts of
Definition 14.1 by $f_0$ gives the table above; the typed-entry count is
four per Read plus one per Update, with none for Halt.

The input table satisfies the theorem's genuine-controller premise:
all instruction payloads are installed functions of $z$, each transition
uses only $z$ and its actual typed response, and Read and Update are the
original total native operations on the same tree. The common initial
$z_{\rm init}$ was specified in Construction 11.5. Lemma 11.3 supplies
the reached-node and certified-image invariant for every actual trial;
Construction 11.4 supplies actual active alignment before those trials.
Consequently every promised run follows the intended valid rows and
terminates with the proved original parity. These are the hypotheses
supplying success and termination; the redundant encoding supplies neither
an image certificate nor an independent termination argument.

Theorem 51.2 now transfers the complete typed table and exact execution.
Every actual nonhalt transition changes its logical pattern: GUARD changes
mode; POLL changes to UPDATE or initial VALUE; UPDATE changes to POLL;
a VALUE branch changes path length or candidate index; a VALUE leaf changes
the next path or enters a canonical halt. The path and candidate bounds
exclude ERROR on those runs. The theorem's bit-change identity therefore
gives one physical flip per actual primitive. It also copies the invalid
root-Read-to-ERROR rows exactly, while ERROR's four self-transitions hold.
There is no claim of successful termination from those unpromised entries.
All syndrome labels and the projection in the theorem are proof-side table
specifications, not an external decoder or runtime PC. $\square$

**Corollary 14.3 (one controller's exact native resource witness).** For
one fixed regime let $C^I_{h,T}$ denote the complete intermediate table
and let $\widehat C_{h,T}$ be Theorem 14.2's realization. On each same
allowed $(u,t)$,

$$
Q_{\widehat C}(u,t)=Q_I(u,t),\qquad
U_{\widehat C}(u,t)=U_I(u,t),\qquad
b_{\widehat C}(u,t)=Q_I(u,t)+U_I(u,t).
\tag{SLHC.14.3}
$$

Every actual ordered literal and reply is unchanged. In particular,
decoder guards and second Reads remain separate paid calls even when their
addresses coincide. Polling includes every absent reply before an Update
and the final $\alpha$ reply. All counts stop at first Halt.
The following bounds hold simultaneously for this one realization in each
row, with $P,A_*$ as in §11.1:

| Original regime | Exact or bounded calls | Submitted literal bounds | Complete width and installed words |
| --- | --- | --- | --- |
| $T=0$, every $h$ | $Q=2h-1$, $U=0$ | $P=h-1$, $A\le(2h-1)(h-1)$ | $\ell_0$, $M_0$, with $e=0$ |
| Static, even $h$, $T\ge1$ | $U=0$, $Q\le(T+1)(4h-2)=H$ | $P=h-1+\lceil T/2\rceil$, $A\le HP$ | $\ell_0$, $M_0$, with $e=\lambda(T+1)$ |
| Active, even $h$, $T\ge1$ | $U=B-t-\kappa(u)$, $Q\le U+1+2h(4h-2)$ | $P=h-1+B/2$, $A\le(B+1)B/2+2h(4h-2)P$ | $\ell_0$, $M_0$, with $e=\lambda(2h)$ |

Here $1\le U\le B$ in the active row, so $Q+U\le H$. To give the
sourcewise quantities behind these uniform bounds, let $\mathcal N(u,t)$
be the consecutive candidate offsets actually tried by the intermediate
table up to its first successful trial. For candidate $N$, let
$\mathcal P_N$ be its ordered list of visited virtual addresses, including
the cutoff branch when that trial fails, and put

$$
v_N=|\mathcal P_N|,\qquad d_N=\sum_{p\in\mathcal P_N}|p|.
$$

These lists are proof-side descriptions of actual trials, not an additional
archive available to the observer. The exact Read count and address-length
sum of that trial are

$$
q_N=\begin{cases}v_N,&N=0,\\2v_N-1,&N>0,\end{cases}
\qquad
a_N=\begin{cases}d_N,&N=0,\\
2d_N+Nv_N-\lfloor N/2\rfloor,&N>0.
\end{cases}
\tag{SLHC.14.4}
$$

In the static and zero-lag regimes,

$$
Q=\sum_{N\in\mathcal N(u,t)}q_N,\qquad
A=\sum_{N\in\mathcal N(u,t)}a_N,\qquad U=0.
\tag{SLHC.14.5}
$$

For active positive lag the exact quantities are

$$
\begin{aligned}
U&=B-t-\kappa(u),\\
Q&=U+1+\sum_{N\in\mathcal N(u,t)}q_N,\\
A&=(U+1)B/2+\sum_{N\in\mathcal N(u,t)}a_N.
\end{aligned}
\tag{SLHC.14.6}
$$

Let $b_\beta$ count the original $\beta$ leaves and let $F_0=0,F_1=1$.
The actual source node count at absolute epoch $s$ remains

$$
V_u(s)=2\bigl((h-b_\beta)F_{s+1}+b_\beta F_{s+2}\bigr)-1.
\tag{SLHC.14.7}
$$

The exact node peaks on these same runs are $2h-1$ for $T=0$,
$V_u(t)\le2hF_{T+2}-1$ for static entry, and
$V_u(\tau)\le2hF_{B+2}-1$ for active entry, where
$\tau=t+U=B-\kappa(u)$. The active source visits precisely the same
successive versions with epochs $t,t+1,\ldots,\tau$ as the input table.
The original target is still $\pi(u)$, not parity of an unrelated current
representative.

Proof. Equation (SLHC.14.3) and preservation of each ordered literal follow
from Theorem 14.2. At positive $N$, every visited nonroot node has its
accepted GUARD Read followed by its VALUE Read; the root has only VALUE.
There are $v_N-1$ such guards, giving $2v_N-1$ Reads. Their total length
is $d_N+(v_N-1)\lfloor N/2\rfloor$, since the guard at $p$ has length
$|p^-|+\lfloor N/2\rfloor+1=|p|+\lfloor N/2\rfloor$.
The values have total length $d_N+v_N\lceil N/2\rceil$. Adding proves
(SLHC.14.4), with both occurrences charged when the literals coincide.
At $N=0$ only the original virtual addresses are read.

Construction 11.4 has exactly $U+1$ polls of length $B/2$ and exactly
$U$ Updates, before the source becomes stationary for the trials. This
gives (SLHC.14.5)–(SLHC.14.6). The inherited $v_N\le2h-1$,
$|p|\le h-1$, at most $T+1$ static trials and at most $2h$ active
trials give the stated uniform bounds from §11.6 without its routing
factor. The direct $T=0$ traversal visits all $2h-1$ nodes once.
Its exact address sum is the sum of their depths.

The source versions are equal at every matched boundary. Formula
(SLHC.11.16), with the same original leaf counts, gives (SLHC.14.7).
Leaf count is nondecreasing under genuine Update, so the peak occurs at
the final visited epoch, giving the displayed exact source peaks. The
bounds for different coordinates need not be attained by one source;
all nevertheless hold for the one controller on every admitted source.
No coordinatewise optimization is used. $\square$

**Definition 14.4 (full table, initialization and service prices).**
Every installed Read literal, including those in unreachable rows, has
length at most the regime's $P$. Indeed the valid patterns have $s<h$;
static offsets satisfy $N\le T$ and active offsets $N\le B$. A VALUE
literal has length $s+\lceil N/2\rceil$, and a GUARD literal has length
$s+\lfloor N/2\rfloor$. POLL has length $B/2$, and invalid/ERROR
literals are empty. Thus the same $P$ used for runs also bounds the
whole installed menu.

Use §11.6's explicit row format with the new width and row counts. Set

$$
g_0=\lambda(P+1),\qquad q_0=\lambda(\ell_0+1),\qquad
S_0=M_0(\ell_0+2+g_0+P+4q_0).
\tag{SLHC.14.8}
$$

There are $M_0$ fixed-size records, each containing its complete
$\ell_0$-bit word key, a two-bit Read/Update/Halt0/Halt1 opcode, a
$g_0$-bit length, $P$ padded address bits and four $q_0$-bit hold/flip
slots. For Read, slots follow the fixed order
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$. Update uses the first
slot for $\star$ and zero padding in the other three. Halt has four
padding slots and no typed responses. Non-Read address fields are zero.
A zero response index denotes hold, and any nonzero used index denotes
one physical bit to flip, as in FIB IV Theorem 51.2. The exact number
of meaningful typed slots is the table count in Theorem 14.2; it must
not be confused with the $4M_0$ reserved slots in this representation.

The array has exactly $S_0$ bits under this fixed format. The common
initial word adds $\ell_0$ immutable bits; its being all zero does not
remove the initialization service or its price. The two fixed outputs
have $f_0$ installed rows apiece and are represented in the opcodes;
there is no additional output-bit column to charge twice. If the old
table's installed Read-literal sum is

$$
L_I=\sum_{z:\,I(z)\text{ is Read}(p_z)}|p_z|,
$$

the exact fully inlined unpadded address length is $f_0L_I$, and

$$
f_0L_I\le(2^k-2-u_0)f_0P.
\tag{SLHC.14.9}
$$

The entire distinct installed literal union is unchanged. The addresses
are already included in the $P$-bit fields of (SLHC.14.8). A shared
literal dictionary would have a different bill with its references,
framing and delivery separately counted; it is not used to reduce $S_0$.
Any additional format descriptors, indexing structure or physical selector
has its own installation cost. An explicit finite row specification does
not bound physical table-generation time, delivery time or lookup energy.

For the actual $n=Q_I(u,t)+U_I(u,t)$ calls, there are exactly $n+1$
instruction selections, $Q_I(u,t)$ full literal deliveries, $n$ immediate
response selections/writes and one fixed-bit output. There is one
initialization. Following (SLHC.11.15) and FIB IV (FIB.52.3), the cost
vector for this realization is

$$
\begin{aligned}
C={}&C_{\rm promise/auth}+C_{\rm source/entry}
 +C_{\rm compile/install}+C_{\rm init}\\
 &+\sum_{j=0}^{n-1}\bigl(
 C_{\rm select}(w_j)+C_{\rm deliver}(I(z_j))
 +C_{\rm primitive}(I(z_j),y_j)
 +C_{\rm response}(w_j,r_j)\bigr)\\
 &+C_{\rm select}(w_n)+C_{\rm output}(\pi(u)).
\end{aligned}
\tag{SLHC.14.10}
$$

Update has no address payload. Initializing a whole word is not counted
as one of the $n$ response flips. The growing source and any actual costs
of materializing its versions are distinct from observer width, installed
row bits and response writes. The conditional services must select and
write using this single word and the transient current response; they
cannot keep an external address cursor, decoded syndrome, phase, response
buffer or PC. Their prices are not equalized between realizations merely
because the native traces agree.

**Corollary 14.5 (compatible resource alternatives and original boundaries).**
For each positive regime of Definition 14.1, one explicit controller
simultaneously witnesses the width, complete table, initialization and
same-source event resources above. The two supplied realizations of the
same intermediate table have these different upper resource points:

| Realization | Complete word length | Installed words | Bound on actual native calls |
| --- | --- | --- | --- |
| Construction 11.6 with paid routing | $4k+15$ | $2^{2k+8}$ | $(2k+7)H$ |
| Theorem 14.2 preserving the intermediate trace | $2^{k+1}-3$ | $2^{2^k-1}$ | $H$ |

The second row has static $Q=O(h(T+1))$ and active
$Q+U=O(T+h^2)$ under the displayed native-call bounds. Its width is
exponential in $k$ and its installed-state count is doubly exponential
in $k$. For active finite-$T$ entry, $e=\lambda(2h)$, so these two
counts depend on $h$ alone, whereas the installed literal payload and
source-growth bounds still depend on $T$. There is no assertion of a
single installation for all lags.

Proof. All coordinates in each row come from that row's one complete
controller and its own execution proof. Construction 11.6 pays for added
source-preserving root Reads. Theorem 14.2 preserves every call of
Construction 11.5, so it has none of that routing overhead and bears the
new alias/table bill instead. The formulas for $H$, together with
$B=2\lceil(T+2h)/2\rceil$, give the two stated call orders. They do not
compare physical selection tariffs or prove any lower bound on calls,
width, installation or their joint cost.

The successful-family quantifier remains (SLHC.11.17): for each finite
$T$ in a positive regime there is a controller working on the whole
unknown-shape original family. The odd-$h$, positive-lag collision
obstruction and the unbounded-lag fixed-literal obstruction remain
exactly those of §11.7 and §9.7. Redundant aliases provide neither a new
source port nor an infinite literal menu, so they do not evade either
supplier's hypotheses. The fixed public skeleton of §12 is absent here;
its supplied-shape width minima are not substituted for this family's
width or installation count. $\square$

For fixed $h,T$ the original family is finite, so FIB II Corollary 47.2
already gives an actual-history existence realization. The resource point
here uses FIB IV's different bound in terms of the entire installed
intermediate table and its all-typed-row correspondence. The parity
algorithm, image licensing, alignment and source growth remain those of
§11; the Hamming and zero-interleaving ingredients have the literature
attribution in FIB IV Theorem 51.2. No Pareto or total
physical-cost optimum, and no synthesis from a merely closed candidate
family, follows from this construction.

[SLHC14-LIFT]: FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md#51-redundant-complete-words-with-the-original-call-trace

## 追加锚（本行以下为增补区）

## 15. Exact stationary zero-delay right-ray acquisition price

### 15.1. One unknown source and the acquisition coordinate

This section evaluates one instance of SLH's acquisition problem: the
entire future of one pure right address, acquired at epoch zero. Its new
content is the uniform closed-form all-address necessity argument in
§15.3. Ordered search, finite future codes, transport, continued use and
actual-image view conversion retain their existing suppliers. The
supporting operational application below fixes their precise scope.

**Definition 15.1 (source, installation and truthful port).** Fix a public
integer $d\ge0$. The unknown input is any $u\in\mathcal T$, with no size,
shape or orbit promise, where

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

These are ordered full binary trees: each branch has both children.
Addresses are arbitrary finite words in $L,R$, starting at the same root.
The actual call $\mathsf{Read}(p)$ returns $r_y(p)$ in
$\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$ on the current register
$y$. At the empty address it reports the root constructor. A nonempty
address below a leaf is absent; at a branch its first letter selects the
corresponding child. Every finite address is legal, without first reading
its prefixes. There is no query-depth restriction.

Before Start, an environment actually installs $u$ in one opaque bound
register. The observer has the same fixed root reference, public $d$,
program, readable program backing and literal/update rights on every
input. Its evidence and workspace start empty apart from source-independent
initialization. Source preparation, binding assurance, program installation
and rights are separately paid setup. They are supplied services, not an
authentication mechanism derived here. The observer cannot inspect a
source description, pointer layout, source size, seed, age, old cache,
private installer residue, service timing or any source-specific advice.
Only truthful actual Read replies supply source information during
acquisition. Computation and acquired working storage may be unrestricted,
but every allowed source must lead to finite termination.

The register remains $u$ throughout acquisition. There is no external
request ingress in that phase; only the controller's selected Reads and
local steps are enabled. Subsequent use retains the same register, root,
program and rights. No concurrent writer, replacement, re-rooting, hidden
update or revocation is admitted. Reads and updates complete synchronously
with their declared effects. This is a mathematical service contract;
source-busy implementation interiors are not added to its settled-cut
claims.

**Definition 15.2 (complete future and raw-call price).** The task is to
acquire an actually retained finite residual from which a common effective
procedure computes every term of

$$
F_d(u)=\bigl(r_{\rho^n u}(R^d)\bigr)_{n\ge0}
\tag{SLHC.15.1}
$$

without any later source observation. A residual is not supplied as an
input. All accessible source-dependent fields at handoff count as part
of it. Local finite computation may interpret the residual, but cannot
receive new source information. Let $n_A(u)$ count all actual acquisition
Read calls of a correct deterministic source-total procedure $A$, and set

$$
m_0(d)=\inf_A\sup_{u\in\mathcal T}n_A(u).
\tag{SLHC.15.2}
$$

Every call costs one, including a root call, an absent call and a repeated
call. An unbounded worst case has cost $+\infty$. Address letters,
navigation, local work, working and retained storage, setup, transmission,
cleanup and actual substitutions have separate costs. The infimum
optimizes only this raw-call coordinate.

**Theorem 15.3 (exact stationary right-ray price).** For every $d\ge0$,

$$
\boxed{\quad
m_0(d)=\min\{k\in\mathbb N:d+2\le2^k\}
      =\lceil\log_2(d+2)\rceil.
\quad}
\tag{SLHC.15.3}
$$

The lower bound permits arbitrary adaptive finite-address queries and
unrestricted acquired storage. One common deterministic controller attains
the bound on every finite tree, using only $R$-prefix queries of length
at most $d$, with no repeated address. It acquires the capped code
$a_d(u)$ defined below and retains it for the callable realization of
§15.5. In particular $d=0$ costs one actual root Read.

### 15.2. The supplied task code and its exact correspondence

**Supplier application 15.4 (right clock, future and boundary).** Put

$$
\kappa(\alpha)=0,\qquad \kappa(\beta)=1,\qquad
\kappa(\langle x,y\rangle)=2+\kappa(y),\qquad
C=2d+2,\qquad a_d(y)=\min(\kappa(y),C).
\tag{SLHC.15.4}
$$

SLH §2 and `DelayedOriginalReadout.right_clock_iterate` and
`right_clock_readout` supply, for all finite $y$ and $n,s\ge0$,

$$
\kappa(\rho^n y)=\kappa(y)+n,
\qquad
r_y(R^s)=
\begin{cases}
\mathsf{absent},&\kappa(y)<2s,\\
\alpha,&\kappa(y)=2s,\\
\beta,&\kappa(y)=2s+1,\\
\mathsf{branch},&\kappa(y)\ge2s+2.
\end{cases}
\tag{SLHC.15.5}
$$

Their one-step calculation is also immediate from the displayed source
rules: the leaf clocks become $1,2$, and a pair has clock
$2+\kappa(\rho y)=2+\kappa(y)+1$. The ray table follows by descending its
right child. These existing identities, not an assumed clock-to-geometry
correspondence, give the source-blind decoder

$$
E_d(a,n)=
\begin{cases}
\mathsf{absent},&a+n<2d,\\
\alpha,&a+n=2d,\\
\beta,&a+n=2d+1,\\
\mathsf{branch},&a+n\ge2d+2.
\end{cases}
\qquad F_d(y)(n)=E_d(a_d(y),n).
\tag{SLHC.15.6}
$$

Saturation is valid: if $a=C$, both sides are branch at every future
count. If $0\le a<a'\le C$, take $n=2d+1-a\ge0$. Then $E_d(a,n)=\beta$
and $E_d(a',n)=\mathsf{branch}$. Thus distinct attained codes have
distinct complete futures. A real update transports the current code by

$$
a_d(\rho y)=\min(a_d(y)+1,C).
\tag{SLHC.15.7}
$$

This is the single-ray instance of SLH §§35–39, with empty prior history,
$N=0$ and $Q=(R^d)$. For $d>0$, codes $a<2d$ correspond to
$\mathsf D_{2d-a}$, while $a=2d,2d+1,C$ correspond to
$\mathsf A,\mathsf B,\mathsf C$. For $d=0$ only the last three occur.
`FiniteMenu.Kernel.original_menu_kernel`, with menu `[rights d]` and
common iterate $n$, already classifies this same future equivalence; the
numbering here is not a new generic kernel.

Equivalently, $a_d(u)$ determines and is determined by the initial prefix
$V_{d+1}(u)=(r_u(R^j))_{0\le j\le d}$. If the first ray leaf has depth
$j\le d$ and colour bit $b$ ($\alpha$ means $0$, $\beta$ means $1$), the
code is $2j+b$. Otherwise $R^d$ is a branch and the code is $C$. This
prefix equivalence connects the task to SLH §13.2 with $M=0$ and finite
history-task list $((0,R^j))_{j=0}^d$: generic exact-price computability
and attainment were already supplied. What remains to prove here is the
closed value (SLHC.15.3), uniformly in $d$, against every address.

Present-only reading is a different task: one Read at $R^d$ supplies its
present literal. For $d\ge1$, both $\alpha$ and $\beta$ presently report
absent there, but their full futures differ by (SLHC.15.6). At $d=0$ the
present root constructor already determines its full future, and the
exact acquisition price remains one.

### 15.3. All-address necessity on actual finite sources

**Lemma 15.5 (comb families and query refinement).** Define actual finite
contexts and families by

$$
\begin{aligned}
&K_0(z)=z,\qquad K_{j+1}(z)=\langle\alpha,K_j(z)\rangle,
\qquad \gamma=\langle\alpha,\alpha\rangle,\\
&H_m=\{K_j(\alpha),K_j(\beta):0\le j<m\}\quad(m\ge0),\\
&G_t=\{K_j(\alpha),K_j(\beta):0\le j\le t\}
       \cup\{K_t(\gamma)\}\quad(t\ge0).
\end{aligned}
\tag{SLHC.15.8}
$$

$H_0$ is empty. On $H_m$, every nonconstant arbitrary-address query is
a function of a ray query $R^p$ with $p<m$. On $G_t$ the same holds with
$p\le t$. Moreover, embedding either family in a fixed $K_\ell[-]$
cannot make identification easier than identification of its hole content
with the same call budget.

Proof. Every address is either $R^p$ or uniquely $R^pLw$. Every actual
left child of these combs, including the extra terminal pair, is the leaf
$\alpha$. For $w\ne\varepsilon$ the reply is always absent. For
$w=\varepsilon$ it is $\alpha$ exactly when the reply at $R^p$ is branch,
and is absent otherwise. This supplies an explicit four-symbol
postprocessing, valid on the entire family simultaneously.

On $H_m$, all ray queries with $p\ge m$ are constant absent. On $G_t$,
$R^{t+1}$ returns $\alpha$ only on $K_t(\gamma)$ and absent on all other
members. It is the postprocessing that maps the branch reply at $R^t$
to $\alpha$ and all other replies to absent. All deeper ray queries are
constant absent. Together these cases exhaust every finite address,
including arbitrarily deep off-ray addresses; they are not a claim about
off-ray information on arbitrary unrestricted trees.

For a fixed prefix $K_\ell[-]$, a query at a strict ray ancestor of its
hole has constant reply branch. A query entering one of the fixed left
leaves has constant reply $\alpha$ or absent. A query that reaches the
hole is exactly a suffix query on its unknown content. Thus a simulator
can run any embedded-family procedure using locally supplied constant
replies and at most one actual suffix Read for each original call. It
returns the identified hole member from the identified complete tree.
The hole and every complete tree here are genuine finite sources, not
independently chosen answer coordinates.

Finally, replacing a query $q$ by a refining ray query $R^p$ preserves any
identification procedure on the family: feed the deterministic
postprocessed reply to its old continuation and ignore the extra
information. Each refined child is contained in an old reply child, so
correctness and the remaining read bound hold on every refined child.
A constant query can instead be supplied locally. These substitutions
are permitted for a restricted-family lower bound; they do not provide
free source observations to the original all-tree procedure. $\square$

**Lemma 15.6 (simultaneous paired capacities).** For each $k\ge0$:
identification of every member of $H_m$ within $k$ raw calls implies
$m+1\le2^k$; identification of every member of $G_t$ within $k$ raw calls
implies $t+2\le2^k$. Identification means a different terminal residual
for each member, or a source-free decoder that distinguishes them.

Proof. A deterministic procedure restricted to one finite family unfolds
into a finite reply tree. Each member's run is finite by source-totality,
so the union of these finitely many finite paths is finite. At a common
reply prefix the local state, computation and next address are the same:
only replies can introduce a source-dependent branch. Unrestricted
acquired memory does not change this fact. This justifies the decision
tree even when local computation has no uniform bound on all trees.

We induct simultaneously on $k$. At $k=0$, $H_0$ satisfies
$0+1=1\le2^0$; any nonempty $H_m$ contains both $\alpha$ and $\beta$.
Every $G_t$ contains at least three members. No zero-read source-blind
procedure identifies either nontrivial family. Thus both implications,
including the empty-family boundary, hold.

Let $k\ge1$. For a nontrivial family discard any initial constant
queries. An informative query must eventually occur, since a common
terminal output cannot identify distinct members. Refine that first
informative query by Lemma 15.5 to a canonical ray pivot. After this one
query each child has a correct identification continuation with at most
$k-1$ calls. Prior constant queries could only have consumed additional
budget, so dropping them cannot invalidate this upper bound.

On $H_m$, a pivot $0\le p<m$ has absent child $H_p$, singleton leaf
children $\{K_p(\alpha)\},\{K_p(\beta)\}$, and branch child
$K_{p+1}[H_{m-p-1}]$. The fixed-context simulation and induction give

$$
p+1\le2^{k-1},\qquad m-p\le2^{k-1}.
\tag{SLHC.15.9}
$$

An empty $H$ child satisfies the same inequality $1\le2^{k-1}$ without
a run. Adding the inequalities proves $m+1\le2^k$.

On $G_t$, for $p<t$ the absent child is $H_p$, the two leaf children are
singletons, and the branch child is $K_{p+1}[G_{t-p-1}]$. Therefore

$$
p+1\le2^{k-1},\qquad t-p+1\le2^{k-1},
\tag{SLHC.15.10}
$$

and adding gives $t+2\le2^k$. At the remaining pivot $p=t$, the absent
child is $H_t$ and the other three children are singletons: its alpha
leaf, beta leaf and terminal branch. Induction gives
$t+1\le2^{k-1}$, whence

$$
t+2\le2^{k-1}+1\le2^k.
\tag{SLHC.15.11}
$$

This includes $t=0$ and empty absent child. Lemma 15.5 has already
handled every noncanonical query. Each inductive restriction is a family
of complete actual sources; its embedding is simulated before applying
the residual-family hypothesis. No abstract interval is assumed to have
literal access equivalent to a different source family. $\square$

Proof of Theorem 15.3, lower bound. On $G_d$ the clocks are
$0,1,\ldots,2d+2$, since $\kappa(K_j(\lambda_b))=2j+b$ and
$\kappa(K_d(\gamma))=2d+2=C$. Thus all $2d+3$ members have different
$a_d$ and, by (SLHC.15.6), different required futures. Any globally
correct acquisition procedure identifies this actual finite family from
its retained residual. Lemma 15.6 forces $d+2\le2^k$ for any finite
uniform bound $k$. A procedure with infinite worst-case cost cannot
improve the asserted finite price. This proves necessity with repetitions,
root calls, absent calls, arbitrary depth and arbitrary adaptivity all
included. The pair structure strengthens the generic four-reply leaf
count; merely counting $2d+3$ answers would not prove this value.

### 15.4. A source-blind attaining controller

**Construction 15.7 (verified zero-delay ordered search).** Let
$h=\min\{k:d+2\le2^k\}$. Two modes use only integers and earlier replies.
In $G(\ell,t,k)$, the node at $R^\ell$ exists, $\ell+t=d$, and the task
is its ray endpoint through depth $d$, with any branch at $d$ collapsed
to code $C$. Maintain $t+2\le2^k$. In $H(\ell,m,k)$ the first ray leaf
is promised to have depth in $[\ell,\ell+m-1]$, and maintain
$m+1\le2^k$ and $\ell+m-1\le d$. Strict ancestors before $\ell$ are
branches in either mode. An empty $H$ promise is never reached on a
truthful input. Start at $G(0,d,h)$; root existence uses only nonemptiness.

In a nonempty $H$ mode, $k\ge1$. Put $p=\lfloor(m-1)/2\rfloor$ and
actually query $R^{\ell+p}$. A leaf of colour bit $b$ gives the answer
$2(\ell+p)+b$. An absent reply enters $H(\ell,p,k-1)$; a branch enters
$H(\ell+p+1,m-p-1,k-1)$. Their capacities obey

$$
p+1\le2^{k-1},\qquad m-p\le2^{k-1},
\tag{SLHC.15.12}
$$

because $m+1\le2^k$ and $p$ is the lower midpoint. A reply leading to
an empty leaf interval contradicts the current promise and therefore
cannot occur. This does not replace any legal absent-address Read by an
error.

In $G(\ell,t,k)$, again $k\ge1$. Put

$$
p=\min(t,2^{k-1}-1)
\tag{SLHC.15.13}
$$

and query $R^{\ell+p}$. A leaf gives $2(\ell+p)+b$. An absent reply
enters $H(\ell,p,k-1)$; its invariant follows from
$p+1\le2^{k-1}$. A branch at $p=t$ returns $C$. A branch at $p<t$
enters $G(\ell+p+1,t-p-1,k-1)$. In this last case
$p=2^{k-1}-1$, and

$$
(t-p-1)+2=(t+2)-(p+1)\le2^{k-1}.
\tag{SLHC.15.14}
$$

A branch ensures that the next right child really exists. An absent
reply means that the first leaf is strictly before the queried pivot;
a branch means it is strictly after it, unless the cap has been reached.
These implications follow directly from full-tree ray geometry on every
allowed input, without constraints on its left subtrees.

Every nonterminal step decreases $k$ and preserves the appropriate
promise. Neither a nonempty $H$ mode nor a $G$ mode can satisfy its
capacity invariant at $k=0$. Consequently every input terminates in at
most $h$ calls with the correct endpoint and $a_d(u)$. Each continuation
interval excludes its pivot; all later queries lie in that interval.
Thus no address repeats, and every queried depth is at most $d$. At
$d=0$ the start has $h=1,p=0$ and its one root Read distinguishes
$\alpha,\beta,\mathsf{branch}$. All choices depend only on public $d$
and actually received replies. This proves attainment and completes
Theorem 15.3. $\square$

The construction reuses the ordered-search method of SLH §6.3, with
prefix-length parameter $A=d+1$ and zero observation delay. That section
occurs within the $M\ge4$ contract of SLH Definition 6.1. Its stated
positive-delay theorem cannot be specialized to $M=0$: the odd-threshold
addresses can have negative exponents. Equations (SLHC.15.12)–(SLHC.15.14)
verify the zero-delay controller directly using only even ray thresholds;
no unavailable odd-threshold service is imported.

### 15.5. Actual acquired memory and callable continued use

**Operational application 15.8 (same-register requests).** Implement the
search by tail transitions. Its acquisition workspace contains mode,
$\ell$, remaining interval/cap parameter, $k$, pivot, one four-valued
reply, finite program control and an address buffer of length at most
$d$. All search indices are bounded by $d+2$, and $k\le h$; no stack,
cache or event archive is needed. A final answer field ranges through
$0,\ldots,C$, rather than through only $d+2$ values. Local arithmetic,
address construction and response handling are finite paid work.

On success actually write $a=a_d(u)$ into the retained predictor field,
clean up and release the search fields and buffer, and emit the constant
acknowledgement Ready. The settled observer is exactly
$\mathsf{Ready}(a)$ with the fixed backing, $d$, reference and rights.
No old output, hidden archive, source version counter or source-dependent
workspace remains accessible. Cleanup is part of this realization and
has its own bill; a different implementation retaining such fields must
include them in its memory observation. A fixed finite description of
this controller does not by itself prove a storage bound; the displayed
bounded field ranges do.

At Ready admit the four request tokens in the following complete table.
Here $y$ is the same actual source register and $a^+=\min(a+1,C)$.

| Request at $\mathsf{Ready}(a)$ | Completed output | Full source/controller successor |
| --- | --- | --- |
| Value | $E_d(a,0)$, typed as a derived value | $(y,\mathsf{Ready}(a))$ |
| Advance | Advanced | $(\rho y,\mathsf{Ready}(a^+))$ |
| Halt | Halted | $(y,\mathsf{Halted}(a))$ |
| Invalid | Error(BadRequest) | $(y,\mathsf{Ready}(a))$ |

Invalid is a declared input token representing a complete bad request,
not an unbounded malformed frame parser. There are no other admitted
requests. At $\mathsf{Halted}(a)$ every request is disabled: it has no
executed event, completed rejection or successor. Acquisition admits no
external token. Under the truthful synchronous contract there are no
other runtime errors. Nonadmission is not an Error event. No transition
restarts Halt or replaces the source by a representative tree.

Advance executes and pays for one real synchronous $\rho$ before its
acknowledgement and code update. Value performs no source observation.
Induction on every finite admitted request sequence, using
(SLHC.15.7), maintains

$$
y=\rho^n u,\qquad a=a_d(y),
\tag{SLHC.15.15}
$$

where $n$ is the actual number of completed Advances, a proof coordinate
rather than a retained unbounded counter. Value therefore returns the
current target correctly, even after any finite number of real updates.
The same induction applies to a coupled adaptive external client starting
in the same state and choosing from these outputs. That client's own
state and journal are outside this observer; including them internally
would enlarge the memory target. This is a concrete application of
SLH §§38 and 44's supplied continuation methods, not a new generic use
or replay theorem. A computed Value is not a raw Read or a newly
manufactured historical event.

### 15.6. Independent readouts, recovery domain and dynamics

**Definition 15.9 (four observations on the same actual process).** Fix
the common installation, backing and root. Let $D_0$ be all actual first
Ready cuts of Construction 15.7, before any external request. Let $D$
contain the settled Ready/Halted cuts after acquisition and a finite
admitted request sequence. Both domains range over all initial finite
$u$. Acquisition, cleanup and update interiors are outside these domains.
An observation compares readout values; it does not reconstruct hidden
off-ray parts of the joint source/controller configuration.

Define each view before providing recovery maps:

- $S$ is the actual oriented tagged current ray path from the root to
  depth $d$, stopping at its first leaf if earlier, together with the
  settled Ready/Halted phase. It records actual parent/right incidence
  and constructor tags on this restricted spatial path, not sibling
  subtrees or an event history.
- $B$ is the terminal boundary of that exploration: the first leaf
  $R^j$ and its colour for $j\le d$, or the capped branch $R^d$ when no
  leaf occurs through $d$, together with phase. It is a geometric
  stopping boundary for the ray exploration, not the whole tree's leaf
  frontier.
- $T$ is the chronologically indexed word of actual completed
  acquisition Read(address,reply) events, the constant Ready-return
  event, and the subsequent actually serviced request/output events
  through the cut. One completed event is one unit of this declared
  macro-event clock. Local CPU steps, service duration and source setup
  are not events of this clock and retain separate costs. This labelled
  chronological readout is a function of the actual execution prefix,
  not a retained archive secretly appended to memory.
- $M$ is all accessible settled observer memory: phase and retained
  $a$, together with the fixed public program, $d$, root reference and
  rights backing specified in §15.5. It exposes the installed predictor
  and actual callable binding. It does not expose the opaque source
  except through the declared operations.

**Proposition 15.10 (recovery and its exact limits).** On $D$, $S,B,M$
mutually determine one another; $T$ determines each of them. On $D_0$
all four determine one another, and all routes between their actual
images agree. On $D$, the three current-view conversions and the fold
from $T$ commute with each admitted request, its entire output/error
and its successor readout. Reverse recovery of $T$ on all $D$ is false.

Proof. Taking the last position of $S$ gives $B$. Restoring branch
ancestors before the endpoint gives $S$ from $B$. A leaf endpoint
$(R^j,\lambda_b)$ gives $a=2j+b$, and a capped branch gives $a=C$.
Conversely every $a<C$ uniquely gives $j=\lfloor a/2\rfloor$ and
$b=a\bmod2$, while $a=C$ gives the cap. Preserve phase and attach the
common backing to obtain exactly $M$. These inverses concern the actual
ray and installed memory values, not an arbitrarily completed whole
source or newly issued rights.

On $D_0$, the code determines every possible acquisition query reply:
for any $0\le j\le d$, the clock table at $2j,2j+1$ is unchanged by
capping at $C=2d+2$. Run the fixed controller on these determined replies.
By induction on its selected calls it produces exactly the actual next
address, reply and transition, then the same constant Ready return.
This is a finite computation of the chronological word's value; the
actual word has already occurred in this specified acquisition. Conversely
fold its actual replies through that controller to obtain its returned
$a$. Thus $T$ and $a$ determine one another on $D_0$. Together with the
explicit endpoint inverses, every route returns the same actual value.
This specializes the prefix-boundary and trace-faithfulness methods of
SLH §§41 and 43. Pure $R$ has no left-edge first-leaf collision.

On $D$, fold the acquisition prefix to its first code and then fold the
serviced events through the table in §15.5. This gives exactly the
current phase and $a$, hence $M,S,B$. For dynamics, an alpha endpoint
becomes beta at the same position. A beta endpoint at depth $j<d$
becomes an alpha endpoint at $j+1$; at depth $d$ it becomes the cap.
A cap remains a cap. These actual geometric changes give exactly
$a\mapsto\min(a+1,C)$. Value and Invalid preserve the three current
views; Halt changes their phase. Outputs and admission are the displayed
functions of phase and $a$. Appending the actual event to $T$ and folding
therefore agrees with updating its recovered current views. Induction
gives compatibility for every finite legal request word.

At Ready, equal codes are exactly equivalence for this continuation
interface. Distinct $a<a'$ are separated by the common word of
$2d+1-a$ Advances followed by Value, which gives beta versus branch.
Ready and Halted differ in admission. All Halted cuts, however, have
the same empty continuation behavior, even when their retained codes
and geometric views differ. The specified retained distinctions at Halt
are sufficient and redundant, not the minimal continuation kernel.

Finally append one Value to any actual Ready run. It preserves
$y,S,B,M$ and adds one real serviced event to $T$. Therefore those
current views cannot recover chronological $T$ throughout $D$.
$D_0$ is not closed under requests; its four-way equivalence is a
restriction to actual first-Ready cuts. $\square$

A scalar duration does not replace the labelled $T$: at $d=0$ the
sources $\alpha,\beta,\gamma$ each take one Read and one Ready return,
but give three different spatial endpoints, boundaries and codes. Nor
is task recovery full-source recovery. For every $d$, the sources
$\langle\alpha,\alpha\rangle$ and $\langle\beta,\alpha\rangle$ have
clock $2$, identical current capped rays, futures and acquisition traces,
but different replies at $L$. An arbitrary later address interface
would need additional acquisition and retention.

### 15.7. Separate resources and the certified delayed comparison

Let $q=n_A(u)\le h$ for Construction 15.7. Its submitted address letters
sum to at most $dq\le dh$, and its four-symbol replies have a fixed
encoding of at most $2q$ bits. The bounded search fields use
$O(\log(d+2))$ bits besides the length-$d$ address buffer and the fixed
backing; a direct implementation suffices. These are abstract storage
and transmission bounds, not an assertion that locating a deep address
costs one physical step. A retained predictor field can use
$\lceil\log_2(2d+3)\rceil$ bits, plus phase and the separately priced
backing, reference and rights. The $2d+3$ required first-Ready source
distinctions and their conditional code width are applications of SLH
§§8.2 and 39.2, not a new complete-memory optimum. Halt retains $a$
and is not minimal for its empty task.

One run's complete bill has the following distinct terms:

$$
\begin{aligned}
\mathfrak C={}&C_{\rm source/setup/binding}+C_{\rm program/rights/install}
 +C_{\rm init}+C_{\rm acquisition\ local/workspace}\\
&+\sum_{i=1}^{q}\bigl(C_{\rm address\ generation/transmission}(p_i)
 +C_{\rm navigation}(p_i,y)+C_{\rm raw\ Read}(p_i,y)
 +C_{\rm response}(i)\bigr)\\
&+C_{\rm retain/cleanup}
 +\sum_{\text{serviced requests }e}C_{\rm local/input/output}(e)
 +\sum_{\text{actual Advances }e}C_{\rho}(y_e)
 +C_{\rm continuing\ retention}.
\end{aligned}
\tag{SLHC.15.16}
$$

Only the number of raw Read summands in the acquisition sum is minimized
by Theorem 15.3. Value has decoding/output work and zero new source
observations. Every Advance pays the actual source rewrite, its material
and local predictor update. Halt and Invalid pay their processing and
output. Retaining or materializing an event archive adds its own storage,
access and serialization bill; the mathematical $T$ readout does not
supply one. The initial source has unrestricted off-ray size and can grow
without bound under continued substitution, even when the predictor
saturates. No bound on total apparatus memory or physical resource use
follows from its bounded predictor field.

**Corollary 15.11 (one-read difference under a different paid epoch).**
For the same original task $F_d(u)$, SLH Theorem 6.2 at its actual
certified delayed epoch $M\ge4$, with prefix length $A=d+1$, gives the
already supplied price

$$
Q_{d+1}(M)=\left\lceil\log_2\frac{2d+5}{3}\right\rceil.
\tag{SLHC.15.17}
$$

For $d=2^r-1$ and $r\ge2$, this is $r$, whereas $m_0(d)=r+1$.

Proof. Its original target $V_{d+1}(u)$ is equivalent to $a_d(u)$ and
$F_d(u)$ by §15.2. For these $d$,

$$
2^{r-1}<\frac{2^{r+1}+3}{3}\le2^r,
\qquad
2^r<d+2=2^r+1\le2^{r+1}.
$$

The two ceilings give the claim. $\square$

The delayed reads occur on the same original source's actual
$\rho^M u$, stationary during those reads, with certified $M$ and the
supplier's own full all-address contract. Reaching that epoch requires
$M$ real updates and their source growth and certification costs. Its
attaining addresses have the separate length bound
$d+1+\lfloor M/2\rfloor$. This corollary supplies no new delayed
capability, free waiting, total-work advantage or resource dominance.
It is a consequence of the new stationary evaluation and the existing
delayed theorem, with the original task held fixed.

### 15.8. Source ownership, attribution and remaining boundaries

The appropriate owner is this SLH continuation: the source, literal
interface and exact-price question are those of SLH, while this section
has no complete-word, one-bit-write or parity installation promise.
The following parameter correspondences limit what is reused.

| Source supplier | Correspondence and limit |
| --- | --- |
| SLH §§1–2, 6.3 | All finite trees, total four-valued address port, right-clock table and mature ordered search. The zero-delay specialization is verified in §15.4, without applying the $M\ge4$ theorem at zero. |
| SLH §§10–13, especially 13.2; §§69.1–69.4 | Effective finite-game exact price and attainment already exist. Here $M=0$, $F=((0,R^j))_{j=0}^d$. Section 69's more general complete acquired partition fibre is credited, not assumed to be present at this empty-evidence entrance. |
| SLH §§35–44 | $H=\varnothing,N=0,Q=(R^d)$; later current-code transport uses actual Advances. Finite future code, boundary, exact retained distinction, canonical prefix trace and paid use are supporting applications. The new theorem evaluates the pure-right case left between the bounds of §§37.2 and 40.3. |
| `ActualTreeReadoutAcquisition` and its owning Scribe | Source `.of true/.of false/.mul` means alpha/beta/pair; address `false/true` means left/right. Its `Policy/Strategy` has common empty history and pointwise finite correctness, but its original output is third-image membership and `paid` counts distinct addresses. Neither output nor metric is renamed into ours. |
| `DelayedOriginalReadout` and its owning Scribe | `rightClock` is $\kappa$, `rights d` is $R^d$; `right_clock_iterate` takes $N=n$, and `right_clock_readout` takes $s=d$. Its private `clock_step` supplies the one-step calculation. `original_decoder_service` recovers one historical literal with its supplied epoch, not the entire future or this minimum. |
| `FiniteMenu/Kernel` and its owning Scribe | `original_menu_kernel` takes menu `[rights d]` and common count $n$. Its `Same`, branch bounds and private `kernel_aux` prove future equivalence, without acquiring the unknown code or pricing its reads. |
| `FiniteMenu/NativeStationaryIntervalResources` and its owning Scribe | Its `Identifies/native_interval_capacity` recover numeric age $n$ from one orbit $T(n)=\rho^n\alpha$, with public $L\le n\le U$. Its private literal table, leaf-cell bounds and capacity induction use that orbit's geometry. That family is not the arbitrary original comb family (SLHC.15.8). Setting $n=\kappa(u)$ preserves the ray clock but not the whole literal-query geometry, so its $3\cdot2^k-2$ positive and zero-origin capacities cannot replace Lemma 15.6. |
| NCR §§1–2, 5; PVC §1; AA selected-Ready §27 and acquired-use §45; Atlas §6.3; PG and PR57 | Paid actual acquisition, callable backing, individual-view kernels, route agreement and continuation are existing substantive structures. NCR retains its closed program and actual clocks; PVC retains fixed-$H$ acquired entrance, authorized installation, unused-lane and serialization premises. AA retains its actual selected source/control. Their physical and historical services are not acquired here. Atlas requires each view's kernel and operations separately; §15.6 checks them on the declared domains. No new generic view, replay, tape backend or grant mechanism is claimed. |

The complete SLH original used for these correspondences is its source
at `ead132fb284340a8b3a70b957a974196f85fecc3`. The four named D5 modules
and owning Scribes above are read at
`718f48862606f2a12a01bf0349a23ee2521010b0`; an identical cached blob's
directory name does not change that revision binding. NCR, AA and Atlas
use their supplied `ead132fb` originals; PVC uses its separately bound
`718f4886` body and preserves its own historical dependency revision
`82c9eb9c1462af91333b7038a93488c8b9b8bdc7`. These references identify
source content, not a claim of a new compilation or transitive audit.

For primary classical context, Nowak, *The Geometry of Generalized Binary
Search*, [arXiv:0910.4397v5](https://arxiv.org/abs/0910.4397v5), studies
binary hypothesis splitting and conditions for logarithmic complexity.
Chrobak, Golin, Munro and Young, *A Simple Algorithm for Optimal Search
Trees with Two-Way Comparisons*,
[arXiv:2103.01084v3](https://arxiv.org/abs/2103.01084v3), studies optimal
two-way comparison trees including unsuccessful searches. Their primary
titles and abstracts support this bounded contextual attribution, not an
application of their structural theorems to our four-valued literal
geometry. SLH §9.2 supplies the classical deterministic decision-tree
and ordered-search references. Recursive splitting, query refinement,
static reply simulation and finite distinction counting are mature
methods, `literature-attested` at that level. The source-specific joint
$H/G$ capacity proof and its uniform evaluation (SLHC.15.3) are
`repo-derived`. This attribution asserts no worldwide priority,
exhaustive literature search or new general ordered-search theorem.

The result is ordinary mathematical exposition. Its source work uses the
formal-thinking-and-answer and theory-volume-template guidance with
external CLI mathematical authorship. It claims neither new Lean
certification, an independent review verdict, publication nor completion
of the sustained programme.

All model conditions remain substantive. This is a separately installed
fixed-$d$ task observer with truthful stationary acquisition and retained
use of held ports. It does not solve present-only reading by calling it
the complete future, recover the entire unknown source, accept arbitrary
later target addresses, or identify an unknown age on an atomic orbit.
Randomized or error-tolerant prices, concurrent or moving acquisition,
unknown bindings, revoked rights, busy-cut inversion, physical duration,
hardware implementation, total resource optima and unrestricted
observer/client histories require separate results.

The first-Ready correspondence does not recover exact old chronology
at all later cuts, lost caches, old controls or an uncharged archive.
The original fixed-$G_{gc}$/original-$Q$, parked-consumer,
unchanged-initialization, unavailable-access and unidentified-$R2$
obligations retain their original scope and remain unresolved by this
unit. No bridge to those apparatuses or universal alpha/beta reduction
has been proved. The full search for a parsimonious common relation
structure expressing space, time, boundary and memory remains open;
this exact deterministic raw-call price is one bounded contribution.

## 追加锚（本行以下为增补区）

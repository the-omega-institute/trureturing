# Recursive relational observation: native selectors and common extensions

> **Volume contract.** This is ordinary mathematical reference input, with
> definitions, proofs and bounded exact checks. It uses the `generic-v1`
> heading and claim conventions. Published bytes and append anchors are
> immutable; additions begin with a numbered heading after the last anchor
> and end with a new anchor. The mathematical statements here have no
> Lean-kernel verification claim.

## 1. The original stationary source and complete paid export

**Definition 1.1 (source, action and observation).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\quad h(\alpha)=h(\beta)=0,
\quad h(\langle x,y\rangle)=1+\max\{h(x),h(y)\}.
$$

Pairing is free and ordered. Every finite word over $L,R$, including
$\varepsilon$, is a legal original-root literal. Its reply $r_t(a)$
lies in $\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$:
the first three describe the reached constructor, and traversal beyond
a leaf returns absent. Set

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

For every public integer $D\ge1$ use exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
W_D=\{q:|q|\le D-1\},\qquad
\mathcal P_D=\{Rq:q\in W_D\}.                         \tag{SCE.1}
$$

One actual initial $t$ remains stationary during all acquisition.
The iterates $\rho^kt$ describe predicted readouts. There is no subtree,
equality, source-identity, age, reset, copying, navigation or advice port.

**Assumption 1.2 (unchanged late-target contract).** A single
deterministic effective source-blind preparation, depending on $D$ and
common source-independent installed tables but not on the later target,
terminates on every $t\in\mathcal F_D$. It acquires source dependence
only through charged literal Reads and exports $E(t)$. Its complete
attained alphabet includes every accessible surviving source distinction:
selectors, control, buffers, operands, lengths, allocation, handles,
counters and accessible timing. Every other accessible field is a
function of this name and public data. A separately paid handoff and
access-isolation service removes all other preparation dependence,
including the transcript, and supplies lawful reader entry.

Only after export a public source-independent $p\in\mathcal P_D$
arrives. A common deterministic effective reader uses $E(t),D,p$ and
installed tables to choose zero Reads or one fresh Read of the same
stationary source at any finite original-root word. This choice precedes
the reply and every supplied count. Its final predictor $Z$ satisfies

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad\text{for every }t\in\mathcal F_D,\ p\in\mathcal P_D,
\text{ and authentic subsequently supplied }k\ge0,             \tag{SCE.2}
$$

without further Reads. Define $M_1(D)=\min|E[\mathcal F_D]|$ over
these jointly correct procedures. Only this complete retained alphabet
is optimized. Acquisition, work/control, installed tables, workspace,
predictor size, address lengths and letters, count representation,
handoff, isolation, entry, continuity, authentication and physical time
are separate resources. The services are premises, not physical
operations inferred from tree algebra. This is the full [FMR, §1][FMR]
contract, including all variable shapes and arbitrary off-target words.

**Convention 1.3 (credited exact temporal factor).** Use [AAR,
Definition 12.2, Theorem 12.3 and Proposition 13.3][AAR]. Put
$s(r)=\#L(r)+2\#R(r)$ and $e(\alpha)=0,e(\beta)=1$. A branch
endpoint has $\Gamma_q(u)=(0,0)$. Otherwise let the first original
leaf along $q$ be $\ell$ at $a$, with $q=ar$. Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}                                                   \tag{SCE.3}
$$

On attained factors the supplied decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}                                                   \tag{SCE.4}
$$

Here $c=1$ implies $b\ge2$. This equals $r_{\rho^ku}(q)$ for
every $k\ge0$. Conversely the trajectory determines $b$ as its first
branch count and $c$ by the presence of an alpha stage. Thus equality
of factors is exactly equality of full trajectories, including initially
absent targets. In the wrapper the factor at $Rq$ equals $\Gamma_q(v)$,
and its first coordinate is at most $2D$.

**Definition 1.4 (canonical sources and unrestricted joint donors).** Set

$$
C_0=\langle\alpha,\alpha\rangle,\quad S_1=\{\alpha,\beta,C_0\},
\quad S_{d+1}=\{\alpha,\beta\}\sqcup
                 \{\langle x,y\rangle:x,y\in S_d\},
\quad N_d=|S_d|.                                               \tag{SCE.5}
$$

In particular $N_1=3$ and $N_{d+1}=2+N_d^2$. Write
$G_q=\Gamma_q(S_d)$ when $d$ is fixed. A nonempty
$B\subseteq S_d^n$ is fully admissible if each target $(i,q)$,
$i\in[n],q\in W_d$, is constant on $B$ or has a donor
$(j,a)\in[n]\times W_d$ and a total decoder
$\delta:\mathcal A\to G_q$ such that

$$
\Gamma_q(x_i)=\delta(r_{x_j}(a))\qquad(x\in B).                 \tag{SCE.6}
$$

Every donor, self donor, cycle and correlation is permitted. Choices may
differ between targets. A complete template chooses one such equation
for every target; its full solution set may be empty. These are the
credited [NPC, Definition 2.2][NPC] competitors. [FMR, Lemma 2.2][FMR]
simulates every finite canonical word by one boundary reply in the same
block or a constant. Thus the donor notation does not remove arbitrary
native experiments.

For reference, $K_d(n)$ is the least number of nonempty admissible
subsets covering $S_d^n$. Its fractional counterpart $Z_d(n)$ minimizes
$\sum_B z_B$ over nonnegative coefficients satisfying
$\sum_{B\ni x}z_B\ge1$ for every $x\in S_d^n$. For a nonnegative
whole-block weight $w:S_d\to[0,\infty)$ define

$$
A_n(w)=\max_{\Theta}\sum_{x\in C_\Theta}\prod_{i=1}^nw(x_i),
\qquad \beta_d(w)=\sup_{n\ge1}A_n(w)^{1/n}.
$$

Here $\Theta$ ranges over full complete templates. The credited FMR
and NPC relations give

$$
\sigma_d=\lim_{n\to\infty}\frac{\log_2K_d(n)}n
        =\inf_{n\ge1}\frac{\log_2K_d(n)}n,\qquad
\lambda=\lim_{D\to\infty}2^{-D}\log_2M_1(D)
       =\sup_{d\ge1}2^{-d}\sigma_d.
$$

The maximum defining $A_n$ exists because every fixed-size template
family is finite. No finite size cutoff for its all-length supremum is
assumed. Write $\Delta(S_d)$ for the probability simplex on $S_d$.

## 2. A unique least generator among unary target selections

**Definition 2.1 (the precise minimization class).** A unary target
generator is a subset $J\subseteq W_d$ such that for every $q\in W_d$
there are an $r\in J$ and a source-independent function
$\theta_{q,r}:G_r\to G_q$ with
$\Gamma_q=\theta_{q,r}\circ\Gamma_r$ on all $S_d$. Define

$$
J_1=\{\varepsilon\},\qquad
J_d=\{q:|q|=d-1\}\cup
     \{q:1\le|q|<d-1,\ q\text{ ends in }L\}\quad(d\ge2).
                                                               \tag{SCE.7}
$$

This minimizes a subset of the existing target coordinates, with one
coordinate allowed per reconstruction. It does not minimize arbitrary
encodings of the joint vector, arbitrary relational descriptions, or
multi-coordinate reconstruction rules.

**Theorem 2.2 (positive reconstruction of every omitted coordinate).**
For every $d\ge1$, every actual $v$ with $h(v)\le d$, and every
$q\in W_d\setminus J_d$,

$$
\Gamma_q(v)=\Psi(\Gamma_{qL}(v)),                              \tag{SCE.8}
$$

where the public function needed on attained inputs is

$$
\begin{aligned}
\Psi(0,0)=\Psi(1,0)=\Psi(2,1)&=(0,0),\\
\Psi(2,0)&=(1,0),\\
\Psi(3,0)&=(2,1),\\
\Psi(b,0)&=(b-1,1)\qquad(b\ge4).
\end{aligned}                                                 \tag{SCE.9}
$$

In particular $qL\in J_d$, and its attained range is contained in
the displayed domain of $\Psi$.

Proof. An omitted word is either $\varepsilon$ or an R-ending word
of length at most $d-2$. Its L-child is in $W_d$ and is either at
maximum depth or L-ending, so belongs to $J_d$.

If $q$ is branch, its L-child is branch, beta or alpha. Their factors
are $(0,0),(1,0),(2,1)$, respectively, and the desired parent factor
is $(0,0)$. If $q$ is a beta leaf, its L-extension has factor $(2,0)$;
if it is an alpha leaf that factor is $(3,0)$. Their parent factors are
$(1,0)$ and $(2,1)$, giving the next two lines.

If $q$ is absent, it is nonempty and ends in R. Its residual after the
first blocking leaf therefore ends in R and has weight at least two.
Equation (SCE.3) gives $\Gamma_q=(b,1)$ with $b\ge3$. Appending L
adds one to the first coordinate and makes the second zero, giving
$\Gamma_{qL}=(b+1,0)$. The last line of (SCE.9) applies. These
exhaust all actual shapes. The argument uses the first original leaf,
including when the target itself is absent. $\square$

**Theorem 2.3 (unique least unary generator).** For every $d\ge1$,
$J_d$ is a unary generator and every unary generator contains it.
Consequently it is the unique inclusion-minimal and unique
minimum-cardinality unary generator. The same statement holds when
the generator identities are required on every actual $v$ with
$h(v)\le d$, rather than only on $S_d$. Its cardinality is

$$
|J_1|=1,\qquad |J_d|=3\,2^{d-2}-1\quad(d\ge2).                \tag{SCE.10}
$$

Proof. Theorem 2.2 reconstructs omitted targets; retained targets use
the identity. To prove necessity, fix $q\in J_d$ and any distinct
$r\in W_d$. We exhibit two actual canonical trees with the same
$\Gamma_r$ and different $\Gamma_q$.

First suppose $r$ is a proper prefix of $q$. Make all strict ancestors
of $q$ branches, put alpha in every unused sibling, and vary the leaf
at $q$ between alpha and beta. At $r$ both factors are $(0,0)$;
at $q$ they are $(2,1)$ and $(1,0)$. If $q,r$ are incomparable,
make branches at the strict prefixes of their union, put a fixed alpha
leaf at $r$, and vary the leaf at $q$ in the same way. Now
$\Gamma_r$ is the fixed alpha factor. The remaining unused siblings
are alpha. All these path trees belong to $S_d$ because both word
lengths are at most $d-1$.

The remaining case is that $r$ strictly extends $q$. A maximum-depth
$q$ has no such extension in $W_d$. Otherwise (SCE.7) makes $q=aL$.
Use identical branch ancestors toward $a$ and alpha unused siblings.
In the first tree put beta at $a$; in the second put
$\langle\alpha,\alpha\rangle$ there. These trees belong to $S_d$.
At $q$ the factors are $(2,0)$ and $(2,1)$. Write $r=qz$ with
$z\ne\varepsilon$. In the first tree the residual is $Lz$ after
beta; in the second it is $z$ after alpha. Both $r$ factors are

$$
\bigl(s(z)+2,\mathbf1_{z\text{ ends in }R}\bigr).
$$

Thus no distinct target unary-generates $q$. At $d=1$ there is only
the root target, and the empty subset cannot generate it. Every
generator must therefore contain each member of $J_d$. For $d\ge2$
there are $2^{d-1}$ maximum-depth words and
$\sum_{l=1}^{d-2}2^{l-1}=2^{d-2}-1$ shorter nonempty L-ending words.
This proves the count and uniqueness. Theorem 2.2 supplies the generator
identities on the whole actual family, and all necessity witnesses
already belong to its canonical subfamily $S_d$, proving the stated
full-family version as well. $\square$

## 3. Exact requirements equivalence with the whole donor menu retained

**Definition 3.1 (reduced requirements).** Reduced admissibility asks
for (SCE.6) only at $(i,q)\in[n]\times J_d$. Its donors still range
over every $(j,a)\in[n]\times W_d$, with all the constant choices.
The source universe remains $S_d^n$. A reduced complete template
specifies one equation for every reduced target.

**Theorem 3.2 (unchanged relations, covers and all nonnegative masses).**
For every $d,n\ge1$ and every nonempty $B\subseteq S_d^n$, full and
reduced admissibility are equivalent, without changing $B$. Every
chosen reduced witness extends to omitted requirements with the same
donor and literal. The integral and fractional cover optima are
therefore identical. For every arbitrary nonnegative
$\omega:S_d^n\to[0,\infty)$, the maximum $\omega$-mass over full
complete-template solution sets equals that over reduced ones.

Proof. Full admissibility implies reduced admissibility by restriction.
For an omitted $q$, take the chosen witness at $(i,qL)$. If its factor
is constant, compose that constant with $\Psi$. Otherwise compose
its decoder with $\Psi$ and leave $(j,a)$ untouched. Equation
(SCE.8) proves the omitted equation on this very same $B$. No
projection, product replacement or independence assumption occurs.
Thus the admissible subsets, hence both cover families and optima,
are exactly the same.

For clarity the template mass statement has two directions. Deleting
omitted equations from a full template can enlarge its solution set,
so nonnegative mass cannot decrease. Hence the full maximum is at
most the reduced maximum. Conversely expand any reduced template by
the composed equations just described. Every reduced solution satisfies
them by (SCE.8), and a full solution still satisfies the original
reduced equations. Its solution set is exactly unchanged, proving the
opposite maximum inequality. Empty solution sets cause no exception.
Simply deleting equations from an arbitrary full template is not an
assertion of equality of that individual template's solution set.
$\square$

The weight $\omega$ may be fully correlated, or a product of arbitrary
nonnegative whole-block potentials. Every repeated reply still refers
to the same source coordinate and every original potential is used
once. In particular this theorem preserves the credited $K_d(n)$,
$Z_d(n)$, all-length product pressure, $\sigma_d$ and their original
rate consumer. It gives no numerical improvement to these quantities.

**Theorem 3.3 (same preparation, same complete code, one late Read).**
Fix $D\ge1$. Suppose a preparation satisfying Assumption 1.2 has a
correct reduced reader for all requests $Rq$, $q\in J_D$. There is
an effective full reader with that exact preparation and that exact
function $E:\mathcal F_D\to E[\mathcal F_D]$. On an omitted request
$Rq$ it makes precisely the reduced reader's zero-Read choice or its
chosen one arbitrary original-root Read for $RqL$. Preparation charges
and the complete attained alphabet are unchanged. Restriction supplies
the converse, so the reduced and original optima are equal.

Proof. A finite public table can turn the reduced reader's one reply
into its full requested factor. To establish this effectively without
supplying a fictitious authentic count, enumerate all finite explicit
trees in $\mathcal F_D$. On each, simulate the given terminating
preparation with locally computed replies. For each attained name and
reduced request, the deterministic reader's query choice before the
first Read depends only on that name, request and public data. Record
its zero-Read choice or word. Compute its reply on every enumerated
explicit tree and compute that tree's factor directly by (SCE.3).

For a fixed name, request and selected reply, all these factors agree.
Indeed equal inputs and reply give the same final predictor; correctness
for every subsequently supplied authentic count gives equal entire
trajectories, and Convention 1.3 gives equal factors. The zero-Read
case is the same argument without a reply. Thus the table is
well-defined; unattained replies receive arbitrary values. Enumeration
and all required simulations terminate because the family is finite
and the given procedures terminate on every actual source. Uniformly
in public $D$ this is an effective table-generation procedure, with
no efficiency claim and no unknown-source input.

At run time an omitted request chooses $RqL$, makes that reader's
identical query or zero-Read choice, uses the public table to obtain
$\Gamma_{qL}(v)$, and applies $\Psi$. Equation (SCE.8) gives the
desired $\Gamma_q(v)$. Equation (SCE.4) answers each authentic count
when it is subsequently supplied, with no further Read. Retained
requests use their original reader. Every query still acts on the
same actual stationary $t$ and may remain off-target or arbitrarily
long. No canonical replacement of $E$, additional acquired field,
reselected color, or preparation transcript is used. $\square$

**Convention 3.4 (paid attainment from a reduced cover).** If starting
instead from a finite reduced cover, expand its witnesses by Theorem
3.2 and use the credited [FMR, Theorems 2.3–2.5][FMR] construction.
It actually scans $Rq$, $q\in W_D$, including absent replies,
computes the canonical tree $\pi_D(v)$, and exports its first-cover
name. Sufficient charges on every original source are

$$
T_{\rm prep}=2^D-1,\qquad Q_{\rm prep}=D,\qquad
A_{\rm prep}=(D-1)2^D+1.                                    \tag{SCE.11}
$$

Only the counted complete name survives under the paid isolation
service. This is credited acquisition, not a free preassigned color.
The reduced requirements do not prune this acquired boundary or the
donor menu. Unlike Theorem 3.3, a construction from an arbitrary cover
is not an assertion that a previous encoder function is preserved.

## 4. One output retraction on one fixed actual-consistency promise

**Definition 4.1 (common source coordinates and total extensions).** Fix
$d,n\ge1$. For $I=[n]\times W_d$ use the ambient product
$X=\mathcal A^I$. The actual-coordinate map is

$$
c(x)_{(i,a)}=r_{x_i}(a),\qquad c:S_d^n\longrightarrow H_d^n.
                                                               \tag{SCE.12}
$$

Here $H_d$ consists of arrays with nonabsent root and parent-child
pairs in

$$
\{(\mathsf{branch},\alpha),(\mathsf{branch},\beta),
(\mathsf{branch},\mathsf{branch}),
(\alpha,\mathsf{absent}),(\beta,\mathsf{absent}),
(\mathsf{absent},\mathsf{absent})\}.
$$

[CBN, Theorem 2.2][CBN] proves that $c$ is a bijection. Thus no
independent choice is assigned to repeated coordinates. Fix any
nonempty $B\subseteq S_d^n$ and the one promise $\mathcal D=c(B)$;
the full actual promise $H_d^n$ is the case $B=S_d^n$.
Define $f_{\rm full}$ on this promise as the vector of all
$\Gamma_q(x_i)$ and $f_J$ as its $[n]\times J_d$ projection.
Their ambient output products are respectively

$$
Y=\prod_{i\in[n]}\prod_{q\in W_d}G_q,\qquad
Y_J=\prod_{i\in[n]}\prod_{q\in J_d}G_q.
$$

Let $\pi:Y\to Y_J$ be projection.
Define $L:Y_J\to Y$ by keeping the selected coordinates and setting
each omitted coordinate $(i,q)$ equal to $\Psi(y_{i,qL})$.
Theorem 2.2 implies $\Psi(G_{qL})\subseteq G_q$, so this is total.
Then

$$
\pi L=\mathrm{id}_{Y_J},\qquad
f_{\rm full}=Lf_J,\qquad f_J=\pi f_{\rm full}.                \tag{SCE.13}
$$

In particular $L$ is injective even on unrealizable output tuples,
and $L\pi:Y\to Y$ is idempotent and fixes the promised task.

For a total extension $H:X\to Y$ or $H:X\to Y_J$ and any coordinate
cut $A\subseteq I$, its response at an assignment $a\in\mathcal A^A$
is the function $b\mapsto H(a\sqcup b)$ on
$\mathcal A^{I\setminus A}$. Its capacity $\kappa_A(H)$ counts
distinct such functions, on the whole ambient product. Complementary
assignments are not separately assumed consistent or realizable.

**Theorem 4.2 (simultaneous common-extension consumer).** Fix any one
finite labelled Full tree $T$ whose leaves are exactly $I$, with the
disjoint sibling coordinate sets required by
`FixedTreeCommonExtension.Full`. On the same promise $\mathcal D$,
the full and reduced tasks have equal upward closures of their
common-total-extension capacity vectors at every original node of $T$.
For every coordinatewise monotone cost into a linearly ordered set,
their attained capacity minima and their attained fixed-tree protocol
minima are equal. The protocol reachable-vector families themselves
are equal. These assertions hold for arbitrary correlated $B$.

Proof. Given any total extension $H_J:X\to Y_J$ of $f_J$, use the
single extension $LH_J$ of $f_{\rm full}$. At every cut, two response
functions of $LH_J$ agree if and only if those of $H_J$ agree:
one direction is postcomposition, and the other applies injectivity
of $L$ pointwise. Hence

$$
\kappa_A(LH_J)=\kappa_A(H_J)\qquad\text{for every }A\subseteq I.
                                                               \tag{SCE.14}
$$

Conversely any total extension $H:X\to Y$ gives $\pi H$, extending
$f_J$, and postprocessing gives

$$
\kappa_A(\pi H)\le\kappa_A(H)\qquad\text{for every }A\subseteq I.
                                                               \tag{SCE.15}
$$

Equations (SCE.14) and (SCE.15) give the two upward-closure
inclusions, using one common extension simultaneously at every node.
No extensions are chosen independently at different cuts.

Now apply the credited exact
[`FixedTreeCommonExtension.result`][FTE]. Its coordinate index $I$
is finite, every coordinate alphabet is the finite nonempty
$\mathcal A$, $T$ is Full and has all coordinates as leaves, and
$\mathcal D$ is nonempty because $B$ is. Its task is $f_J$ or
$f_{\rm full}$ on that same promise. The supplier identifies each
task's protocol and extension upward closures and gives attained
monotone-cost minima. Combining it with (SCE.14)–(SCE.15) proves
the asserted equal minima.

There is also a direct equality of protocol vector families: keep all
leaf encoders, messages and internal mergers of any correct reduced
protocol and compose its final read map with $L$. Conversely compose
the full protocol's final read map with $\pi$. Equation (SCE.13)
proves correctness; every actual promised message remains identical
at every node. This proves both inclusions of those vector families.
$\square$

**Convention 4.3 (operational limits of this consumer).** The supplier's
`Implementation` receives each leaf coordinate and the full tuple of
child messages at a merger. Its final `read` is a decoder. These
mathematical inputs are not free literal observations on the original
source. Its `canonical` uses representative choice; its attained
capacity statement does not price source acquisition or installed
controller states. Theorem 3.3 is the separate same-code native
consumer: it preserves the single actual source, all original targets,
one selected literal, and the complete export. Theorem 4.2 does not
identify fixed-tree width or its root message with $M_1(D)$.

## 5. Separately priced pooling of all target answers

**Definition 5.1 (a stronger completion interface).** A pooled
completion starts after the complete export $E(t)$, receives neither
a target nor a count, and makes charged adaptive original-root Reads
of that same stationary $t$. It then outputs one complete state $Z$.
With no further Reads, $Z,D$ and public tables must answer every
$p\in\mathcal P_D$ and every authentic subsequently supplied
$k\ge0$. Its only acquired input at entry is $E(t)$; inaccessible
preparation transcripts remain inaccessible. Address choice, stopping
and local work are deterministic. All additional workspace and final
state distinctions are charged separately from the initial alphabet.
This changes the task by requiring a common acquired answer state
before the request is known.

**Theorem 5.2 (alphabet versus fresh-query obstruction).** For any
complete original code $E$ and any correct pooled completion, let

$$
B_e=\{x\in S_D:E(\langle\alpha,x\rangle)=e\}.
$$

For each nonempty canonical fiber let $q_e$ bound its fresh Read
count. If $m=|E[\mathcal F_D]|$ and $q$ is a common worst bound,
then

$$
|B_e|\le4^{q_e},\qquad
N_D\le\sum_{e:B_e\ne\varnothing}4^{q_e}\le m4^q,
\qquad
q\ge\max\!\left\{0,\left\lceil\log_4(N_D/m)\right\rceil\right\}.
                                                               \tag{SCE.16}
$$

These bounds allow arbitrary correlated fibers, unbounded submitted
address lengths, off-target queries and variable stopping.

Proof. The full target-factor vector separates $S_D$: its $k=0$
readouts give the whole $W_D$ reply array, which reconstructs the
canonical source by CBN Theorem 2.2. The selected vector also
separates, by Theorem 2.2. Therefore one pooled state cannot serve
two distinct canonical sources: some original target already has
different required replies at count zero.

Fix a name $e$. Each address and each stopping choice is a function
only of $e,D$, public data and preceding replies. There are four
possible replies per Read. A decision tree of depth at most $q_e$
has at most $4^{q_e}$ terminal transcripts, including early stops.
This follows inductively: a root stop gives one leaf; otherwise sum
the at most four subtree bounds $4^{q_e-1}$. Determinism makes the
final state identical for every source at one transcript. The
separation just proved permits at most one canonical source there,
giving the fiber bound. Addresses and their lengths cannot add source
information beyond that transcript because they are functions of its
prefix. Sum over the unchanged fibers and use their number at most
$m$. No preparation record is accessible in this argument. $\square$

**Corollary 5.3 (pooling has a different asymptotic memory rate).** Let
$M_{\rm pool,1}(D)$ minimize the complete pre-completion alphabet
for Definition 5.1 with at most one fresh Read. Then

$$
\lceil N_D/4\rceil\le M_{\rm pool,1}(D)\le N_D,
\qquad
\lim_{D\to\infty}2^{-D}\log_2M_{\rm pool,1}(D)=\chi,
\quad \chi:=\lim_{D\to\infty}2^{-D}\log_2N_D.                 \tag{SCE.17}
$$

For any pooled compiler preserving an optimal original alphabet
$M_1(D)$ and using at most $q(D)$ fresh Reads,

$$
\liminf_{D\to\infty}\frac{q(D)}{2^D}
\ge\frac{\chi-\lambda}{2}
>\frac{\log_2 123}{16}-\frac3{32}>0.                         \tag{SCE.18}
$$

Here $\lambda$ is the credited original rate. The constant $\chi$
is the full-boundary cardinality rate, distinct from both $\lambda$
and FMR's scaffold constant $\phi$.

Proof. The lower alphabet bound is (SCE.16). For the upper, the
credited paid scan (SCE.11) exports the entire canonical name, one
of $N_D$ possibilities. Its factor vector and all future target
readouts can then be computed with zero fresh Reads. This is the
existing full-menu passive endpoint, used only as an upper here.

Put $a_D=2^{-D}\log_2N_D$. The recursion in (SCE.5) gives

$$
a_{D+1}-a_D=2^{-D-1}\log_2(1+2/N_D^2)>0.
$$

Since $N_D\ge3$, these increments are bounded by the summable
sequence $2^{-D-1}\log_2(11/9)$. Thus $a_D$ has a finite limit
$\chi$. The two alphabet bounds differ in logarithm by at most two
bits, giving (SCE.17). Equation (SCE.16) for optimal original names
gives $2q(D)\ge\log_2N_D-\log_2M_1(D)$. Divide by $2^D$ and
use the credited existence of $\lambda$ from FMR Theorem 3.3.
Since $N_3=123$, monotonicity gives $\chi\ge\log_2 123/8$;
the credited [D3, Theorem 4.1][D3] gives $\lambda<3/16$.
This proves the strict middle inequality. Positivity follows already
from $123>8$. In particular $q(D)=o(2^D)$ is excluded for this
defined same-alphabet pooling mechanism. $\square$

## 6. Exact fresh Read counts on the credited depth-three code

**Convention 6.1 (the prescribed original encoder).** Reuse exactly
the four-name encoder of [D3, Theorem 2.3, (D3.23)–(D3.26)][D3],
credited there to LTR. If $\tau(x)=0$ at a leaf and $1$ at a branch,

$$
E_0(\langle\alpha,v\rangle)=
\begin{cases}
00,&v=\alpha,\\
11,&v=\beta,\\
\tau(x)\tau(y),&v=\langle x,y\rangle.
\end{cases}                                                   \tag{SCE.19}
$$

It is actually acquired by the three fixed original-root Reads
$R,RL,RR$, with maximum length two and five submitted letters.
Only its four complete names survive paid export. Its existing
one-request reader serves every original target with at most one
fresh literal, chosen before the count. These facts and $M_1(3)=4$
are credited inputs, not conclusions obtained from pooling.

Put $A=\alpha,B=\beta$ and
$\mathcal G=\{\langle x,y\rangle:x,y\in S_1\}$, of size nine.
The canonical fibers are precisely

$$
\begin{array}{c|c|r}
e&B_e&|B_e|\\\hline
00&\{A\}\cup\langle\{A,B\},\{A,B\}\rangle&5\\
01&\langle\{A,B\},\mathcal G\rangle&18\\
10&\langle\mathcal G,\{A,B\}\rangle&18\\
11&\{B\}\cup\langle\mathcal G,\mathcal G\rangle&82.
\end{array}                                                    \tag{SCE.20}
$$

**Theorem 6.2 (sharp completion costs for this same code).** Starting
with exactly $E_0$ and no preparation transcript, the minimum worst
fresh Read counts for pooled completion on names $00,01,10,11$ are,
respectively, $2,3,3,4$. These are minima over every deterministic
adaptive procedure with arbitrary finite original-root words on the
whole original family. Sufficient worst fresh letter counts are
$4,8,8,12$ respectively, with maximum fresh address lengths
$2,3,3,3$; no letter optimum is asserted.

Proof of necessity. Apply Theorem 5.2 separately to the four actual
canonical subfamilies (SCE.20). The strict inequalities
$4<5$, $16<18$, and $64<82$ give the respective lower bounds
$2,3,3,4$, even against arbitrary off-target adaptive words.

Proof of attainment on every original source. Reconstruct only
$\pi_3(v)$, not the unobserved terminal labels of $v$. Whenever an
acquired endpoint reply is branch, its public canonical representative
at the cutoff is $C_0$; alpha and beta keep their labels.

On $00$, query $RL$. An absent reply identifies $v=A$: a branch
with this name has two leaf children, so $RL$ would be present.
Otherwise this reply gives its left leaf, and a query $RR$ gives
the right leaf. This uses at most two Reads and four letters.

On $01$, query $RL,RRL,RRR$. The first gives the left leaf;
the latter two give the canonical children of the known right
branch. Their lengths sum to $2+3+3=8$. The case $10$ queries
$RLL,RLR,RR$, with the symmetric reconstruction and the same cost.

On $11$, first query $RLL$. An absent reply identifies $v=B$:
on every branch with this name both children are branches, so this
grandchild is present. Otherwise query $RLR,RRL,RRR$ as well.
These four endpoint replies reconstruct both children, replacing
cutoff branches by $C_0$. They use at most four Reads and twelve
letters. All are actual original-root words on the same stationary
source; rereading information once used by preparation is paid again.

The code bits supply exactly the presence and type facts used in
these case distinctions. Every right subtree of height at most three
falls into them, including variable shapes. The reconstructed
$\pi_3(v)$ preserves every target factor by the credited FMR
canonicalization. Hence it supplies all original requested trajectories
through (SCE.4), for authentic counts arriving only after completion.
The initial four-name code and its three-Read preparation are
unchanged. $\square$

**Corollary 6.3 (a concrete failed same-alphabet pooling bridge).** At
$D=3$, no four-name export admits pooled completion with at most two
fresh Reads: $123>4\cdot4^2=64$. In particular a single target-free
late Read cannot turn any four-name export into one common acquired
state answering all targets. The credited $E_0$ nevertheless answers
each individually selected original request with at most one Read,
and its exact pooled worst cost is four by Theorem 6.2.

Proof. Apply (SCE.16) with $m=4,N_3=123$ and then the credited
individual-target correctness of $E_0$. $\square$

This rejects precisely a target-independent, same-alphabet pooled
compiler with the stated fresh-query budget. It attributes no such
claim to FixedTreeCommonExtension or NativeLiteralMoore, excludes no
other common-extension organization, and supplies no new lower bound
for the original $M_1(D)$.

## 7. Shared realization, resources and the unclosed global bridge

**Convention 7.1 (source/action/observation mapping).** In Theorem 3.3
the common source is the full actual $t\in\mathcal F_D$, its
preparation and code function are literally retained, and its selected
query is the reduced reader's original literal. In Theorem 3.2 all
equations concern the same tuple and every old donor experiment stays
available. In Theorem 4.2 the source is represented by CBN's injective
actual reply array on one promise; the same $L$ and the same extension
are used across every cut of one tree. These analytical coordinates
are not extra acquired inputs. In Theorem 6.2 every fresh observation
is one paid original-root reply; neither its code bits nor the
canonical completion introduce a subtree port.

At public prefix-free actual block occurrences $Ra_i$, a donor
$(j,a)$ means precisely the one actual word $Ra_ja$. The credited
[CBN, Proposition 7.2][CBN] and [FMR, Lemmas 3.1 and 6.2][FMR]
provide the paid acquisition and occurrence transport, with presence
required. For $|a_i|\le H$, their sufficient joint preparation cost is
$n(2^d-1)$ Reads, peak length $H+d$ and at most

$$
n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr)
$$

letters. This construction computes one joint name from the whole
acquired tuple. It does not assume independently encoded children or
separately realized targets. A source-dependent cut, topology, pairing,
representative or selector accessible after export must be included in
the complete name. Public fixed tables need no unknown-source field.

**Convention 7.2 (separate prices).** The positive native rewrite
preserves preparation Reads and the entire alphabet exactly, including
any pre-existing surviving fields. Public table generation and
installation, decoder construction, work/control, post-request space,
final predictor size and address-generation work need not be preserved.
In the scan construction all acquired arrays, intermediate selectors,
buffers, lengths, allocation and timing beyond the complete name are
isolated by the declared paid service. The factor alone still fits in
$\lceil\log_2(2D+1)\rceil+1$ bits; authentic-count representation is
separate. Pooled completion has its separately charged calls, letters,
workspace and complete final state. No total-efficiency or physical
realization conclusion follows from counting names.

**Open problem 7.3 (unchanged original quantifiers).** The exact
requirements reduction leaves arbitrary joint sizes, correlations,
cycles, off-target donors, shared owners, guards, compatibility zeros
and full once-owned nonnegative joint weights. It does not produce
a total computable verifier $V(d,\mu,C,\pi)$, for rational
$\mu\in\Delta(S_d)$, rational $C>0$ and finite strings $\pi$,
whose acceptance implies

$$
\forall n\ge1\ \forall\Theta,\qquad
\sum_{x\in C_\Theta}\prod_i\mu(x_i)\le C^n,                    \tag{SCE.21}
$$

with accepted endpoints $-\log_2C$ cofinal at every unchanged
$\sigma_d$: for every $d\ge1$ and rational $\epsilon>0$, some
accepted pair would satisfy $-\log_2C>\sigma_d-\epsilon$.
Nor does it give a uniform effective vanishing length
error sufficient for terminating two-sided approximation of the original
$\lambda$. These remain [NPC, Definition 8.1][NPC] and
[GDB, Definition 11.1][GDB]'s obligations. Theorem 3.2 is an exact
presentation equivalence, so any such verifier must still control all
the original competitors. The unary minimum is not a universal
encoding minimum, and pooling is a different task.

The general-depth equality
$a_d=\min_\mu\Omega_d(\mu)=b_d=\min_\mu\beta_d(\mu)$ remains
unproved; finite-envelope optimization and rationalization are credited
NWO results. [COK, §§18–25][COK] fixes the matching-population maximum
and its error floor, and its reciprocal-unit losses retain their
one-incoming-owner conditions. [OCC, §§10–17][OCC] prices a separate
actual component descriptor and retains extensive conditional loss;
its augmented task is not $M_1$. [GDB, §§20–25][GDB] concerns its two
specified forest mechanisms and a restricted syndrome bypass. None
of those scopes is enlarged by the selector reduction.

Credit [NCE, §§13–19][NCE] for the specified positive asymmetric law
with exact pressure $3038031/7792603$, the all-original-competitor
lower bound, and $M_1(6)\ge1874$. Together with the credited D3
upper, the retained interval is

$$
\frac18\log_2\frac{7792603}{3038031}\le\lambda<\frac3{16},
\qquad M_1(3)=4.                                             \tag{SCE.22}
$$

There is no new rate endpoint here. Sharp $\lambda$, general exact
$M_1(D)$, effective all-size certification and the broader
minimal-relations/internal-observer and space/time/boundary/memory
mutual-recovery programme remain unresolved. The operational recovery
proved or reused here is the requested temporal factor and every
authentic-count readout. It recovers neither arbitrary hidden history,
unknown age, physical spacetime, nor the access services themselves.

## 8. Attribution, exact supplier scope and bounded checks

**Convention 8.1 (repository and primary sources).** All repository
suppliers in this volume refer to the immutable public snapshot
`17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b`. They are fallible
ordinary mathematical suppliers unless their exact formal declarations
are specifically named. Reading those declarations is not compilation.
The deductions in §§2–6 are `repo-derived`; functional dependence,
injective postcomposition of response functions, and deterministic
decision-tree leaf counting are mature methods. No worldwide
originality or exhaustive literature-search claim is made.

| Supplier | Exact use and transfer boundary |
| --- | --- |
| AAR §§12–13 and 16; FMR §§2–3 and 6; NPC §§2 and 5–8; CBN §§2 and 7 | Exact trajectory factor, canonical actual trees, every-word simulation, paid cover acquisition, arbitrary correlated fibers and rates. The full-menu passive endpoint is credited rather than reproved as an acquisition theorem. |
| D3 Theorems 2.3 and 4.1 | Exact original $M_1(3)=4$, its prescribed four-name preparation and fibers, and $\lambda<3/16$. The new cost in §6 is fresh pooled completion of that same code. |
| [`FixedTreeCommonExtension.result`][FTE], `Full`, `Implementation`, `canonical`, and [owning Blueprint][FTEB] | Finite nonempty coordinate alphabets, one finite Full tree with all coordinates as leaves, nonempty promise and one task. Theorem 4.2 checks these hypotheses on actual reply arrays. Internal mergers receive complete child-message tuples; root decoding is not a paid literal Read. |
| [`NativeLiteralMoore.NativeLiteralFeasible`][MLM], `literal_moore_feasibility`, `finite_literal_synthesis`, `zero_budget_endpoint`, and [owning Blueprint][MLMB] | A fixed prefix-free cut, current row $C=\operatorname{canonicalRow}(P,\rho u_0)$, supplied acquired `ImageValues C`, and four upper budgets for initial code names, installed states, calls and literal letters. The target is the entire predecessor row. Encoder/controller reselection is allowed; acquisition, export, isolation and authenticated one-update continuity are separate premises. No theorem here transfers its predecessor target, supplied class terms or code reselection into the original late-target task. |
| Kowshik–Kumar, *Optimal Function Computation in Directed and Undirected Graphs*, [arXiv:1105.0240v2][KK], §III-B, Theorem 4, Lemma 2 and Example 1 | Response-function construction for the full Cartesian assignment space; feasibility of specified encoders under arbitrary support is an all-cut condition. The correlated diagonal example couples encoders. Separate average-description optimization uses full support. This supplies neither native paid acquisition nor the one-late-Read bridge or a native all-size cap. |
| [Systematic Data Structure Lower Bounds via the Query-with-Sketch Model, arXiv:2609.18024v1][QWS], Definition 2.1 and model comparison | A sketch selects an adaptive coordinate-probe procedure; repeated probes count. The text distinguishes one decision tree for all outputs from separate trees for individual outputs. Theorem 5.2 instead proves its actual-tree four-reply count directly; no matrix application or conditional-min-entropy theorem is imported. |

The common-extension identity and finite literal synthesis are credited
suppliers with distinct contracts. A root decoder, supplied full source
table or semantic extension is not silently installed as a native
acquired state. The source/action/observation and resource correspondence
needed for a different transfer remains an additional theorem.

**Convention 8.2 (bounded exact readings).** In-memory exact enumeration
gives the following readings; no experiment program or data is retained.

| Depth | Canonical states | Selected targets | Omitted-coordinate identity checks | Pairs of an essential target and a distinct target that fail unary determination |
| --- | ---: | ---: | ---: | ---: |
| $1$ | $3$ | $1$ | $0$ | $0$ |
| $2$ | $11$ | $2$ | $11$ | $4$ |
| $3$ | $123$ | $5$ | $246$ | $30$ |
| $4$ | $15131$ | $11$ | $60524$ | $154$ |

For each enumerated state the selected factor vector also distinguishes
that canonical state. Enumerating all $1446$ actual right subtrees of
height at most three gives the canonical fiber sizes $5,18,18,82$.
The procedures in Theorem 6.2 reconstruct $\pi_3(v)$ on all of them,
with worst fresh costs $(2,4),(3,8),(3,8),(4,12)$ in
(Reads, letters) order. All $10122$ comparisons of the seven full
factors with those of the reconstructed canonical source agree.
These checks cover only the stated finite domains. Universal
minimality, all-template equivalence, simultaneous common extensions,
arbitrary-word lower bounds and asymptotic claims rest on the ordinary
proofs above, not finite extrapolation. No Lean build, ingestion or
all-programme completion is asserted.

[AAR]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[FMR]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NPC]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[CBN]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[D3]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[NCE]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[COK]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONDITIONAL_OWNER_KERNELS.md
[OCC]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OWNER_COMPONENT_COMPLETION.md
[GDB]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GLOBAL_DEPENDENCE_BOUNDARIES.md
[FTE]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/D5/S3/Observer/Separation/FixedTreeCommonExtension.lean
[FTEB]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/Blueprint/D5/S3/Observer/Separation/FixedTreeCommonExtension.scribe.cs
[MLM]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.lean
[MLMB]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.scribe.cs
[KK]: https://arxiv.org/html/1105.0240v2
[QWS]: https://arxiv.org/html/2609.18024v1

## 追加锚（本行以下为增补区）

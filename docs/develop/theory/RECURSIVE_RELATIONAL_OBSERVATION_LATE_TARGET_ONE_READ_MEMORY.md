# Recursive relational observation: retained memory for one late target Read

## 1. Stationary sources, paid preparation and undeclared targets

**Convention 1.1 (ordinary mathematics and source correspondence).** This
volume gives ordinary finite-tree mathematics, with the native operations
of the published repository at revision
`abe0ff2886e540396cf69a9cfba3b28f5f69c98e`. It is reference theory, without
new Lean kernel certification. Theorems below concern a retained alphabet
and an authenticated prediction interface; they do not establish physical
space or time recovery. Published text is preserved; additions and
corrections belong after the terminal append anchor.

**Definition 1.2 (the exact native family and literal port).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\operatorname{height}(\alpha)=\operatorname{height}(\beta)=0,
\qquad
\operatorname{height}(\langle u,v\rangle)
 =1+\max(\operatorname{height}(u),\operatorname{height}(v)).
$$

The pairing is ordered. A word is a finite string of $L,R$, including
the root word $\varepsilon$. Every word is a legal original-root query.
At a present leaf it returns its label, at a present pair it returns
$\mathsf{branch}$, and beyond a leaf it returns $\mathsf{absent}$.
In particular absence is a reply, rather than an illegal query. Write
$r_t(w)=\operatorname{readout}(w,t)$. The substitution is

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

For public $D\ge1$ the source and target families are exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:
                    \operatorname{height}(v)\le D\},
\qquad
\mathcal P_D=\{Rq:q\in\{L,R\}^{\ast},\ |q|\le D-1\}.
$$

One actual $t\in\mathcal F_D$ remains stationary throughout preparation,
handoff and later acquisition. No source is changed within an execution.
There is no subtree, equality, source-identity, age, reset, copying,
free-navigation or free-advice port. Mathematical child notation does
not supply a child as an operational input. Every child observation must
submit its entire literal address from the original root.

These are `Source` and `substitution` in
[GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
and `Address`, `Reply`, `readout` in
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean).
The Boolean directions there are $L=\mathrm{false}$ and
$R=\mathrm{true}$; the leaf labels are alpha for `true` and beta for
`false`. That module's Boolean recognition task is not the task below.

**Assumption 1.3 (paid complete handoff and lawful entry).** Preparation
starts from the same source-independent state for every $t$, with only
public $D$ and common installed code and tables. Its only source
dependence comes from actual charged literal Reads. It terminates on
every source and exports a finite effective code $E(t)$ before any
target is supplied. A separately supplied paid handoff isolates all
other accessible preparation state and lawfully enters the later
reader. Every surviving source distinction belongs to the code: this
includes selectors, operands, buffers, transcripts, control, lengths,
allocation, handles, counters and accessible timing distinctions.
Any remaining field must be a fixed function of $E(t)$ and public data.
Prior transcripts and previously acquired descriptions are inaccessible.

Isolation, source continuity, authentication, export and new reader entry
are services assumed and separately paid for. They are not inferred
physical actions, erasure operations, or actions of an already stopped
producer. Inaccessible material need not be physically erased.

**Definition 1.4 (one late Read and the retained-alphabet objective).**
Only after export, a public source-independent $p\in\mathcal P_D$ is
supplied. One common deterministic effective reader, given $E(t),D,p$
and the installed tables, makes at most one fresh Read of that same
stationary $t$. Its word may be any finite original-root word, chosen
from those inputs. It then produces a final predictor state $Z$.
For every subsequently supplied authentic $k\ge0$, a passive decoder
must satisfy

$$
\mathsf{Dec}(Z,D,p,k)=r_{\rho^k t}(p)
\qquad(t\in\mathcal F_D, p\in\mathcal P_D, k\ge0).
\tag{LTR.1}
$$

No $k$ is supplied before the query, and there are no further Reads.
Zero-Read branches are permitted. Each statement is uniform over the
entire family, all late targets and all authentic counts; it is not a
source-dependent request or a separate preparation for each target.
Define

$$
M_1(D)=\min_{E,\mathsf{Reader},\mathsf{Dec}}|E[\mathcal F_D]|,
\qquad B_1(D)=\lceil\log_2 M_1(D)\rceil.
\tag{LTR.2}
$$

The minimization is over preparations and readers satisfying the whole
contract. It counts the complete attained source-dependent alphabet.
$B_1$ is its fixed-width binary naming capacity, not total physical
storage. Preparation Read count, submitted letters and maximum word
length will be bounded for the constructions. Preparation work and
control, installation, temporary and post-request workspace, final
predictor size, count representation, addressing overhead, isolation,
entry and physical time remain separate resource coordinates.

## 2. Reused temporal factors and the common-fiber condition

**Convention 2.1 (the published all-count predictor).** Put
$s(q)=\#L(q)+2\#R(q)$, and $e(\alpha)=0$, $e(\beta)=1$.
Use the predictive factor $G_q(u)=(b_q(u),c_q(u))$ of
[Adaptive Acquired Reference Frontier, Definition 12.2 and Theorem 12.3](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md#12-the-native-spatial-quotient-for-arbitrary-retained-prediction-codes),
abbreviated AAR. If $q$ is an original branch, $G_q(u)=(0,0)$.
If the first leaf along $q$ is at $a\preceq q$, with actual label
$\lambda$ and $q=ar$, then

$$
G_q(u)=
\begin{cases}
(2-e(\lambda),1-e(\lambda)),&r=\varepsilon,\\
(s(r)+2-e(\lambda),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{LTR.3}
$$

For every finite $u$, word $q$ and $k\ge0$, the supplied theorem gives

$$
r_{\rho^k u}(q)=\mathsf{Pred}(G_q(u),k),\qquad
\mathsf{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1\text{ and }k=b-1,\\
\alpha,&c=1\text{ and }k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{LTR.4}
$$

On attained factors $c=1$ implies $b\ge2$. The entire trajectory
recovers $b$ as the first branch count and $c$ by the presence of an
alpha stage. Thus factors and trajectories determine each other.
For $t=\langle\alpha,v\rangle$ and $p=Rq$,

$$
G_p(t)=G_q(v),\qquad
r_{\rho^k t}(Rq)=r_{\rho^k v}(q),\qquad b_p(t)\le2D.
\tag{LTR.5}
$$

The source correspondence is the pairing homomorphism and
`original_present_transport` in
[NativeDepthPatterns](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean).
Transport applies only at an actually present original subtree, in
particular at the blocking leaf of an absent target. The atomic last-edge
guard in (LTR.3) is essential: an $L$-ending nonempty suffix has no alpha
stage. The decoder is also AAR Proposition 13.3's $\Gamma_p$.
These laws and the factor/trajectory bijection are reused suppliers,
not new recovery theorems.

**Lemma 2.2 (the quantifier order on unchanged attained fibers).** For
an effective finite encoder acquired under Assumption 1.3, let
$C_z=\{t\in\mathcal F_D:E(t)=z\}$, for each attained $z$.
A correct one-Read reader exists exactly when, for every $z$ and every
$p\in\mathcal P_D$, either $G_p$ is constant on $C_z$, or there is
one word $w=w(z,D,p)$ such that

$$
\forall t,u\in C_z,\quad
r_t(w)=r_u(w)\ \Longrightarrow\ G_p(t)=G_p(u).
\tag{LTR.6}
$$

Proof. Before its only Read the reader's inputs are identical throughout
$C_z$, so its decision to stop or its submitted word is fixed there.
Equal replies give identical final predictors, hence identical entire
trajectories and, by Convention 2.1, identical factors. With zero Reads
the factor must be constant. Conversely each attained reply cell has
one factor by (LTR.6). The common finite table assigns that factor to
the reply and uses (LTR.4). Values on unattained replies are immaterial.
The family, code alphabet and target set are finite, and the factors
are effective, so these choices have a finite installed realization.
Installation is separate from paid acquisition. $\square$

This is an interface criterion, not an exact structural solution for
$M_1$. It requires one acquired partition that works for every target.
It does not permit changing $E$ after $p$, assigning different words
to different pairs in a fiber, or replacing its sources by completions
that change the fiber. On the full family, words longer than $D+1$
are constant absent and can be removed without changing any fiber.
No reduction to target prefixes follows. Section 7 gives an attained
counterexample to that stronger reduction.

## 3. A paid paired-code construction on the full family

**Definition 3.1 (codes and the two designated fibers).** For an
auxiliary target depth $d\ge1$ set

$$
\mathcal C_1=\{0,1\},\qquad P_1=0,\quad Q_1=1,\qquad
E_1(u)=\begin{cases}0,&u\text{ is a leaf},\\1,&u\text{ is a branch}.
\end{cases}
$$

Recursively define

$$
\begin{aligned}
\mathcal C_{d+1}&=\mathcal C_d\times\mathcal C_d,\\
E_{d+1}(\langle u,v\rangle)&=(E_d(u),E_d(v)),\\
E_{d+1}(\alpha)&=(P_d,P_d),\qquad
E_{d+1}(\beta)=(Q_d,Q_d),\\
P_{d+1}&=(P_d,Q_d),\qquad Q_{d+1}=(Q_d,P_d).
\end{aligned}
\tag{LTR.7}
$$

$P_d\ne Q_d$. Leaf codes are absorbed into two branch-code pairs.
Neither a separate leaf selector nor a label survives outside this
code. The recursion counts this particular construction, not the
minimum $M_1$.

**Definition 3.2 (one common selector and reply decoder).** For each
$c\in\mathcal C_d$ and every $|q|\le d$, define a relative query
$W_d(c,q)$ and a factor decoder $J_d(c,q,y)$ as follows.
At $q=\varepsilon$, query the root and decode its reply as
$(2,1)$ for alpha, $(1,0)$ for beta and $(0,0)$ for branch.
For $d=1$ and $|q|=1$, code $0$ queries the root and applies
(LTR.3) to its label with residual $q$; code $1$ queries $q$ and
decodes its alpha, beta or branch reply as the endpoint factor.

At depth $d+1$, for $q=br$ with $b\in\{L,R\}$, write
$c=(c_L,c_R)$ and set

$$
W_{d+1}(c,br)=bW_d(c_b,r).
\tag{LTR.8}
$$

Decode its one reply by

$$
J_{d+1}(c,q,y)=
\begin{cases}
(s(q)+2,\mathbf1_{q\text{ ends in }R}),
       &c=(P_d,P_d),\ y=\mathsf{absent},\\
(s(q)+1,\mathbf1_{q\text{ ends in }R}),
       &c=(Q_d,Q_d),\ y=\mathsf{absent},\\
J_d(c_b,r,y),&\text{otherwise}.
\end{cases}
\tag{LTR.9}
$$

Unattained decoder cases may be assigned any fixed value. In the
actual source $t=\langle\alpha,v\rangle$, a relative word $a$ means
the submitted original-root literal $Ra$. The recursion in (LTR.8)
constructs one word before its reply; it does not execute recursive
Reads or transfer a subtree.

**Theorem 3.3 (correctness, present-query invariant and joint attainment).**
For every $d\ge1$, every finite $u$ and every $|q|\le d$,

$$
J_d(E_d(u),q,r_u(W_d(E_d(u),q)))=G_q(u).
\tag{LTR.10}
$$

The selected word has length at most $d$. On either designated fiber
$E_d(u)=P_d$ or $E_d(u)=Q_d$, its reply is never absent, for every
such $q$. Every code in $\mathcal C_d$ is attained by an actual tree
of height at most $d$, and

$$
|\mathcal C_d|=2^{2^{d-1}}.
\tag{LTR.11}
$$

Proof. Induct simultaneously on $d$. At $d=1$ the root is always
present. On code $0$ every target queries that root leaf; on code
$1$ a length-one target queries a present child of a branch. The
replies and (LTR.3) prove correctness and the invariant. The leaf
alpha attains $0$ and $\langle\alpha,\alpha\rangle$ attains $1$.

For the induction step the root target is handled directly. Consider
$q=br$. If $u=\langle u_L,u_R\rangle$, its selected reply equals
$r_{u_b}(W_d(E_d(u_b),r))$. Usually (LTR.9) invokes the induction
decoder, yielding $G_r(u_b)=G_q(u)$ by homomorphism. The two special
absent cases cannot occur on such a branch: at code $(P_d,P_d)$
the child has code $P_d$, so its selected query is present; likewise
for $(Q_d,Q_d)$. Thus no branch is incorrectly declared a leaf.

If $u=\alpha$ its code is $(P_d,P_d)$ and every nonempty selected
word is absent. The first case of (LTR.9) gives exactly $G_q(\alpha)$.
For $u=\beta$ the second case gives $G_q(\beta)$. This uses absence
as a guarded distinction between the absorbed root leaf and branch
sources in the same code, rather than transporting from an absent
address. The query is chosen without $k$, so (LTR.4) then proves
correctness for every later count.

The two new cross-pair designated codes contain only branches: they
differ from both diagonal leaf codes. Their selected child has one
of the two old designated codes, making its selected reply present.
Their root query is present as well. This proves the invariant and
the distinctness of the designated codes at the next depth.

The length bound follows from (LTR.8). For attainment, realize any
$c_L,c_R\in\mathcal C_d$ by the inductively supplied actual trees,
and pair those trees. This one tree simultaneously attains the desired
pair code and has height at most $d+1$. Hence the whole Cartesian
code alphabet is attained. The recurrence
$|\mathcal C_1|=2$, $|\mathcal C_{d+1}|=|\mathcal C_d|^2$ gives
(LTR.11). $\square$

**Theorem 3.4 (actual target-blind acquisition and full-family upper).**
For $D\ge2$, put $d=D-1$ and $N=2^{D-2}$. There is one preparation
and one reader on all of $\mathcal F_D$ satisfying (LTR.1), with
complete attained alphabet exactly $2^N$ and preparation costs

$$
T\le2^{D-1}-1,\qquad Q\le D-1,\qquad
A\le(D-2)2^{D-1}+1.
\tag{LTR.12}
$$

Here $T$ counts all actual preparation calls, $Q$ is their maximum
submitted word length and $A$ their total submitted letters. The
later reader submits one word of length at most $D$. Consequently
$M_1(D)\le2^N$.

Proof. Starting at literal $R$, evaluate (LTR.7) by actual Reads.
At depth parameter $1$ a node Read decides leaf versus branch.
At larger parameter a leaf reply selects its prescribed diagonal
code; a branch reply schedules the two original-root child words,
each at one smaller parameter. Stationarity and the actual branch
reply certify those children as present. No source description or
later target is an input. The recursion terminates, using at most
$2^d-1$ Reads. At relative depth $j<d$ there are at most $2^j$
calls, each at submitted length $j+1$, so

$$
\sum_{j=0}^{d-1}(j+1)2^j=(d-1)2^d+1,
$$

which proves (LTR.12). Use a fixed public concatenated binary name
of the pair codes. Its width is $2^{d-1}=N$; fixed output extent
and all surviving fields depend only on that name and $D$. All
other acquired labels, operands, stacks, buffers, control and
allocation distinctions are isolated by the paid service in
Assumption 1.3. This is an acquired code, not a free preassigned color.

Every code is attained within height $d\le D$ by Theorem 3.3. For
every late $p=Rq$, the reader computes $W_d(E_d(v),q)$, submits
the one literal $RW_d(E_d(v),q)$ on the same $t$, and retains the
factor from $J_d$. Equations (LTR.4), (LTR.5) and (LTR.10) give
(LTR.1) simultaneously for all sources, targets and counts.
Preparation workspace, local code arithmetic, installed programs,
handoff and final predictor representation are separate costs; the
alphabet bound makes no free-total-efficiency claim. $\square$

## 4. A simultaneous weighted full-family lower bound

**Definition 4.1 (five native gadgets on one actual scaffold).** For
$D\ge2$, set $h=D-2$, $N=2^h$ and take the perfect ordered binary
scaffold of height $h$ in $v$. At every frontier word
$a_i\in\{L,R\}^h$, independently choose one of

$$
g_0=\alpha,\quad g_1=\beta,\quad
g_2=\langle\alpha,\alpha\rangle,\quad
g_3=\langle\alpha,\beta\rangle,\quad
g_4=\langle\alpha,\langle\alpha,\alpha\rangle\rangle.
\tag{LTR.13}
$$

For $x\in\{0,1,2,3,4\}^N$, call the resulting source $t_x$.
Every simultaneous filling is an actual member of $\mathcal F_D$,
since its right-subtree height is at most $h+2=D$. Define the late
target $p_i=Ra_iR$, of permitted length $D$. The five factors at
that target, in order, are

$$
(4,1),\ (3,1),\ (2,1),\ (1,0),\ (0,0).
\tag{LTR.14}
$$

Thus its complete trajectory identifies $x_i$. These are not separate
marginal best cases: all $5^N$ combinations exist on the same actual
source grammar with the same scaffold and the same target menu.

**Lemma 4.2 (all finite words and the local weighted selector bound).**
On the family of Definition 4.1 every literal is either constant,
or depends on just one gadget through a local suffix in this table.
The entries list replies on $g_0,\ldots,g_4$.

| Local suffix | Reply vector | Maximum identified weight, in units of $1/7$ |
| --- | --- | ---: |
| $\varepsilon$ | $(\alpha,\beta,\mathsf{branch},\mathsf{branch},\mathsf{branch})$ | $5$ |
| $R$ | $(\mathsf{absent},\mathsf{absent},\alpha,\beta,\mathsf{branch})$ | $5$ |
| $L$ | $(\mathsf{absent},\mathsf{absent},\alpha,\alpha,\alpha)$ | $3$ |
| $RL$ or $RR$ | $(\mathsf{absent},\mathsf{absent},\mathsf{absent},\mathsf{absent},\alpha)$ | $3$ |
| Every other suffix | $(\mathsf{absent},\mathsf{absent},\mathsf{absent},\mathsf{absent},\mathsf{absent})$ | $2$ |

For the analytical measure
$\mu=(2,2,1,1,1)/7$, a decoder of any single local reply can
correctly identify that gadget on mass at most $5/7$. Its decoded
state map has image of size at most four. A constant query has
maximum identified mass $2/7$.

Proof. The original outer root is branch, its left leaf is alpha,
and strict extensions of that left leaf are absent. In the right
subtree, a word ending strictly above the scaffold frontier is
constant branch. Every other word reaches exactly one frontier
gadget and has a unique local suffix. Inspecting the five finite
gadgets gives the displayed exhaustive table, including arbitrary
depths and words outside the target cone. For a decoder to identify
the state it may choose at most one state in each reply cell. Summing
the heaviest weights in those cells gives the third column.
There are at most four replies, proving the image bound. $\square$

**Lemma 4.3 (weighted dependence, including correlated fibers).** Let
$X_1,\ldots,X_n$ have the independent analytical measure $\mu$ of
Lemma 4.2. Impose one equation per coordinate: either
$x_i=f_i(x_{j(i)})$, where $f_i$ factors through one of the local
native query partitions in that lemma, or $x_i$ equals a constant.
The mass of the set satisfying all equations is at most $(5/7)^n$.

Proof. Direct an arrow $i\to j(i)$ for every nonconstant equation;
a constant vertex has no outgoing arrow. Each component of this
finite graph ends either at one constant vertex or at one directed
cycle. Trees attached to those terminal structures can be eliminated
from their leaves toward the terminal structure. Conditional on a
parent value, the eliminated coordinate is fixed, so its summed
mass is at most $2/7$. This argument sums over an independent ambient
measure; it assumes no conditional independence of an eventual code
fiber.

A constant terminal vertex has mass at most $2/7$. A one-vertex
cycle imposes $x_i=f_i(x_i)$. Its fixed-point set contains at most
one correctly identified state per native reply cell, giving mass
at most $5/7$ by Lemma 4.2. For a cycle of length $k\ge2$, choose
one cycle coordinate. Its value lies in the image of its defining
map, of size at most four. Given this value, walking against the
arrows uniquely determines every other cycle coordinate. Thus there
are at most four satisfying cycle tuples, each with mass at most
$(2/7)^k$. Since

$$
4(2/7)^k\le(5/7)^k\qquad(k\ge2),
$$

the required bound holds for each terminal structure. Every eliminated
vertex contributes a factor at most $2/7\le5/7$. Distinct components
use disjoint ambient coordinates, so their masses multiply. The full
bound follows. $\square$

**Theorem 4.4 (the general full-family lower).** Under Definitions
1.2--1.4, every correct complete preparation and one-Read reader
satisfies, for $D\ge2$ and $N=2^{D-2}$,

$$
|E[\mathcal F_D]|\ge\left\lceil(7/5)^N\right\rceil.
\tag{LTR.15}
$$

Proof. Restrict its actual code fibers to the simultaneous sources
$t_x$ of Definition 4.1, without altering the encoder. Fix an attained
code $z$ and its restricted fiber $B_z$. For target $p_i$, the
reader's pre-query inputs are constant on this same $B_z$. Its zero-Read
decision or submitted word is consequently fixed. If it makes a Read,
Lemma 4.2 makes that reply either constant or a function of one
coordinate $x_j$, possibly $j\ne i$. The final predictor depends only
on this reply and the common inputs.

The required five trajectories in (LTR.14) are distinct. Therefore,
on $B_z$, correctness imposes $x_i=f_i(x_j)$, where $f_i$ factors
through this native reply partition. Assign any fixed gadget state
to replies whose predictor does not represent one of those five
trajectories. This extends $f_i$ to all five input states without
increasing its image beyond the number of reply cells. Such arbitrary
extensions do not change the equation on $B_z$. A constant query
or zero Reads instead impose a constant $x_i$. The reader is not
operationally executed for multiple targets at once: these equations
express its required correctness for every permitted alternative
late request on the one unchanged source.

These equations for all $i$ define a superset of $B_z$. Lemma 4.3
therefore gives $\mu^N(B_z)\le(5/7)^N$, even with arbitrary
correlations inside the actual fiber, off-target queries, very deep
words and code-dependent selectors. The restricted fibers partition
the whole $5^N$ actual-source product, of total analytical mass one.
Hence their number is at least $(7/5)^N$, and the attained full-family
alphabet is at least that large. Integer rounding proves (LTR.15).

The measure is a lower-bound witness, not a prior on correctness.
No independence of retained fibers, source-dependent request,
unavailable preparation transcript or prefix-only query assumption
has been used. $\square$

## 5. General retained-bit price and the known-task contrast

**Theorem 5.1 (the full-family interval and its precise scale).** For
every $D\ge2$, with $N=2^{D-2}$,

$$
\boxed{\ \left\lceil(7/5)^N\right\rceil
          \le M_1(D)\le2^N\ },\qquad
\left\lceil N\log_2(7/5)\right\rceil\le B_1(D)\le N.
\tag{LTR.16}
$$

In particular

$$
\frac{\log_2(7/5)}4\,2^D\le\log_2 M_1(D)\le\frac14\,2^D,
\qquad B_1(D)=\Theta(2^D).
\tag{LTR.17}
$$

The lower coefficient in (LTR.17) is approximately $0.1213567068$.
Also $M_1(1)=1$ and $M_1(2)=2$.

Proof. Theorems 3.4 and 4.4 give the alphabet interval. Taking
logarithms and rounding gives the bit bounds. For $D=1$, the only
late target is $R$. Export one constant code with zero preparation
Reads, zero submitted letters and zero maximum preparation length.
One later Read at $R$ returns alpha, beta or branch and determines
its entire trajectory by (LTR.4). A nonempty family needs at least
one attained code, so $M_1(1)=1$. At $D=2$ (LTR.16) gives both
$\lceil7/5\rceil=2$ and the upper value $2$. $\square$

The logarithmic estimates match the order of retained bits. They do
not give multiplicatively matching alphabet asymptotics: the two
unrounded displayed alphabet endpoints have ratio $(10/7)^N$.
The notation $M_1(D)=2^{\Theta(2^D)}$ expresses exponential order
only, not an exact alphabet rate or an optimum recursion.

**Proposition 5.2 (what target revelation order changes).** If the
target $p$ is known before preparation, its sufficient predictive
alphabet has at most $2|p|+1$ values and is acquirable in exactly
$\lceil\log_2(|p|+1)\rceil$ worst-case native Reads on this family,
with no later Read. By contrast, the late-target contract requires
the growing retained-bit bound (LTR.17). If the whole public menu
is predicted with zero later Reads, its exact alphabet and acquisition
price are already fixed-menu suppliers.

Proof. Directly reuse AAR Theorem 13.8 for singleton acquisition,
Definition 13.2 and Proposition 13.3 for its at-most-$2|p|+1$
descriptor alphabet, and Theorem 12.6 for the minimum predictive
alphabet. Theorem 16.8 prices acquisition for a known joint menu.
For zero later Reads take $P=\mathcal P_D$ in AAR §§12 and 16;
no new endpoint theorem is needed. The late-request bound follows
from Theorem 5.1 on a single preparation independent of $p$. $\square$

**Proposition 5.3 (acquired information and retained distinctions).**
If the complete initial shape of $v$ is public, independent of its
unknown leaf labels, a constant retained code suffices: query the
known blocking leaf of the declared target, or its known branch
endpoint, and use (LTR.3). The full-family lower therefore uses
unknown shapes together with labels; it is not a count of leaf labels.

Proof. The public shape supplies the first leaf position on every
target path, or certifies that its endpoint is a branch. One native
Read of that leaf supplies its label; a branch target may use zero
Reads. All-count decoding is Convention 2.1. In the full-family
preparation of Theorem 3.4, many labels are actually acquired and
then isolated. Its small retained alphabet does not make those
earlier observations uncharged. $\square$

## 6. An exact restricted proper-projection and box-cover theorem

**Definition 6.1 (the four-gadget restriction and its box cover).**
Let a fixed public ordered full binary scaffold have $n\ge1$ leaf
addresses $a_1,\ldots,a_n$, each of length at most $D-2$, where
$D\ge2$. Fill them independently with

$$
h_0=\alpha,\quad h_1=\beta,\quad
h_2=\langle\alpha,\alpha\rangle,\quad
h_3=\langle\beta,\alpha\rangle.
\tag{LTR.18}
$$

Pair this right subtree with the outer alpha. The resulting restricted
family $\mathcal X_{n,D}\subseteq\mathcal F_D$ is in bijection with
$[4]^n$, where $[4]=\{0,1,2,3\}$. It has the same late target set
$\mathcal P_D$ and the same literal port and handoff as before.
For a vector $c\in[4]^n$ define the maximal proper box

$$
\mathcal B_c=\prod_{i=1}^n([4]\setminus\{c_i\}),
\qquad
C_n=\min\{m:[4]^n=\bigcup_{j=1}^m\mathcal B_{c^{(j)}}\}.
\tag{LTR.19}
$$

The restricted minimum is not substituted for $M_1(D)$.

**Theorem 6.2 (exact native admissible fibers).** A nonempty
$B\subseteq[4]^n$ can serve as a common one-Read fiber for every
late target exactly when every coordinate projection is proper:

$$
\forall i,\quad\pi_i(B)\ne[4].
\tag{LTR.20}
$$

Arbitrary correlations within $B$ are allowed.

Proof of necessity. The targets $Ra_iL$ are permitted, and their
four factors are $(3,0),(2,0),(2,1),(1,0)$, respectively. Each
target trajectory thus identifies its gadget state. Every word
ending in the fixed scaffold or outer left cone is constant. A
word entering one gadget has root replies
$(\alpha,\beta,\mathsf{branch},\mathsf{branch})$, left-child replies
$(\mathsf{absent},\mathsf{absent},\alpha,\beta)$, right-child replies
$(\mathsf{absent},\mathsf{absent},\alpha,\alpha)$, or, at greater
depth, constant absence. This is an exhaustive all-word classification
on the same product family. Every fixed native query therefore has
at most three replies, even in another gadget. On $B$, one reader
query gives at most three distinct required trajectories, and zero
Reads give at most one. Hence $|\pi_i(B)|\le3$ for every $i$.

Proof of sufficiency. Choose one missing state $c_i$ per coordinate.
If $c_i=0$ or $1$, Read the gadget's left child: its three replies
distinguish the remaining three states. If $c_i=2$ or $3$, Read the
gadget root: its three replies distinguish the remaining three states.
For a late target ending strictly inside the scaffold the endpoint
is a persistent branch, needing zero Reads. Otherwise its path
enters one known gadget; select that coordinate's prescribed word,
identify its actual gadget, and compute (LTR.3) at the residual path.
This works for every target, including paths initially absent below
a gadget leaf, and all later counts. It is one common rule using
only the fiber's installed missing states and the late target.
The submitted root or left-child word has length at most $D$.
No correlation assumption is needed. $\square$

**Theorem 6.3 (exact restricted alphabet with paid attainment).** The
minimum complete attained alphabet on $\mathcal X_{n,D}$ is $C_n$.
It has an effective target-blind preparation with at most $2n$ actual
Reads, maximum word length at most $D$ and total letters at most
$n(2D-1)$. Moreover

$$
\left\lceil(4/3)^n\right\rceil\le C_n
\le\left\lceil(4/3)^n(n\ln4+1)\right\rceil,
\qquad
\log_2 C_n=n\log_2(4/3)+O(\log n),
\tag{LTR.21}
$$

and $C_1=2$, $C_2=3$.

Proof of the exact correspondence. By Theorem 6.2 every lawful fiber
is contained in a box from (LTR.19), selecting one absent projection
state in each coordinate. Thus any attained-code partition supplies
a cover with the same number of boxes, and needs at least $C_n$
codes. Conversely install a minimum box cover, and assign every
actually acquired vector to its first containing box. Each resulting
fiber satisfies (LTR.20) and has the reader of Theorem 6.2. It uses
at most $C_n$ codes; the preceding lower bound forces all $C_n$
values to be attained.

To acquire this vector from common initialization, actually Read
every gadget root $Ra_i$. A leaf reply identifies $h_0$ or $h_1$;
a branch reply is followed by Read $Ra_iL$, whose alpha or beta
reply identifies $h_2$ or $h_3$. The scaffold promise makes these
addresses known, not their replies. At most two calls per gadget
are made, with respective lengths at most $D-1$ and $D$. After
computing the box index, export only its fixed-width name and
isolate all other acquired state by Assumption 1.3. Public cover
construction, installation, local search and temporary vector storage
are separate resources. This is an actual paid attaining encoder.

For the cover lower bound each box has $3^n$ points, while there
are $4^n$ points to cover. For the upper bound choose $m$ exclusion
vectors uniformly and independently from $[4]^n$. A fixed source
vector belongs to each random box with probability $(3/4)^n$.
The probability that some vector is uncovered is at most

$$
4^n(1-(3/4)^n)^m\le4^n\exp(-m(3/4)^n)<1
$$

when $m=\lceil(4/3)^n(n\ln4+1)\rceil$. A cover therefore exists.
Finite exhaustive search for this public cover is an effective
installation procedure; no efficiency bound or source-dependent
advice is inferred. Taking logarithms gives (LTR.21).

Two three-element sets cover $[4]$, while one does not, proving
$C_1=2$. For $n=2$ any two maximal boxes have intersection of size
at least four and union of size at most $9+9-4=14<16$. Three boxes
with exclusion vectors $(0,0),(1,1),(2,2)$ cover every pair: a pair
contains at most two of those three symbols, so one excluded symbol
is absent from both coordinates. Hence $C_2=3$. $\square$

**Corollary 6.4 (a full-family small-depth consequence and coupling).**
For the original full family,

$$
3\le M_1(3)\le4.
\tag{LTR.22}
$$

Two restricted single-gadget minima do not multiply to the restricted
two-gadget minimum.

Proof. At $D=3$, the height-one scaffold with two gadget positions
gives $\mathcal X_{2,3}\subseteq\mathcal F_3$. Restricting any
full-family preparation and reader preserves its actual fibers,
common rule and all-target correctness, so its alphabet is at least
$C_2=3$. The upper bound is Theorem 3.4. Also $C_1^2=4>3=C_2$.
The box encoder correlates the two coordinates; an independent
subtree-code multiplication would lose this attainable option.
$\square$

The restricted theorem has an exact asymptotic exponent in (LTR.21).
It is not the full-family exponent. In particular its gadgets have
height at most one, whereas Definition 4.1 includes a height-two
gadget and improves the exponential lower coefficient of the
four-gadget volume bound. No extension of a
restricted optimal coloring to all variable shapes is supplied here.

## 7. An attained off-target literal and failed prefix normalization

**Theorem 7.1 (a paid full-family fiber with off-target recovery).** At
$D=3$ there is a complete actually acquired encoder on all of
$\mathcal F_3$ with a four-source fiber on which one off-target
literal serves every late target. On that same fiber no single prefix
literal serves the particular target $p=RLL$.

Proof. Let $(u_0,u_1,u_2,u_3)$ be the four gadgets in (LTR.18), and
put

$$
(z_0,z_1,z_2,z_3)=
(\alpha,\langle\alpha,\alpha\rangle,
 \langle\beta,\alpha\rangle,
 \langle\langle\alpha,\alpha\rangle,\alpha\rangle),
\qquad t_i=\langle\alpha,\langle u_i,z_i\rangle\rangle.
\tag{LTR.23}
$$

Every right subtree has height at most three. The literal $RRL$
has replies $(\mathsf{absent},\alpha,\beta,\mathsf{branch})$ on
these four sources. It therefore identifies the actual $t_i$ in
one Read. Common installed representatives then supply $G_p(t_i)$
for every late $p$, and (LTR.4) supplies every authentic count.

At $RLL$, the four factors are $(3,0),(2,0),(2,1),(1,0)$, all
different. The prefix replies are

| Prefix of $RLL$ | Reply vector on $t_0,t_1,t_2,t_3$ |
| --- | --- |
| $\varepsilon$ or $R$ | $(\mathsf{branch},\mathsf{branch},\mathsf{branch},\mathsf{branch})$ |
| $RL$ | $(\alpha,\beta,\mathsf{branch},\mathsf{branch})$ |
| $RLL$ | $(\mathsf{absent},\mathsf{absent},\alpha,\beta)$ |

Each prefix merges distinct trajectories. Before its one query a
deterministic prefix-only reader sees the same code and target on
the entire fiber, so it must choose one of those words and cannot
be correct. Zero Reads fail as well.

For actual whole-family attainment, prepare by a branch-guided
literal traversal of the entire $v$ from $R$. Query every reached
node once, scheduling children only on branch. This obtains its
finite labelled description in at most $15$ Reads, with maximum
submitted length $4$ and total letters at most
$1+2\cdot2+3\cdot4+4\cdot8=49$. Locally assign one common code
to exactly the four acquired trees (LTR.23), and a distinct singleton
code to every other member of $\mathcal F_3$. No equality or identity
port is used: comparisons concern the already paid finite description.
Export that complete code and isolate every other field. On the
four-source code use $RRL$; singleton codes need zero Reads. This
common reader is correct on all $\mathcal F_3$, all late targets
and all counts. The right-subtree count is $1446$, from
$f_0=2$, $f_{j+1}=2+f_j^2$; this deliberately large supporting
encoder has $1443$ attained codes. It is not an upper-bound competitor.
$\square$

The counterexample refutes replacement by a prefix query on an
unchanged attained fiber. It does not prove that a globally different
prefix-only partition requires more codes, refute the published
known-menu worst-budget projection of AAR Theorem 16.4, or determine
$M_1(3)$. Projecting the correlated off-path subtrees to fixed
completions can change $E$ and destroy this fiber, so such a projection
does not establish a fiberwise reduction.

## 8. Mathematical suppliers, primary methods and recovery boundary

**Source correspondence 8.1 (published native suppliers and their limits).**
All repository references in this volume use the revision in Convention
1.1. AAR Definitions 13.1 and 16.1 have the exact stationary family
and four-reply port used here, but declare the target or menu before
acquisition. AAR Theorems 12.3 and 12.6 supply the trajectory factor
and fixed-menu minimum retained alphabet; Theorems 13.8 and 16.8
supply singleton and joint acquisition prices. They do not supply
the one common pre-request code plus one late Read. AAR Theorem
16.14 explicitly retains the later-unknown-menu boundary. Theorem
16.4 compares acquisition minima through canonical completions;
it does not preserve every arbitrary pre-existing encoder fiber.
The descriptor collision in AAR Proposition 13.3 also remains:
at $p=RLL$, the different blocking positions of
$\langle\alpha,\beta\rangle$ and
$\langle\alpha,\langle\alpha,\alpha\rangle\rangle$ have the same
factor $(3,0)$. Predictor sufficiency is not full descriptor recovery.

[Native Birth Provenance, Assumption 14.1 and Theorem 14.4](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md#14-paid-common-start-preparation-and-code-only-two-phase-feasibility)
supplies the paid common-start, code-only, stationary two-phase
discipline for its full predecessor-fiber task and coupled finite
tables. That task uses an authenticated image source, a known row
and fixed whole-predecessor output. Its attained chart and budget
correspondence are not a late-target future-trajectory optimizer.
The service assumptions are reused as service assumptions, rather
than attributed to an inferred physical implementation.

[Word Retention and Geometric Reaccess, Theorems 3.2 and 4.2](RECURSIVE_RELATIONAL_OBSERVATION_WORD_RETENTION_AND_GEOMETRIC_REACCESS.md#4-固定编码器的准确调用与加权价格)
classifies all literals on a selected comb family as equality tests
and prices a fixed geometric target on fixed retained fibers. Its
constant-word retention and source family differ from $\mathcal F_D$.
AAR Definition 10.1 instead concerns an unknown lag on an updated
version after retention. Neither operation is substituted for the
stationary late-task interface. The guarded same-origin future law
and paid declared-task acquisition in
[Sparse Literal History Transport, §§35--38](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md)
are suppliers for Convention 2.1, not a target-blind optimum.

The no-later-Read universal property of
[TargetFamilyMinimalQuotient](../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean)
is `target_family_minimal_quotient`, a joint kernel quotient.
It supplies a static sufficiency relation, rather than legal one-query
experiments on a common retained fiber. Reading these declarations
does not certify a new compiled application.

**Source correspondence 8.2 (primary intermediate methods).** The
literature status of the native bounds and counterexamples is
`repo-derived`: their ordinary proofs are §§3--7. The following
primary interfaces are `literature-attested` intermediate methods,
with the stated operation correspondence. No worldwide originality
or exhaustive absence claim is made.

Miltersen, Nisan, Safra and Wigderson,
[*On Data Structures and Asymmetric Communication Complexity*,
BRICS RS-94-41, §1.1, printed pp. 1--2](https://www.brics.dk/RS/94/41/BRICS-RS-94-41.pdf),
defines static data $d$, a later query $q$, preprocessing $\phi(d)$
into $s$ cells of $b$ bits and a $t$-probe reader. Its forward
communication simulation sends cell addresses and cell contents.
Here a source holder first exports $E(t)$ before $p$ exists, and
the later requester sends $w(E,D,p)$ and receives a native reply.
Our fresh reply is constrained to $r_t(w)$, and cannot be an arbitrary
computed cell or target value. All of $E$ is available as local
input after handoff. Address length and installed state are separate
resources. Thus the classical framework motivates the partition
analysis, but its unrestricted communication converses or general
data-structure bounds do not implement a native reader here.

Gál and Miltersen,
[*The Cell Probe Complexity of Succinct Data Structures*, BRICS
RS-03-44, §1 and §3, printed pp. 1--5 and 11](https://www.brics.dk/RS/03/44/BRICS-RS-03-44.pdf),
defines systematic representations $\phi(x)=x\cdot\phi^{\ast}(x)$
with an index accompanying the input, and discusses source-dependent
help bits in its prefix-sum argument. Our retained code has the
role of an index while the original source remains readable, but
it is prepared by paid native Reads and probed through constructors,
not through arbitrary representation bits. The source-dependent
index may correlate coordinates; this is the reason to preserve
joint fibers. Neither its parity lower bound nor the separately
cited help-bit theorem is a premise of Lemma 4.3. That lemma proves
the needed weighted dependence bound for the actual five native
gadgets. The box-cover upper in Theorem 6.3 uses the elementary
probabilistic method and union bound, with its complete argument
given there, not a claimed new general covering method.

**Proposition 8.3 (what spatial structure plus one Read recovers).**
Under the paid interface, Theorem 3.4 turns a target-blind retained
relation and one same-source observation into the exact selected
temporal trajectory for every late spatial address. That trajectory
and its factor determine each other on attained inputs. The code
alone need not predict the trajectory, identify the first leaf,
or recover the whole tree or spatial boundary.

Proof. The construction's selector and decoder give the factor
by Theorem 3.3; Convention 2.1 gives the attained bijection with
the trajectory. At $D=2$ its code $0$ contains both right-root
leaves alpha and beta, with different trajectories at $R$. Thus
the code alone is not sufficient even for that target. AAR's
descriptor collision shows why the factor need not identify its
blocking position, and branch factors ignore arbitrary descendants.
An exact prediction at supplied $k$ produces no authentic Read
event on $\rho^k t$; source continuity and the authentic count remain
assumptions. $\square$

**Open problem 8.4 (the unchanged full-family optimum).** Determine
$M_1(D)$ for arbitrary finite $D$ by a non-tautological native
structural characterization with an exact recurrence, or close the
alphabet-scale gap with rigorously matching bounds. In particular,
determine the sharp leading alphabet rate, including whether

$$
\lim_{D\to\infty}\frac{\log_2 M_1(D)}{2^{D-2}}
$$

exists and what its value is. The present bounds place any such
limit between $\log_2(7/5)$ and $1$. The exact value at $D=3$
also remains between $3$ and $4$.

The missing relation is a global coloring or optimal-fiber theorem
on the full variable-shape family that preserves all late targets
and all native words on each jointly attained code fiber. Lemma 2.2
names that interface but is only a generic partition criterion.
The exact restricted theorem does not extend its box fibers to the
whole family; Theorem 7.1 excludes a general unchanged-fiber
prefix reduction, and $C_2=3$ excludes multiplying independent
local minimum code counts. Finite source-table enumeration, small
depth checks and selected scaffold families do not discharge this
general obligation. The retained-bit order is a partial result
within the full minimal-relations and mutual-recovery programme,
whose physical realization and broader recovery questions remain
open as well.

## 追加锚（本行以下为增补区）

## 9. One common temporal query versus a supplied target and count

**Convention 9.1 (source and evidence boundary).** Sections 9–14 use
public repository suppliers at revision
`17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b`. Their results below are
ordinary mathematics, without new Lean certification. The source,
substitution, four-reply literal port, paid complete handoff and
source-independent request family are exactly Definitions 1.2–1.4.
In particular, one actual initial source remains stationary; the
expressions involving its substituted versions are predictions, not
additional observations or updates of that source.

Write $\Gamma_q=G_q$ for the credited factor in Convention 2.1.
Its all-count decoder and the equivalence of factors and trajectories
are reused from [AAR, Definition 12.2, Theorem 12.3 and Proposition
13.3][CombAAR]. The canonical normalization and paid boundary scan
below are reused from [FMR, Definition 2.1, Lemma 2.2 and Theorems
2.3–2.5][CombFMR] and [RRN, §7][CombRRN].

**Definition 9.2 (two query/output contracts).** Call the original
contract of Definition 1.4 $\mathsf U$. For each complete attained
code $e$ and later public target $p$, it selects zero Reads or one
word $w(e,D,p)$ before receiving any count. After that observation
it must answer every subsequently supplied authentic $k\ge0$.

Define a relaxed comparison task $\mathsf P$ with exactly the same
source, preparation, handoff and code accounting. After export it
receives the pair $(p,k)$, with $p\in\mathcal P_D$ and authentic
$k\ge0$. It selects zero Reads or one word $w(e,D,p,k)$ and need
output only $r_{\rho^k t}(p)$ for that supplied count. It need not
leave a predictor correct at other counts. Both tasks require one
common preparation, independent of both $p$ and $k$, correct for
every $t\in\mathcal F_D$ and every allowed later input. Neither
permits access to the preparation transcript.

For a fixed fiber and target, the relevant distinction is

$$
\begin{aligned}
\mathsf U &: \quad \exists w\ \forall k\ge0\ \exists\delta_k
 \ \forall t\text{ in the fiber},\quad
 \delta_k(r_t(w))=r_{\rho^k t}(p),\\
\mathsf P &: \quad \forall k\ge0\ \exists w_k\ \exists\delta_k
 \ \forall t\text{ in the fiber},\quad
 \delta_k(r_t(w_k))=r_{\rho^k t}(p).
\end{aligned}
\tag{LTR.24}
$$

Here a constant experiment represents zero Reads. In $\mathsf U$
the decoder family has the effective factor realization (LTR.4);
the query itself cannot depend on $k$. Revealing a count early while
still requiring the resulting predictor to work for all counts does
not change the common-query requirement.

**Definition 9.3 (canonical states and prescribed refinement).** Set
$C_0=\langle\alpha,\alpha\rangle$ and use the credited canonical
sets and their attained sizes

$$
S_1=\{\alpha,\beta,C_0\},\qquad
S_{a+1}=\{\alpha,\beta\}\sqcup(S_a\times S_a),\qquad
s_a=|S_a|,\quad s_1=3,\quad s_{a+1}=2+s_a^2.
\tag{LTR.25}
$$

A pair in this disjoint union means its actual ordered constructor.
For a right subtree $v$ of height at most $D$, $\pi_D(v)$ keeps
all reached constructors through depth $D-1$ and replaces each
branch at that depth by $C_0$. It fixes $S_D$ and preserves
$r_v(q)$ and $\Gamma_q(v)$ for all $|q|\le D-1$.

For two complete acquired exports $E,E^\circ$ on the whole
$\mathcal F_D$, say that $E$ **refines** $E^\circ$ if a public
finite map $g$ satisfies $E^\circ=g\circ E$ on every source.
Thus a refinement may split an old fiber but cannot merge two old
names. This is a restriction on the assembly mechanism, not on the
definition of $M_1(D)$.

**Definition 9.4 (even combs on an actual public scaffold).** Define

$$
T_0=\alpha,\qquad T_{j+1}=\langle T_j,\alpha\rangle.
$$

Fix integers $m\ge1$ and $h\ge0$, and put

$$
d=6m-2,\qquad n=2^h,\qquad D=h+d,\qquad
\mathcal C_m=\{T_{2r}:0\le r<3m\}\subseteq S_d.
\tag{LTR.26}
$$

The heights of these $3m$ distinct trees are $0,2,\ldots,d$;
all their leaves are alpha. Let $\operatorname{Sc}_0(x)=x$ and
recursively pair the first and second halves to form the perfect
ordered height-$h$ scaffold $\operatorname{Sc}_h$. Its public
frontier words $a_1,\ldots,a_n$ all have length $h$. Put

$$
\begin{aligned}
G_{m,h}&=\operatorname{Sc}_h(\mathcal C_m^n)\subseteq S_D,\\
X_{m,h}&=\{\langle\alpha,u\rangle:u\in G_{m,h}\}
                  \subseteq\mathcal F_D.
\end{aligned}
\tag{LTR.27}
$$

The scaffold map is injective: its ordered, actually present frontier
subtrees recover its entries. Consequently $|G_{m,h}|=(3m)^n$.
This recovery is a mathematical identification, not a supplied subtree
or source-identity port. At every actual occurrence, homomorphic
substitution gives

$$
r_{\rho^k\langle\alpha,\operatorname{Sc}_h(u_1,\ldots,u_n)\rangle}
 (Ra_iq)=r_{\rho^k u_i}(q).
\tag{LTR.28}
$$

Every operational use of the right-hand side below submits the entire
original-root word on the left. The presence premise is exactly that
of `NativeDepthPatterns.original_present_transport`; it is never
asserted at an absent occurrence.

## 10. All-target pointwise recovery with a single slice name

**Lemma 10.1 (even-comb pointwise query).** For every $m\ge1$,
$d=6m-2$, word $q$ with $|q|\le d-1$, and integer $k\ge0$,
there is a zero-Read constant or a literal $L^a$, $0\le a\le d-1$,
whose reply on $T_j$, $j\in\{0,2,\ldots,d\}$, determines
$r_{\rho^k T_j}(q)$. The choice and decoder are effective functions
of $m,q,k$, independent of $j$.

**Proof.** First let $q=L^\ell$, including $\ell=0$. The credited
factor formula gives

$$
\Gamma_{L^\ell}(T_j)=
\begin{cases}
(0,0),&j>\ell,\\
(2,1),&j=\ell,\\
(\ell-j+2,0),&j<\ell.
\end{cases}
\tag{LTR.29}
$$

At $k=0$, query $L^\ell$ and return its actual reply. At $k\ge1$
put $a=\ell+1-k$. If $a<0$, (LTR.29) and (LTR.4) make every
answer branch. If $a\ge0$, query $L^a$ and decode

$$
\mathsf{absent}\mapsto\mathsf{absent},\qquad
\alpha\mapsto\beta,\qquad
\mathsf{branch}\mapsto\mathsf{branch}.
\tag{LTR.30}
$$

Indeed these replies mean respectively $j<a,j=a,j>a$. In the
first case $k<\ell-j+1$ and the predicted reply is absent. In the
second $k=\ell-j+1$, giving beta, including $j=\ell,k=1$.
In the third it is branch; if $j=\ell$ then $k\ge2$, and if
$j>\ell$ it was a branch already. Also $a\le\ell\le d-1$.

Otherwise write uniquely $q=L^rRu$. Define

$$
B=\#L(u)+2\#R(u)+2,\qquad
c=\mathbf1_{q\text{ ends in }R}.
$$

The first alpha reached is at $L^j$ when $j\le r$, and at
$L^rR$ when $j>r$. Hence, including $u=\varepsilon$,

$$
\Gamma_q(T_j)=
\begin{cases}
(B+r+2-j,c),&j\le r,\\
(B,c),&j>r.
\end{cases}
\tag{LTR.31}
$$

As the allowed even $j$ increase, the distinct first coordinates
$b$ strictly decrease in gaps of at least two, followed by the
possible final plateau $b=B$. The gap immediately before that
plateau is two or three. For fixed $k$, (LTR.4) gives branch at
$b\le k$, beta at $b=k+1$, alpha at $b=k+2$ if $c=1$, and
absent at the remaining larger $b$. Two distinct exceptional levels
would differ by one, which the gap excludes. Thus the outputs, in
increasing $j$ order, consist of an initial absent interval, at most
one exceptional alpha-or-beta level, and a final branch interval.
An interval may be empty; an exceptional plateau can have several
$j$ but only one $b$ and one output.

If the exceptional level is a nonplateau even $j_*$, query
$L^{j_*}$. Its absent, alpha and branch replies correspond exactly
to $j<j_*,j=j_*,j>j_*$. Decode them as absent, the exceptional
output, and branch. Here $j_*\le r\le d-2$. If the exception is
the final plateau $j>r$, query $L^r$: absent or alpha means
$j\le r$ and has output absent, whereas branch means the plateau
and has its exceptional output. This query also has $r\le d-2$.

If there is no exceptional level and both output intervals are
nonempty, take an odd $a$ strictly between the last absent even
length and the first branch even length. Its possible replies are
absent and branch, with exactly those outputs. One can take one
more than the last absent length, so $a\le d-1$. A constant
output uses zero Reads. These alternatives exhaust all cases and
are effective finite comparisons. Every $b\le2d$, so $k\ge2d$
is constant branch; a finite installed table for $k<2d$ suffices.
The proof covers every word $q$, including initially absent targets,
rather than just the pure-left test targets. $\square$

**Corollary 10.2 (pointwise recovery on the whole scaffold slice).**
Under the explicit promise $t\in X_{m,h}$, the constant export
with no preparation Reads serves $\mathsf P$ for every original
target and count, with at most one actual Read of length at most
$D$.

**Proof.** Write $p=Rq$. If $|q|<h$, it ends at a scaffold branch
which remains branch. Otherwise $q=a_iq'$ for a unique $i$, with
$|q'|\le d-1$. Apply Lemma 10.1 to $q',k$ and implement its
query as $Ra_iL^a$. Its length is $1+h+a\le D$, and (LTR.28)
gives its required prediction. Only this one local response is
acquired. The promise in this corollary is not supplied for free in
the full-family construction below. $\square$

## 11. All-count slice complexity against arbitrary original queries

**Theorem 11.1 (exact attained names on the slice).** Every preparation
and reader correct for $\mathsf U$ on the full $\mathcal F_D$ has
at least $m^n$ distinct complete attained names on $X_{m,h}$.
The lower bound also holds for procedures promised only this slice.
It permits arbitrary correlated code fibers, different off-target
queries for different requests, and every finite original-root word.
There is an attaining $m^n$-name reader on the slice which extends
to a lawful reader on all of $\mathcal F_D$.

**Proof of the lower bound.** Every initial source in $X_{m,h}$
has only alpha leaves. Therefore every finite original-root word,
including a wrapper word, an off-target word or an overlong word,
has at most the three replies absent, alpha and branch across this
slice. This assertion concerns the actual stationary source, not
its later substituted version.

For coordinate $i$ take the permitted target
$p_i=Ra_iL^{d-1}$, of length exactly $D$. Its local factors are

$$
\Gamma_{L^{d-1}}(T_j)=
\begin{cases}
(d+1-j,0),&j\in\{0,2,\ldots,d-2\},\\
(0,0),&j=d.
\end{cases}
\tag{LTR.32}
$$

These $3m$ factors are pairwise distinct. By the credited
factor/trajectory equivalence they demand different complete
trajectories, not merely different descriptors of the source.

Let $B$ be the set of slice tuples receiving one complete name.
At $p_i$ the decision to stop or the one literal query is fixed
throughout $B$ before every count. Equal replies must give the
same entire trajectory, and hence the same $j_i$. There are at
most three replies, so its coordinate projection has size at most
three; a zero-Read branch has size at most one. It follows that

$$
|B|\le\prod_{i=1}^n|\operatorname{pr}_i B|\le3^n.
\tag{LTR.33}
$$

Only containment of a relation in the product of its projections is
used here. No projection is assumed to be an admissible fiber, no
independence is inferred, and no donor is moved into the requested
coordinate. Partitioning $(3m)^n$ actual sources into fibers of
size at most $3^n$ requires at least $m^n$ names.

**Proof of attainment.** Write each local even height uniquely as
$j_i=6g_i+2z_i$, with $0\le g_i<m$ and $z_i\in\{0,1,2\}$.
Export the vector $(g_1,\ldots,g_n)$. If $p$ stops above the
frontier it is constant branch. Otherwise let $p=Ra_iq'$ and
query the single original-root word

$$
Ra_iL^{6g_i+2}.
\tag{LTR.34}
$$

For the three possible heights $6g_i,6g_i+2,6g_i+4$, its replies
are respectively absent, alpha and branch. Thus it identifies the
local height and its full $\Gamma_{q'}$ from the installed table.
Use (LTR.4) for every later authentic count. Its length is at most
$1+h+6(m-1)+2=D-1$. All $m^n$ vectors are attained. Section 12
gives the paid extension to every actual source. The three-height
median query itself is the credited ingredient of [COK, Proposition
23.3][CombCOK]; the reply-range projection argument is also used in
[RCE, Theorem 8.2][CombRCE]. The new conclusion here is their exact
all-target quantifier separation and prescribed full-family refinement
cost. $\square$

## 12. Exact full-family refinement premium and paid acquisition

**Definition 12.1 (the prescribed pointwise export).** Use disjoint
names $\star$ and $[u]$ for $u\in S_D\setminus G_{m,h}$.
On every actual $t=\langle\alpha,v\rangle\in\mathcal F_D$ set

$$
E^\circ(t)=
\begin{cases}
\star,&\pi_D(v)\in G_{m,h},\\
[\pi_D(v)],&\pi_D(v)\notin G_{m,h}.
\end{cases}
\tag{LTR.35}
$$

A name $[u]$ fixes one canonical state, not necessarily one actual
source. Its full inverse image may contain different terminal labels
and shapes hidden below the queried boundary. They have the same
requested factors by canonicalization.

**Theorem 12.2 (full-family exact refinement).** For every $m\ge1$
and $h\ge0$, at $D=h+6m-2$ the prescribed complete export
$E^\circ$ is lawfully acquired and correct for $\mathsf P$ on the
entire original $\mathcal F_D$, with exactly

$$
N_{\mathsf P}=s_D-(3m)^n+1
\tag{LTR.36}
$$

attained names. Among all preparations and readers correct for the
original $\mathsf U$ on that full family and refining this same
$E^\circ$, the exact minimum attained alphabet is

$$
N_{\mathsf U\mid E^\circ}=s_D-(3m)^n+m^n.
\tag{LTR.37}
$$

Thus the exact additional-name premium for this prescribed refinement
is $m^n-1$. Both attaining constructions use, on every actual source,
exactly

$$
T_{\rm prep}=2^D-1,\qquad
Q_{\rm prep}=D,\qquad
A_{\rm prep}=(D-1)2^D+1
\tag{LTR.38}
$$

charged preparation Reads, maximum submitted length, and submitted
address letters. Their later readers use at most one original-root
Read: length at most $D$ for $\mathsf P$ and at most $D-1$ for
$\mathsf U$. These are attaining sufficient costs, not preparation
optima.

**Proof.** First, each $u\in S_D$ is an actual right subtree in
the family and is fixed by $\pi_D$. Hence all names in (LTR.35)
are attained, giving (LTR.36).

For the original reader, replace $\star$ by the $m^n$ vector
names of Theorem 11.1 on its canonical scaffold image and retain
each name $[u]$ elsewhere. Explicitly, when $\pi_D(v)\in G_{m,h}$,
its unique ordered comb entries determine $(g_i)$ as in that theorem.
This defines a refinement $E^*$: map every vector name to $\star$
and every other name to itself. Its range has exactly (LTR.37)
elements.

Conversely, any full-family $\mathsf U$ refinement $E$ must have
at least $m^n$ distinct names on the actual subset $X_{m,h}$ by
Theorem 11.1. Each of the other $s_D-(3m)^n$ canonical states
has its own distinct attained $E^\circ$ name and therefore demands
at least one disjoint $E$ name. These names cannot be shared with
$X_{m,h}$. This proves the lower bound (LTR.37) even if the
refinement splits noncanonical inverse images in arbitrary ways.

Here is an actual preparation for each displayed export. Before
receiving $p$ or $k$, submit all words $Rw$ with $|w|\le D-1$
in a fixed public order, including words returning absent. This is
the credited full boundary scan. Its acquired constructor array
determines $\pi_D(v)$: stop at every reached labelled leaf, recurse
through earlier branches, and put $C_0$ at each branch at cutoff
depth $D-1$. A finite common table computes either $E^\circ$ or
$E^*$ from this acquired state. Membership in the scaffold and the
comb heights are computed from this array, never obtained from an
identity, equality or subtree port. Every comparison is a local
comparison of already acquired finite descriptions.

The table can be generated effectively by enumerating the finite
$S_D$, the fixed ordered scaffold and its comb tuples. For each
fixed installed integer $m$, one procedure works for every public
$D\ge6m-2$ by taking $h=D-(6m-2)$. At smaller depths the same
procedure may use one name for each canonical state. It depends on
public $D$ and fixed installed code, never on a later target or count.
All its loops and tables are finite, so it terminates on every actual
source. This specifies an effective acquisition, rather than assigning
free colors to an unknown source.

A later name $[u]$ fixes every requested factor, so both readers
use zero Reads there. On $\star$, use Corollary 10.2's pointwise
reader. On a vector name, use (LTR.34)'s count-blind reader and
then the all-count factor decoder. For $q$ stopping above the
frontier, both output constant branch. Every other original target
enters one unique actual scaffold occurrence. These cases exhaust
all $p\in\mathcal P_D$.

To check correctness beyond the canonical sources, let
$u=\pi_D(v)\in G_{m,h}$. Canonicalization preserves all constructors
through relative depth $D-1$. The scaffold roots at depth $h$ are
therefore actually present in $v$, and every selected relative query
has length at most $D-1$. Its reply on $v$ equals its reply on $u$.
The requested $\Gamma_q$ also agrees, including when $q$ is
initially absent and including any terminal labels not retained by
$\pi_D$. Thus exactly the same installed query and decoder work
on the entire actual inverse image of the canonical name. Transport
at a scaffold root is lawful because that root is present; no absent
address is treated as a supplied subtree. On a name $[u]$, factor
preservation alone proves correctness with zero Reads. This proves
both whole-family attainments with the same stationary actual source.

There are $\sum_{l=0}^{D-1}2^l=2^D-1$ scan words. They include
length-$D$ original-root words, whether present or absent, and their
length sum is

$$
\sum_{l=0}^{D-1}(l+1)2^l=(D-1)2^D+1.
$$

This proves every equality in (LTR.38). The late length bounds were
proved in Corollary 10.2 and Theorem 11.1.

Finally export only a fixed-width encoding of the displayed complete
name. Use public allocation, the fixed scan schedule and padded finite
table selection. The separately paid handoff and access-isolation
services of Assumption 1.3 make all arrays, acquired shape information,
selectors, operands, buffers, lengths, transcripts, control, allocation
and accessible timing inaccessible except for functions of this name
and public inputs. If any additional acquired distinction survives,
it belongs in the alphabet and these counts would no longer describe
that export. The services are declared premises, not inferred physical
erasure or entry operations. This completes the paid complete-code
construction. $\square$

**Corollary 12.3 (an unbounded prescribed-code premium).** For fixed
$m=2$, $d=10$ and every $h\ge0$, the one special name of $E^\circ$
requires exactly $2^{2^h}$ names in an original-task refinement.
The full-family attained alphabets are respectively

$$
s_{h+10}-6^{2^h}+1,\qquad
s_{h+10}-6^{2^h}+2^{2^h},
\tag{LTR.39}
$$

and their exact additive difference is $2^{2^h}-1$.

**Proof.** Substitute $m=2,n=2^h$ in Theorem 12.2. $\square$

This difference counts additional attained names in the full alphabet.
It is not a multiplicative ratio or a bit premium for that whole
alphabet. The original-task lower on $X_{m,h}$ quantifies over all
competitors; adding the outside-state names requires precisely the
refinement hypothesis. A globally recolored full-family export may
merge those old outside names, so (LTR.37) is not a lower bound for
unrestricted $M_1(D)$ and determines no new optimum or rate endpoint.

## 13. The failed assembly mechanism and exact supplier correspondence

**Proposition 13.1 (pointwise witnesses do not assemble on the same
export).** Consider the proposed mechanism which, on a prescribed
paid complete export, verifies a one-query solution separately for
every $(p,k)$ and then asserts a query-before-count solution for the
same export without splitting names. This mechanism is false on
actual full-family native sources. More generally, for the export
$E^\circ$ at fixed $m\ge2$, any repair limited to refinements
must pay the exact additional alphabet (LTR.37).

**Proof.** Theorem 12.2 establishes every pointwise premise on the
full family for $E^\circ$, including all original targets, all
counts, paid acquisition and the same stationary source. Its original
all-count refinements require $m^n>1$ names over the one special
fiber, with the stated exact full-family premium. This refutes the
asserted assembly on unchanged fibers and proves the refinement
claim. $\square$

The consumer of this obstruction is a transfer based on separately
synthesized count-specific controllers or separately chosen task
extensions. Such a transfer must instead exhibit one common literal
witness determining the whole temporal factor on each attained fiber,
as in Lemma 2.2, or count a lawful refinement or recoloring. This is
a necessary operational distinction, not an assertion that either of
the following suppliers made the rejected claim.

**Source correspondence 13.2 (fixed-tree and finite-controller
suppliers).** The following table states their exact input/output
correspondence at the pinned revision. Reading declarations and their
owning narratives supplies no new compiled application.

| Supplier | Verified interface and transfer boundary |
| --- | --- |
| [FixedTreeCommonExtension][CombFT], with its [owning Scribe][CombFTB] | A fixed finite `Full` tree has disjoint sibling coordinate sets, finite nonempty alphabets, nonempty joint promise and one joint task $f$. Local leaf implementations receive coordinate values; internal implementations receive full child-message tuples. Common-total-extension capacity vectors and reachable-message vectors have the same upward closure and attained minima for coordinatewise monotone costs. Its canonical extension uses noncomputable representative choice. The root `read` is a decoder, not a charged literal query. Actual comb coordinates here must be acquired, and separate tasks $f_{p,k}$ do not supply a single count-blind literal or preserve a shared export. Applying it to the joint trajectory task keeps that operational obligation. |
| [NativeLiteralMoore][CombMoore], `NativeLiteralFeasible` and `finite_literal_synthesis`, with its [owning Scribe][CombMooreB] | Fix a prefix-free cut $P$, $C=\operatorname{canonicalRow}P(\operatorname{substitution}u_0)$ and budgets $r,K\ge1,q,\ell$. Feasibility supplies `code : ImageValues C → Q ⊕ H` on the entire actual predecessor fiber; execution queries the stationary actual `substitution u`, and outputs the whole predecessor row `canonicalRow P u`. Budgets count attained initial code names, installed states, actual calls and the same trace's literal letters. The finite synthesis equivalence may reselect the encoder/controller. Acquisition of the actual `ImageValues`, paid export/isolation and authenticated one-update continuity remain supplied premises. This does not supply the original late $p$, all-authentic-$k$ output or a universal one-call bridge. No claim that these combs are that predecessor fiber is used. |

In both cases a finite source-independent installed table is permissible;
an unknown actual coordinate assignment, image source or chosen
representative is not thereby acquired for free. All original targets
here refer to one actual source and one shared acquired export.
No separate optimization at different cuts or counts can discard that
common realization requirement.

**Convention 13.3 (resource coordinates and recovery scope).** The
complete retained alphabet in (LTR.36) or (LTR.37) includes its
special-versus-other selector and every surviving acquired source
distinction. Fixed-width naming uses $\lceil\log_2 N\rceil$ bits
for its respective attained alphabet $N$; unused bit patterns do not
add attained names. The scan computes shape and group indices, but
only the counted name survives.

Installed table generation and size, preparation computation/control
and temporary storage, submitted-address construction, post-request
workspace, final predictor size, count representation, entry,
authentication, source continuity, handoff/isolation and physical time
are separate resources. The original reader can keep the factor
$(b,c)$ with $0\le b\le2D$, using at most
$\lceil\log_2(2D+1)\rceil+1$ bits separately from the retained
name. No small installation, preparation-work or total-efficiency
bound is asserted. The preparation Reads and literal lengths are
exactly those specified, not a preservation of an arbitrary rival's
acquisition cost.

What the boundary observer recovers is the complete selected temporal
trajectory via one actually obtained native reply and the retained
relation. The relaxed reader instead recovers just the supplied-count
answer. Neither reader acquires a substituted source, an unknown age,
a hidden history or physical space and time. Source continuity and
authentic count input remain separately supplied services.

## 14. Attribution, bounded checks and the unchanged global obligation

**Convention 14.1 (attribution of ingredients and result).** The
even-comb quantifier separation, exact prescribed refinement count
and its paid full-family realization in §§9–13 are `repo-derived`
ordinary deductions. The temporal factor, canonicalization, paid scan,
reply-range projection argument and median-comb query are credited
suppliers, as identified above. In particular the range argument of
RCE Theorem 8.2 and the triple identification of COK Proposition 23.3
are not asserted as new general methods.

Kowshik and Kumar, *Optimal Function Computation in Directed and
Undirected Graphs*, [arXiv:1105.0240v2, §III-B, Lemma 2 and
Example 1][CombKK], give a `literature-attested` zero-error comparison.
For arbitrary joint support, their cut condition separates two
assignments in $S$ whenever the same complementary assignment makes
both positive-probability and their function values different.
Example 1 on diagonal support explicitly couples the encoders;
separate average-description minimization is stated with full-support
probabilities. These support-sensitive feasibility distinctions do
not implement a paid literal acquisition or exchange the count/query
quantifiers in (LTR.24).

Garg, He, Li, Papakonstantinou and Yang, *Systematic Data Structure
Lower Bounds via the Query-with-Sketch Model*, [arXiv:2609.18024v1,
Definition 2.1][CombQWS], give a `literature-attested` comparison in
which an input-dependent sketch precedes probes chosen from the
transcript, and repeated probes count with multiplicity. Our export
has that sketch role, but must itself be acquired through paid native
Reads; a native reply is a constrained constructor observation, not
an arbitrary stored value. No min-entropy lifting theorem or general
data-structure lower bound is imported. These inspected sources
supply neither the specific theorem here nor an effective original
all-size cap. Their scope is bounded documentary comparison, without
an exhaustive literature or worldwide-originality assertion.

**Proposition 14.2 (bounded exact corroboration).** Direct recursive
actual-substitution readout on the combs gives the following finite
checks of Lemma 10.1. All listed target words have length at most
$d-1$, and counts range from zero through $2d$, inclusive.

| $m$ | $d$ | Target/count tables | Nonconstant tables | Actual readout/factor comparisons |
| --- | --- | --- | --- | --- |
| $1$ | $4$ | $135$ | $59$ | $405$ |
| $2$ | $10$ | $21483$ | $4583$ | $128898$ |

Every table factors through the specified zero-Read constant or one
literal $L^a$, $0\le a<d$. At $d=10$, the deepest-target factors
in increasing comb height are exactly

$$
(11,0),(9,0),(7,0),(5,0),(3,0),(0,0).
\tag{LTR.40}
$$

For $m=2,h=1,D=11$, all $36$ actual two-comb rows and all
$2047$ original targets give $73656$ factor comparisons at targets
entering a frontier block. The original triple-code reader's factor
agrees with direct (LTR.3) evaluation in every case; the remaining
$36$ root-location cases have constant factor $(0,0)$. Separately,
the pointwise reader at counts $0,1,2,5,22$ gives $368280$ output
comparisons, all agreeing with actual original-root substitution
readout.

**Verification scope.** The actual readout computation recursively
replaces an alpha by beta and a beta by $\langle\beta,\alpha\rangle$
when a positive substitution count reaches a leaf, and otherwise
traverses the original ordered branch. It does not use the factor
formula to compute the actual reply. Separately compute (LTR.3) and
(LTR.4), and check equality and the selected literal's reply partition
on each finite list above. The scaffold checks use the actual wrapper
and full root-prefixed literal addresses. These are bounded exact
checks only; the universal assertions for every $m,h,q,k$ and every
competing fiber rest on the ordinary proofs, not extrapolation or an
empirical convergence claim.

**Convention 14.3 (credited native frontier).** With the existing
normalization $\lambda=\lim_{D\to\infty}2^{-D}\log_2M_1(D)$,
[FMR][CombFMR] supplies existence of this limit. [NCE, §§13–19,
in particular Theorems 17.1–17.2][CombNCE] supplies the credited
positive asymmetric depth-three law with exact pressure
$3038031/7792603$, and hence

$$
M_1(D)\ge
\left\lceil(7792603/3038031)^{2^{D-3}}\right\rceil
\quad(D\ge3),\qquad
\frac{\log_2(7792603/3038031)}8\le\lambda<\frac3{16}.
\tag{LTR.41}
$$

The upper endpoint and $M_1(3)=4$ are credited to [D3, Theorems
2.3 and 4.1][CombD3]; the same NCE result gives $M_1(6)\ge1874$.
These credited results answer the existence and depth-three subquestions
in Open problem 8.4. Its displayed alternative normalization is $4\lambda$.
The sharp rate and general exact memory question remain open. No new
endpoint, fixed-law pressure result or optimized recoloring bound is
provided by (LTR.37).

The conditional-owner, component and forest results of [COK,
§§18–25][CombCOK], [OCC, §§10–17][CombOCC] and [GDB,
§§20–25][CombGDB] retain their declared matching-population,
augmented-descriptor and specified-certificate scopes. None is an
unrestricted optimizer-cofinality obstruction. [NPC][CombNPC],
[CBN][CombCBN] and [RRN][CombRRN] retain actual common sources,
shared coordinates, guards and each full joint block potential once;
their semantic completeness and exact representations give no
uniform finite-length cutoff.

**Open problem 14.4 (unchanged effective all-size bridge).** For
fixed $d$, let $S_d$, complete native donor templates $\Theta$,
their solution sets $C_\Theta\subseteq S_d^N$, joint cover counts
$K_d(N)$ and pressure rate $\sigma_d$ be exactly those of
[NPC, §§1–8][CombNPC] and FMR. Construct a total computable
verifier $V(d,\mu,C,\pi)$ on rational probability laws $\mu$ on
the full $S_d$, rational $C>0$ and finite certificates $\pi$,
whose acceptance implies

$$
\forall N\ge1\ \forall\Theta,\qquad
\sum_{x\in C_\Theta}\prod_{i=1}^N\mu(x_i)\le C^N,
\tag{LTR.42}
$$

and prove optimizer-cofinality: for every $d$ and rational
$\epsilon>0$, some accepted rational label has
$-\log_2C>\sigma_d-\epsilon$. Equivalently useful here would
be a proved uniform effective length error
$\eta_d(N)\to0$, with computable evaluation and a computable
convergence modulus in $d$ and the requested accuracy, satisfying

$$
\sigma_d\ge\frac{\log_2K_d(N)}N-\eta_d(N).
\tag{LTR.43}
$$

Together with the credited depth-tail bound either route would give
the required terminating two-sided approximation of the same original
$\lambda$. Neither route is established here. In particular the
general equality between the optimized conditional-owner envelope
$a_d$ and $b_d=\min_\mu\beta_d(\mu)=2^{-\sigma_d}$, or a different
sound cofinal mechanism, remains unproved; rationalization alone
is already supplied by [NWO][CombNWO]. Shared-realization completion
and positive global-defect control near arbitrary correlated native
extremizers remain obligations. The exact obstruction above changes
one operational prerequisite for a controller/extension transfer:
it must preserve a common all-count witness, not only its separate
count-specific answers. It excludes neither lawful global recoloring
nor a different all-size certificate method. General exact $M_1(D)$,
sharp $\lambda$, effective all-size certification and the full
minimal-relations/internal-observer/mutual-recovery programme remain
unresolved.

[CombAAR]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[CombFMR]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[CombRRN]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REPRESENTATIVE_REPLY_NORMAL_FORM.md
[CombCOK]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONDITIONAL_OWNER_KERNELS.md
[CombRCE]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RECURSIVE_CERTIFICATE_ESCAPE.md
[CombFT]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/D5/S3/Observer/Separation/FixedTreeCommonExtension.lean
[CombFTB]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/Blueprint/D5/S3/Observer/Separation/FixedTreeCommonExtension.scribe.cs
[CombMoore]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.lean
[CombMooreB]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.scribe.cs
[CombKK]: https://arxiv.org/html/1105.0240v2
[CombQWS]: https://arxiv.org/html/2609.18024v1
[CombNCE]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[CombD3]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[CombOCC]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OWNER_COMPONENT_COMPLETION.md
[CombGDB]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GLOBAL_DEPENDENCE_BOUNDARIES.md
[CombNPC]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[CombCBN]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[CombNWO]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHT_OPTIMIZATION.md

## 追加锚（本行以下为增补区）

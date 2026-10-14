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

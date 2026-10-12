# Native first-disagreement frontiers and joint prefix cost

## 1. Entire original sources and the joint quantifiers

**Definition 1.1 (native source and complete retained input).** Use the
finite nonempty ordered native algebra of [NSF, Definition 1.1][NSF]:

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,
\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

An address is a word in $\{L,R\}^*$, with root $\varepsilon$.
Write $\operatorname{Pos}(u)$ for reached addresses, $u|_p$ for a
reached whole subtree, and $r_u(p)$ for its four-valued reply in
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.
Below a leaf all replies are absent.

For a finite prefix-free cut $A$, the complete row $R_A(u)$ consists
of its ordered reached set, the entire concrete exterior with numbered
holes at those reached addresses, and the full equality partition of
their whole subtrees. An erased hole's former value is not an exterior
label. The empty cut has exterior $u$ and no holes; the root cut has
one reached hole, one class and no concrete exterior node.

Fix a complete input $I=(P,R,H_0,H_{\rm rel},Q,N)$ as in
[ARH, Definitions 1.1–1.2 and Assumption 1.3][ARH]. Its entire fiber is

$$
\begin{aligned}
D(I)=\{u\in\mathcal T:\;&R_P(u)=R,\\
&r_{\rho^a u}(p)=c\quad\text{for every }(a,p,c)\in H_0,\\
&p\in\operatorname{Pos}(\rho^a u),\quad
 t\in\operatorname{Pos}(\rho^b u),\quad
 (\rho^a u)|_p\ \bowtie\ (\rho^b u)|_t
 \text{for every }(a,p,b,t,\bowtie)\in H_{\rm rel}\}.
\end{aligned}
\tag{NMF.1}
$$

Each sign $\bowtie\in\{=,\ne\}$ requires both endpoints reached.
The old exterior, old absent-address conditions, repeated old classes,
every old cross-class disequality, and all off-task records remain.
Every occurrence within one source uses that same whole source.
All listed epochs and native powers are supplied fixed numerals;
there is no bound on their values across inputs. If the presentation
also carries native image, preimage or rank conditions, they remain
conjuncts of its entire fiber, with their owning variables and guards.
They are not replaced by independent marginal choices.

The actual paid acquisition and complete-state factoring contract of
ARH Assumption 1.3 is a premise: the retained records are actual-epoch
records, the one register has authentically reached $\rho^N u$, and
the complete accessible state has exactly fiber (NMF.1). No additional
source-bearing field narrows that fiber. This premise is retained in
the examples below; a description of a fiber does not establish an
acquisition implementation.

**Definition 1.2 (whole row product and inclusive joint prefix).** Let
$B=(r_1,\ldots,r_m)$ be a finite list of distinct attained complete
$Q$-rows, with $m\ge2$. Set

$$
D_i=\{u\in D(I):R_Q(u)=r_i\},\qquad
\mathcal E_{I,B}=\prod_{i=1}^m D_i,
$$

and, for $h\in\mathbb N$, put

$$
J_B(h)\quad\Longleftrightarrow\quad
\exists\mathbf u=(u_1,\ldots,u_m)\in\mathcal E_{I,B}\quad
\forall p\in\{L,R\}^*\quad
|p|\le h\ \Longrightarrow
r_{u_1}(p)=\cdots=r_{u_m}(p).
\tag{NMF.2}
$$

The quantifier order is $\forall h\,\exists\mathbf u\,\forall p$ in
the all-depth alternative. Different rows index alternative original
sources; no common auxiliary valuation is imposed across rows.
Within each $u_i$, all its records, auxiliary values, images, ranks
and repeated references remain jointly constrained. The tuple may
change with $h$. A finite disequality is checked on each such finite
tuple; it need not persist at a limiting object.

[NIC, Theorem 4.3][NIC] supplies entire overlapping signed image
presentations for each $D_i$, with both original-source directions.
Its produced values satisfy the complete original row and records;
conversely it reconstructs each original source itself. These
presentations can substitute for $D_i$ in (NMF.2), but their parameters
are kept together within one image case. NSF supplies finite
feasibility and source reconstruction, not a stopping theorem for
$\forall h\,J_B(h)$.

## 2. The finite first-disagreement object

**Definition 2.1 (frontier and minimum mismatch depth).** For any
nonempty finite tuple $\mathbf u\in\mathcal T^m$, let
$v_{\mathbf u}(p)=(r_{u_i}(p))_{i=1}^m$. A vector is constant when all
its coordinates agree. Define

$$
\begin{aligned}
\Delta(\mathbf u)=\{p:\;&v_{\mathbf u}(p)\text{ is nonconstant, and}\\
&v_{\mathbf u}(q)\text{ is constant for every proper prefix }q\prec p\},\\
d(\mathbf u)&=\min\{|p|:p\in\Delta(\mathbf u)\},
\end{aligned}
\tag{NMF.3}
$$

with $\min\varnothing=\infty$. An unequal tuple means that its
components are not all identical. The definition does not assume
that its trees have the same shape or height.

**Theorem 2.2 (first-disagreement exactness).** For every nonempty
finite native tuple, $\Delta(\mathbf u)$ is finite and prefix-free.
It is empty exactly when all components are identical. For an unequal
tuple it is nonempty, and for every $h\in\mathbb N$,

$$
\forall |p|\le h\quad v_{\mathbf u}(p)\text{ is constant}
\quad\Longleftrightarrow\quad d(\mathbf u)>h.
\tag{NMF.4}
$$

Every frontier address is reached in every component. This last fact
does not replace four-reply agreement by a reached-only condition.

Proof. A nonconstant vector has at least one nonabsent coordinate,
so its address belongs to the finite union of the components' reached
sets. This proves finiteness. If $p\in\Delta$ and $p\prec t$, the
proper prefix $p$ of $t$ is already nonconstant, so $t\notin\Delta$.
Thus the frontier is prefix-free.

At any disagreement address choose its shortest nonconstant prefix.
This prefix belongs to $\Delta$ and is no deeper than that address.
Conversely every frontier address is a disagreement. These facts prove
(NMF.4) and show that an empty frontier means all replies agree at
every address. Equal four-reply maps reconstruct equal finite ordered
trees: equal roots are the same leaf or two branches whose respective
children have equal reply maps. Induction on their finite trees gives
equality. Hence precisely the identical tuples have empty frontier.

At a frontier root all coordinates are reached because every native
tree is nonempty. At a nonroot frontier address all proper ancestors
have constant vectors. None can be a common leaf or common absent
reply, since every extension of such an ancestor is absent in every
component. They are therefore common branches. Induction down that
path makes the frontier node reached in every component. A later
absent/reached discrepancy still has a first nonconstant prefix of
this kind; it is not omitted from (NMF.4). $\square$

**Definition 2.3 (synchronous convolution).** The canonical finite
convolution $V(\mathbf u)$ has domain
$\bigcup_i\operatorname{Pos}(u_i)$ and label $v_{\mathbf u}(p)$ at
$p$. Its finite ranked alphabet $\mathbb V_m$ consists of vectors in
$\mathcal A^m$ with at least one nonabsent coordinate. Such a vector
has rank two if any coordinate is $\mathsf{branch}$, and rank zero
otherwise.

A valid convolution has no absent root coordinate. At a rank-two
node, a branch coordinate has nonabsent coordinates at both children;
every nonbranch coordinate has absent coordinates at both children.
These conditions are sufficient as well as necessary: recursively
project each coordinate, terminating at its alpha or beta leaves and
discarding its absent padding. The result is a unique nonempty finite
native tuple, and its convolution is the original labelled tree.
This is a construction for a supplied finite tree. It asserts no
language-level convolution closure for a raw separated tuple packet.

**Definition 2.4 (address-preserving pruning and marker image).** Give
each convolution subtree its flag $E$ if its component reply maps
there all agree, and $D$ otherwise. The flag is $E$ exactly when its
root vector is constant and either the root is nullary or both
children have flag $E$.

For a subtree with flag $D$ define $F$ over the ranked alphabet
$\{e^0,b^2,a_L^1,a_R^1\}$ recursively. A nonconstant root vector
gives $F=e$, without proceeding below it. A constant root in state
$D$ is a common branch. If both children have flag $D$, set

$$
F=b(a_L(F_L),a_R(F_R)).
$$

If only the child in direction $s\in\{L,R\}$ has flag $D$, set
$F=a_s(F_s)$. A child with flag $E$ is omitted. There is no other
case for a $D$ subtree. Write $F(\mathbf u)$ for the result when
$\mathbf u$ is unequal.

On a root-to-$e$ path, concatenate the direction subscripts of its
$a_s$ nodes, ignoring $b$. This is its address word. Let
$K(\mathbf u)$ be the marker image obtained by replacing both $a_L$
and $a_R$ by the one unary letter $a$, retaining $b$ and $e$.
Thus the target alphabet is $\{a^1,b^2,e^0\}$.

**Theorem 2.5 (exact paths, every-path lower bound and source directions).**
For every unequal finite native tuple, the leaves of $F(\mathbf u)$
are in bijection with $\Delta(\mathbf u)$ by their address words.
The path for $p$ has exactly $|p|$ direction markers. Consequently
the corresponding path of $K(\mathbf u)$ has exactly $|p|$
occurrences of $a$, and

$$
\min_{\pi\text{ a branch of }K(\mathbf u)}\#_a(\pi)
=d(\mathbf u).
\tag{NMF.5}
$$

For the entire product of Definition 1.2, every tuple is unequal and

$$
J_B(h)\quad\Longleftrightarrow\quad
\exists\mathbf u\in\mathcal E_{I,B}\quad
\forall\pi\text{ a branch of }K(\mathbf u)\quad
\#_a(\pi)\ge h+1.
\tag{NMF.6}
$$

Both directions use one simultaneously chosen tuple satisfying every
original finite constraint. In particular (NMF.6) does not exchange
$\exists\mathbf u$ and $\forall\pi$.

Proof. Induct on the finite convolution. At a nonconstant root,
the frontier is exactly $\{\varepsilon\}$ and $F=e$; its path has
empty address word and zero markers. At a constant leaf the frontier
is empty, and the subtree has flag $E$. At a common branch,

$$
\Delta=L\Delta_L\ \cup\ R\Delta_R,
$$

with empty contributions precisely from the $E$ children. Each
retained child's path gains its actual direction letter and one
marker. With two retained children $b$ distinguishes their paths
but adds no marker; with one child the unary direction marker still
remembers whether the original edge was left or right. The induction
therefore proves the bijection, the entire original address word and
the exact marker count. Collapsing the two marker labels changes
neither paths nor their counts. This proves (NMF.5). Raw output edge
length, which also counts the inserted $b$ nodes, is not the cost.

If all components of a product tuple were identical, their complete
rows under the deterministic map $R_Q$ would be identical, contrary
to the distinct row labels. Thus (NMF.5) applies to every product
tuple. A witness for (NMF.2), by Theorem 2.2, has $d>h$; its own
pruning supplies the witness on the right of (NMF.6). Conversely
a tuple on that right has $d\ge h+1$ by (NMF.5), hence all four
replies agree through $h$ by (NMF.4). Its membership in the entire
product already enforces all old and new exteriors, reached sets,
partitions, signs and whole-value correlations. $\square$

The minimum in (NMF.5) is the first-disagreement counterpart of
NLC's minimum native leaf depth [NLC, Definition 1.1][NLC]. Common
early leaves are removed here because their descendants agree as
absent; they do not bound the first-disagreement depth. In a full
binary pruned address trie, ordinary minimum leaf depth is exactly
$d$. In a trie with deleted equal children, direction markers count
its original edges even where only one child remains.

## 3. Strict discount, an exact mass criterion and a pair metric

**Definition 3.1 (finite-frontier mass).** For any real $q>0$ and
any nonempty finite tuple define

$$
W_q(\mathbf u)=\sum_{p\in\Delta(\mathbf u)}q^{|p|}.
\tag{NMF.7}
$$

The empty frontier has mass zero. All masses are finite, and are
rational when $q$ is rational. The strict discount criterion fixes
a rational $q$ with $0<q<1/2$. The discount is per original edge,
independently of the number of inserted branching nodes or of any
source-presentation size.

**Theorem 3.2 (two-sided depth comparison and zero infimum).** Fix
a rational $q$ with $0<q<1/2$. Every unequal finite tuple satisfies

$$
q^{d(\mathbf u)}\le W_q(\mathbf u)
\le (2q)^{d(\mathbf u)}.
\tag{NMF.8}
$$

For every nonempty family $\mathcal E$ of unequal finite tuples,
of one fixed finite arity,

$$
\begin{aligned}
\forall h\in\mathbb N\ \exists\mathbf u\in\mathcal E\quad d(\mathbf u)>h
&\quad\Longleftrightarrow\quad
\inf_{\mathbf u\in\mathcal E}W_q(\mathbf u)=0\\
&\quad\Longleftrightarrow\quad
\forall\epsilon>0\ \exists\mathbf u\in\mathcal E\quad
W_q(\mathbf u)<\epsilon.
\end{aligned}
\tag{NMF.9}
$$

In particular, for the entire original product,

$$
\forall h\ J_B(h)
\quad\Longleftrightarrow\quad
\inf_{\mathbf u\in\mathcal E_{I,B}}W_q(\mathbf u)=0.
\tag{NMF.10}
$$

There is no assertion that the infimum is attained or that one finite
tuple works at all depths.

Proof. A shortest frontier address contributes $q^d$, proving the
lower bound. For a finite binary prefix-free set $C$, take a level
$n\ge\max_{p\in C}|p|$. Its sets of length-$n$ extensions are
disjoint and have respective sizes $2^{n-|p|}$. Counting at most
$2^n$ words proves
$\sum_{p\in C}2^{-|p|}\le1$. This is the binary prefix-code Kraft
inequality; see Cover and Thomas, *Elements of Information Theory*,
second edition, §5.2, DOI [10.1002/047174882X][KRAFT]. It is used
as an intermediate inequality, not as a new prefix-code result.
Apply it to $\Delta$ and use $2q<1$:

$$
\begin{aligned}
W_q(\mathbf u)
&=\sum_{p\in\Delta}2^{-|p|}(2q)^{|p|}\\
&\le(2q)^d\sum_{p\in\Delta}2^{-|p|}
\le(2q)^d.
\end{aligned}
$$

If depths are unbounded, for any $\epsilon>0$ choose $h$ with
$(2q)^{h+1}<\epsilon$ and then one tuple with $d>h$. Its mass is
at most $(2q)^{h+1}$. Conversely, if masses have zero infimum, for
each $h$ choose one tuple with $W_q<q^h$. If its depth were at most
$h$, the lower bound would give $W_q\ge q^d\ge q^h$, a
contradiction. This proves both directions of (NMF.9). Equation
(NMF.10) follows from (NMF.4) on exactly the original product.
No hypothesis about limits or persistence of negative records occurs.
$\square$

**Theorem 3.3 (binary metric and multiway control).** For each rational
$q$ with $0<q<1/2$, the function $D_q(s,t)=W_q(s,t)$ is a metric
on finite native trees. For every nonempty finite tuple of arity $m\ge2$,

$$
\max_{i<j}D_q(u_i,u_j)
\le W_q(\mathbf u)
\le\sum_{i=2}^m D_q(u_1,u_i).
\tag{NMF.11}
$$

These comparisons use actual values in one tuple; optimizing the
separate right-hand summands with different tuples is not licensed.

Proof. Symmetry and vanishing exactly on equal trees follow from
Theorem 2.2. The recursion defining the frontier gives distance zero
at equal leaves, distance one at unequal root labels, and

$$
D_q(\langle s_0,s_1\rangle,\langle t_0,t_1\rangle)
=q\bigl(D_q(s_0,t_0)+D_q(s_1,t_1)\bigr).
$$

Also $D_q\le1$ by the Kraft estimate in the preceding proof.
Prove the triangle inequality for $s,t,z$ by induction on their
total finite size. If $s,t$ have different root labels, at least
one of $(s,z)$ and $(z,t)$ has different root labels; its distance
is one, which bounds $D_q(s,t)$. If $s,t$ are the same leaf,
their distance is zero. If $s,t$ are branches and $z$ is a leaf,
the sum of the other two distances is two, while $D_q(s,t)\le1$.
If all three are branches, apply the induction hypothesis to each
child triple and multiply their summed inequalities by $q$.
These exhaustive cases prove the metric assertion.

Every pair's first mismatch has a unique prefix in the multiway
frontier: the pair mismatch is a multiway mismatch, so take its
first such prefix. Group the pair frontier under these prefixes
$p$. Within each group the suffixes are prefix-free, and their
total $q$-mass is at most one by the same Kraft estimate. The
pair's contribution under $p$ is therefore at most $q^{|p|}$.
Summing proves each pair distance is at most $W_q(\mathbf u)$.

For each $p\in\Delta(\mathbf u)$ choose $i\ge2$ whose reply at
$p$ differs from that of $u_1$. All proper prefixes are constant
for the whole tuple, so $p$ is itself a first mismatch of
$(u_1,u_i)$. The selected terms $q^{|p|}$ are distinct terms of
the sum on the right of (NMF.11), which can have further terms.
This proves the other inequality. $\square$

## 4. Two complete native inputs separating the growth notions

**Theorem 4.1 (critical branching mass fails along an actual depth-growing
sequence).** There is a complete acquired native input and two distinct
attained whole rows with an actual tuple sequence $\mathbf u_n$ in
their entire product such that

$$
d(\mathbf u_n)=n+1,
\qquad
W_q(\mathbf u_n)=q(2q)^n\quad(q>0).
\tag{NMF.12}
$$

Thus at $q=1/2$ the frontier's fair binary branching proportion is
always $1/2$, although the minimum mismatch depth tends to infinity.
For every $q>1/2$ the displayed masses grow without bound. No
bound $W_q(\mathbf u)\le f(d(\mathbf u))$ with $f(n)\to0$
can hold uniformly on this entire product for $q\ge1/2$.
Nevertheless the infimum of the critical mass over this same
entire product is zero. In particular the sequence does not refute
a zero-infimum statement on the whole row product.

Proof. Take $P=\{\varepsilon\}$ and the entire one-hole old row,
with reached set $\{\varepsilon\}$ and partition $\{\{1\}\}$.
Take final epoch $N=1$, target cut $Q=\{L,R\}$, and exactly

$$
\begin{aligned}
H_0&=\{(0,\varepsilon,\mathsf{branch}),
          (1,\varepsilon,\mathsf{branch})\},\\
H_{\rm rel}&=\{(1,L,1,L,=),\ (0,\varepsilon,0,L,\ne)\}.
\end{aligned}
\tag{NMF.13}
$$

Every retained source has form $\langle x,z\rangle$. Conversely
every such source satisfies the old row and both literals, since
native updates preserve an existing branch. The epoch-one $L$
endpoint is the reached tree $\rho x$, so its reflexive record
passes with both guards. At epoch zero both negative endpoints
are reached, and the root tree differs from its proper left
subtree: its number of leaves is $\ell(x)+\ell(z)>\ell(x)$.
Thus the entire input fiber is exactly
$D=\{\langle x,z\rangle:x,z\in\mathcal T\}$.
There are no additional retained records or parameter guards.

The complete target rows have reached set $Q$, exterior
$\langle\square_1,\square_2\rangle$, and respectively partitions
$r_{=}=\{\{1,2\}\}$ and $r_{\ne}=\{\{1\},\{2\}\}$.
Their entire strata are

$$
D_{=}=\{\langle x,x\rangle:x\in\mathcal T\},\qquad
D_{\ne}=\{\langle y,z\rangle:y,z\in\mathcal T, y\ne z\}.
\tag{NMF.14}
$$

Both rows are attained, for example by
$\langle\alpha,\alpha\rangle$ and
$\langle\alpha,\beta\rangle$. Equality of the hole values in
the first stratum is whole-value equality; the values themselves
do not appear as exterior labels. These two inclusions in each
stratum follow directly from the fixed complete exterior and its
full partition, not from a selection of some realizers.

Define perfect trees
$A_0=\alpha$, $B_0=\beta$,
$A_{n+1}=\langle A_n,A_n\rangle$ and
$B_{n+1}=\langle B_n,B_n\rangle$.
Their minimum native leaf depth is $n$, in the sense of NLC
Definition 1.1. They have identical branch nodes through depth
$n-1$ and different leaves at every address of depth $n$.
The actual tuple

$$
\mathbf u_n=(\langle A_n,A_n\rangle,
              \langle A_n,B_n\rangle)
\in D_{=}\times D_{\ne}
$$

has frontier $\{Rw:|w|=n\}$. Its $2^n$ addresses all have depth
$n+1$, proving (NMF.12). Each tuple retains all of (NMF.13), with
the actual original whole values and both reached guards.
At $q=1/2$ their cylinders have total fair binary proportion
$2^n2^{-(n+1)}=1/2$. For $q>1/2$ (NMF.12) diverges. These
are sequence and uniform-bound conclusions.

To compute the entire-product infimum, define instead
$Z_0=\beta$ and $Z_{n+1}=\langle A_n,Z_n\rangle$.
The trees $A_n,Z_n$ differ at precisely the one first address
$R^n$. Thus the actual tuple
$(\langle A_n,A_n\rangle,\langle A_n,Z_n\rangle)$ belongs
to the same entire product and has singleton frontier
$\{RR^n\}$, of critical mass $2^{-(n+1)}$. Its masses tend
to zero. Positivity gives the infimum zero, as asserted.

All recorded epochs are at most $N=1$. The displayed mathematical
input is subject to the one paid-source and complete-cut premise
of Definition 1.1; each attained row indexes alternative originals
for that same input. No new acquisition procedure is deduced.
$\square$

The shortest-term bound $2^{-d}\le W_{1/2}$ still implies that
zero critical infimum entails unbounded depth for any family of
unequal tuples. The reverse uniform depth-to-mass estimate used
in Theorem 3.2 fails at the critical threshold by Theorem 4.1.
On the subfamily consisting only of its balanced sequence the
depths are unbounded and the critical infimum is $1/2$; that
subfamily is not the entire product (NMF.14). A failure of the
reverse zero-infimum implication on arbitrary entire signed row
products would require a separate all-tuple lower bound. None is
asserted here. Strict discount supplies both directions without
such an additional fiber hypothesis.

**Theorem 4.2 (many nodes and a long branch with a fixed failed prefix).**
There is a second complete acquired native input, retaining a
nontrivial old full partition and both signed histories, with two
distinct attained complete rows such that $J_B(0)$ holds and
$J_B(1)$ fails. Nevertheless their entire product contains tuple
prunings with arbitrarily many markers and arbitrarily long
marker paths, and sources with arbitrarily many native nodes.

Proof. Set $P=\{L,RL,RR\}$, $N=1$ and $Q=\{RL,RR\}$.
The old row has reached set $P$, entire exterior
$\langle\square_1,\langle\square_2,\square_3\rangle\rangle$,
and full partition $\{\{1\},\{2,3\}\}$. Retain exactly

$$
\begin{aligned}
H_0=\{&(0,\varepsilon,\mathsf{branch}),(0,R,\mathsf{branch}),
       (1,\varepsilon,\mathsf{branch}),(1,R,\mathsf{branch})\},\\
H_{\rm rel}=\{&(0,RL,0,RR,=),(1,RL,1,RR,=),\\
              &(0,L,0,RL,\ne),(0,\varepsilon,0,L,\ne)\}.
\end{aligned}
\tag{NMF.15}
$$

The old row alone gives, in both directions,

$$
D=\{\langle x,\langle y,y\rangle\rangle:
          x,y\in\mathcal T,\ x\ne y\}.
\tag{NMF.16}
$$

It fixes the complete constructor exterior, makes all three holes
reached, repeats the identical value $y$, and makes the first
old class different from the second. In particular both old
cross-class pairs are still unequal, including the pair $L,RR$
not separately repeated in the history.

Every source in (NMF.16) satisfies all four literals. The first
positive record compares $y$ to $y$; the second compares
$\rho y$ to $\rho y$ at its two reached epoch-one endpoints.
The first negative compares the reached $x,y$ and passes exactly
the old cross-class condition. The off-task root/left negative
passes because the root has $\ell(x)+2\ell(y)>\ell(x)$ leaves.
Thus adding every record in (NMF.15) leaves exactly (NMF.16),
without dropping any record or reached guard. There are no further
retained constraints.

Let $r_\alpha$ and $r_\beta$ have reached set $Q$, full one-class
partition $\{\{1,2\}\}$ and respective entire exteriors

$$
\langle\alpha,\langle\square_1,\square_2\rangle\rangle,
\qquad
\langle\beta,\langle\square_1,\square_2\rangle\rangle.
$$

Because $L$ is outside $Q$, these alpha and beta leaves are actual
uncut exterior nodes. They are not values distinguished inside
an erased hole. The exact entire strata are

$$
\begin{aligned}
D_\alpha&=\{\langle\alpha,\langle y,y\rangle\rangle:
                         y\in\mathcal T, y\ne\alpha\},\\
D_\beta&=\{\langle\beta,\langle z,z\rangle\rangle:
                         z\in\mathcal T, z\ne\beta\}.
\end{aligned}
\tag{NMF.17}
$$

Reading the complete exterior and partition from a source proves
one direction of each equality; filling the displayed repeated
holes with any permitted whole value proves the other. Other
complete rows of (NMF.16) remain in the original input fiber.
Neither source stratum is substituted for the whole input.

For $n\ge1$ use the perfect trees from Theorem 4.1 and the tuple

$$
\mathbf v_n=(\langle\alpha,\langle A_n,A_n\rangle\rangle,
              \langle\beta,\langle B_n,B_n\rangle\rangle).
$$

Since $A_n$ and $B_n$ are branches, they meet both disequalities
in (NMF.17). This proves attainment. Every cross-stratum tuple
agrees at the root branch and differs at original address $L$.
Thus its minimum mismatch depth is one, independently of its
other values. This gives $J_B(0)$ and the exact failed depth
$H=1$ for $B=(r_\alpha,r_\beta)$.

For the displayed tuples the entire frontier is

$$
\Delta(\mathbf v_n)=\{L\}\ \cup
\{RLw:|w|=n\}\ \cup\ \{RRw:|w|=n\}.
\tag{NMF.18}
$$

The shortest marker path of $K(\mathbf v_n)$ therefore has
one marker, while its longest has $n+2$. There are $2^{n+1}+1$
frontier leaves. The first two convolution levels retain both
children and contribute four markers. The two remaining perfect
height-$n$ address tries each contribute
$2+4+\cdots+2^n=2^{n+1}-2$ markers. Hence the total marker
count is $2^{n+2}$. Each original source has
$2^{n+2}+1$ native nodes, by counting the root, its left leaf,
its right branch and the two perfect subtrees. All three growth
claims are unbounded, with the same fixed first disagreement.
Indeed their frontier mass is
$W_q(\mathbf v_n)=q+2q^2(2q)^n\ge q$.

The old full row, reached sets, actual-epoch records, off-task
negative and within-source sharing have all been checked on each
actual finite source. The complete handoff and paid-source contract
remains the supplied premise at $N=1$. $\square$

## 5. Effective linear transduction, with its actual input class

**Theorem 5.1 (finite-state annotation followed by faithful pruning).**
For each fixed finite $m\ge2$ there are effectively specified
linear finite tree transducers $\mathsf A_m,\mathsf P_m$ and a
linear tree homomorphism $\mathsf H$ such that, on every valid
unequal convolution,

$$
\mathsf A_m(V(\mathbf u))=\{\operatorname{ann}(V(\mathbf u))\},
\quad
\mathsf P_m(\operatorname{ann}(V(\mathbf u)))=\{F(\mathbf u)\},
\quad
\mathsf H(F(\mathbf u))=K(\mathbf u).
\tag{NMF.19}
$$

$\mathsf A_m$ has no output on valid convolutions of identical
tuples. Here linear means precisely the rule condition in
Barozzini, Clemente, Colcombet and Parys, *Cost Automata, Safe
Schemes, and Downward Closures*, [§4.2, “Transductions”][BCCP42]:
each input child occurs in at most one recursive state call in
any right-hand side. These transducers do not test membership
in $D_i$ or synthesize the convolution language from raw packets.

Proof. For $\mathsf A_m$ take states $E,D$, initial state $D$,
and an annotated alphabet with labels $(v,s)$ of rank zero or
$(v,s,s_L,s_R)$ of rank two. Its rank-zero rule is

$$
(s,v)\longrightarrow(v,s)
\quad\text{exactly when}\quad
(s=E\ \Longleftrightarrow\ v\text{ is constant}).
$$

For rank two, include exactly the finitely many rules

$$
(s,v(x_L,x_R))\longrightarrow
(v,s,s_L,s_R)((s_L,x_L),(s_R,x_R))
\tag{NMF.20}
$$

for which

$$
s=E\quad\Longleftrightarrow\quad
v\text{ is constant and }s_L=s_R=E.
$$

The right-hand $(s_i,x_i)$ are recursive state calls, not
alphabet labels. The vector alphabet and the two flags are finite,
so this is a finite rule set obtained by exhaustive finite cases.
Every input child is traversed exactly once. There are no
epsilon-transitions, variable tests or hidden subtree comparisons.

By bottom-up induction on the supplied finite input, exactly one
flag at each node permits successful rules throughout its subtree,
namely the flag of Definition 2.4. At rank zero this is the rule
condition. At rank two the induction fixes both child flags and
the displayed equivalence fixes the parent. All successfully
guessed child annotations are therefore the unique correct ones.
Starting in $D$ accepts precisely unequal valid convolutions.
In particular all children below a root disagreement are still
checked by this first transducer.

The second transducer has one state $p$, initial state $p$.
On a certified $D$ label with nonconstant vector it outputs $e$
and deletes its children. On a constant vector its only rules are

$$
\begin{aligned}
(p,(v,D,D,D)(x_L,x_R))
 &\longrightarrow b(a_L((p,x_L)),a_R((p,x_R))),\\
(p,(v,D,D,E)(x_L,x_R))
 &\longrightarrow a_L((p,x_L)),\\
(p,(v,D,E,D)(x_L,x_R))
 &\longrightarrow a_R((p,x_R)).
\end{aligned}
\tag{NMF.21}
$$

It has no rule on $E$ labels. The annotated rank-zero or rank-two
nonconstant cases have right side $e$. Its input domain here is
the certified output of $\mathsf A_m$, so no unchecked $D,E,E$
case is accepted. The first transducer checked deleted children;
deleting them in the second cannot make a false annotation succeed.
Each retained child occurs once and each deleted child zero times.
Thus both transducers satisfy the published linearity definition,
including its “at most one” allowance for deletion. Their rules
are exactly the pruning recursion, so induction gives the middle
equality of (NMF.19).

Finally $\mathsf H$ has rules $a_s(x)\mapsto a(x)$ for each
$s$, $b(x,y)\mapsto b(x,y)$, and $e\mapsto e$, understood with
one recursive homomorphism call on each displayed child. It is
also a linear FTT of §4.2. This proves the last equality. Every
rule is well typed by the displayed input and output ranks:
$a_s,a$ are unary, $b$ binary and $e$ nullary. $\square$

**Theorem 5.2 (both entire-source language directions).** For a family
$\mathcal E\subseteq\mathcal T^m$ consisting of unequal tuples, set
$\mathcal V=\{V(\mathbf u):\mathbf u\in\mathcal E\}$ and
$\mathcal K=\{K(\mathbf u):\mathbf u\in\mathcal E\}$. Then

$$
\mathsf H(\mathsf P_m(\mathsf A_m(\mathcal V)))=\mathcal K.
\tag{NMF.22}
$$

In particular, with $\mathcal E=\mathcal E_{I,B}$, every output
comes from one actual simultaneous original tuple satisfying all
of the complete input and its exact rows; every such tuple supplies
an output whose every-path cost is its original minimum mismatch
depth. The output alone need not recover the tuple.

Proof. For soundness choose an output of the left side. By the
definition of relational transduction it has some input in
$\mathcal V$, hence a complete tuple $\mathbf u\in\mathcal E$.
Theorem 5.1 forces the unique annotation and its exact $F$ and
$K$. Theorem 2.5 supplies its exact address and cost correspondence.
For completeness take any tuple in $\mathcal E$, convolve its
actual trees, choose the unique successful annotations guaranteed
by Theorem 5.1, and apply its pruning and homomorphism rules.
This yields its $K$ on the left. No new tuple is chosen at a
branch, and no within-source occurrence changes its value.
For $\mathcal E_{I,B}$, membership and source reconstruction use
the entire strata of Definition 1.2 or NIC's two directions, rather
than a selected finite witness subset. $\square$

**Theorem 5.3 (matched early leaves must be erased).** On the entire
SPC acquired copied-source instance with
$F(y)=\langle\alpha,\rho y\rangle$ and
$U(x,y)=\langle x,\langle y,F(y)\rangle\rangle$, replacing
matched terminated branches by frontier leaves gives a false
boundedness measure on its established all-depth witness sequence.
The pruning of Definition 2.4 avoids this error.

Proof. Use the complete input and exact rows $r_0,r_1$ of
[SPC, Definitions 3.1 and 8.1; Theorems 3.2–3.3][SPCEXT], with
its positive epoch-one record, finite negative, whole exterior,
reached set and full partitions. Those existing results give
$y_n=F^n(\beta)$ and the actual original tuples
$\mathbf w_n=(U(y_n,y_n),U(y_{n+1},y_n))$, whose minimum
mismatch depths tend to infinity. This entire-family supplier
and its non-rational contact are not new claims here.

For every $n\ge1$, both components have reply $\alpha$ at
original address $LL$, because the left child of each $y_n$
is $\alpha$. This is a matched terminated branch, and every
strict extension is absent in both components. A procedure that
turns all matching leaves into cost endpoints therefore has an
endpoint at depth two for every tuple of this sequence. Its
minimum endpoint depth is at most two even though the minimum
first-disagreement depth is unbounded. The whole right subtrees
of the two $U$ sources also agree and create no mismatch obligation.
In Definition 2.4 these subtrees and the common $LL$ leaf have
flag $E$ and are deleted, while every genuine frontier address
keeps its exact original marker count by Theorem 2.5. This is
the consumer of the annotation's equality flags. $\square$

## 6. Every-branch decision transfer and its remaining premise

**Definition 6.1 (faithful safe exact convolution carrier).** A carrier
for $(I,B)$ is a supplied finite recursion scheme $\mathcal G$
whose nonempty finite-output language, in the $\mathsf{nd}$
choice and $\bot$ exclusion convention of [BCCP, §4][BCCP], is
exactly

$$
\mathcal L(\mathcal G)
=\{V(\mathbf u):\mathbf u\in\mathcal E_{I,B}\}.
\tag{NMF.23}
$$

Soundness in (NMF.23) includes convolution validity and all original
records and rows; completeness includes every tuple in the entire
product, with its within-source sharing, image and rank guards.
The scheme is required to be safe in the syntactic sense of
[BCCP, §2][BCCP]: each argument subterm of an application is
superficially safe, meaning every free variable in that argument
has order at least the order of the argument subterm. Every typed
rule right-hand side $\mathcal R(X)$ must be safe in this sense;
the scheme's Böhm tree must also be well defined. A type has
$\operatorname{ord}(o)=0$ and
$\operatorname{ord}(A\to B)=\max(\operatorname{ord}(A)+1,
\operatorname{ord}(B))$.

An effectively supplied carrier means finite scheme data together
with this faithful correspondence and safety condition. A uniform
effective carrier construction would produce such data from each
legal complete $I,B$. Merely supplying a raw packet of separated
whole tree fields gives neither (NMF.23) nor safety.

**Theorem 6.2 (exact native criterion becomes the published every-branch
diagonal).** Conditional on a faithful safe exact convolution carrier,
one can effectively obtain a safe scheme $\mathcal G_K$ with
finite-output language $\mathcal K_{I,B}$ of Theorem 5.2. Moreover
the following statements are equivalent:

$$
\begin{aligned}
&\forall h\in\mathbb N\ J_B(h);\\
&\forall n\in\mathbb N\ \exists T\in\mathcal L(\mathcal G_K)
  \quad\forall\pi\text{ a branch of }T\quad\#_a(\pi)\ge n;\\
&\inf_{\mathbf u\in\mathcal E_{I,B}}W_q(\mathbf u)=0
       \quad(q\in\mathbb Q,\ 0<q<1/2).
\end{aligned}
\tag{NMF.24}
$$

The conditional all-depth alternative is decidable by the published
safe-scheme every-branch diagonal theorem. This is a decision
conditional on (NMF.23), not a construction of (NMF.23).

Proof. BCCP §5, “Closure under transductions”, proves effective
closure of finite-tree languages recognized by safe recursion
schemes under linear FTT transductions, preserving safety.
Apply that result successively to $\mathsf A_m$, $\mathsf P_m$
and $\mathsf H$. Their alphabets, finite rule sets, ranks and
linearity were checked explicitly in Theorem 5.1. The input
language is precisely (NMF.23), so Theorem 5.2 gives both
directions of the resulting language equality. Nothing in these
three operations builds a convolution from separated source fields
or evaluates an unspecified feasibility predicate.

By Theorem 2.5 the middle statement of (NMF.24) is the unbounded
minimum mismatch depth of one chosen tuple at each $n$. For
$n=h+1$ it is exactly $J_B(h)$. The $n=0$ requirement is automatic
because the original rows are attained, so their finite product is
nonempty. This proves the first equivalence. Theorem 3.2 on the
same entire product proves the second.

The middle statement is exactly $\{a\}$-diagonality as defined
in BCCP [§4.4, “The diagonal problem for trees”][BCCP44]: every
branch of one finite tree has the requested label multiplicity.
BCCP [§5, “Solving the diagonal problem”][BCCP5] proves this
problem decidable for safe schemes. Its input hypotheses are now
met by the condition on $\mathcal G$ and the proved transductions.
This supplies the conditional decision. $\square$

**Theorem 6.3 (explicit weak-cost formula and stopping after classification).**
Under the carrier premise of Theorem 6.2, the finite-exclusion
alternative has a concrete weak cost monadic second-order sentence
$\Phi(N)$ whose positive numeric atoms are of the form $|Z|<N$.
For every $N\in\mathbb N$ it holds on the Böhm tree of
$\mathcal G_K$ exactly when every generated finite $K$ has a
branch with fewer than $N$ markers. Acceptance for some $N$ is
equivalent to $\exists H\,\neg J_B(H)$.

Conditional on this decision, a failed-depth search terminates
in the finite-exclusion case; in the all-depth case, each requested
$h$ has an actual simultaneous original tuple obtained using NSF.
No assertion of global termination follows from per-depth extraction
alone.

Proof. Follow the explicit finite-resolution formula of BCCP §5.
The weak set variable $X$ represents one finite resolution,
including its choice ancestors. The formula $\operatorname{Tree}(X)$
says that $X$ contains the root, contains no $\bot$ node, contains
exactly one child at each included $\mathsf{nd}$ node, contains
all children at each other included node, and is prefix-closed.
Equivalently, an excluded node has no included child. Weak
quantification already requires $X$ finite. These are local
first-order conditions once membership in $X$ is given. They
select exactly the complete nonempty finite outputs, with the
choice nodes suppressed afterward.

Let $\operatorname{Anc}(z,x)$ mean that $z$ is an ancestor of $x$,
including $z=x$. It is definable in weak monadic logic using the
finite unique tree path from $z$ to $x$. Put

$$
\begin{aligned}
\Phi(N)=\forall X\bigl(\operatorname{Tree}(X)\ \Longrightarrow
\exists x\exists Z\bigl[&x\in X\land e(x)\\
&\land\forall z\bigl((\operatorname{Anc}(z,x)\land a(z))
                    \Longrightarrow z\in Z\bigr)\\
&\land |Z|<N\bigr]\bigr).
\end{aligned}
\tag{NMF.25}
$$

Both $X$ and $Z$ range over finite sets. The numeric predicate
occurs positively; $N$ is the one permitted numeric parameter.
The ancestor set of any selected finite-output leaf is finite,
and all its ancestors are included in $X$. A set $Z$ of size
less than $N$ containing all its $a$ ancestors exists exactly
when that branch has fewer than $N$ markers: one direction uses
the size of this subset of $Z$, the other takes $Z$ to be exactly
that subset. The symbol $e$ is nullary, so $x$ is a genuine output
leaf. Choice ancestors do not contribute markers. Theorem 2.5
then identifies the least such cardinality in each finite output
with the original $d(\mathbf u)$ of its source tuple. Theorem 5.2
ensures both complete source directions despite possible repeated
output trees.

Thus (NMF.25) holds exactly when
$\forall\mathbf u\in\mathcal E_{I,B}\ d(\mathbf u)<N$.
The product is nonempty, so it cannot hold with $N=0$. For
$N\ge1$ it is equivalent to $\neg J_B(N-1)$ by (NMF.4).
Conversely any failed inclusive depth $H$ makes it hold with
$N=H+1$. This proves the claimed acceptance equivalence.

BCCP §5, “Cost logics”, decides whether a supplied WCMSO
sentence accepts the tree of a supplied safe scheme, with
acceptance meaning that some natural numeric parameter works.
The theorem does not require extracting that numeric witness.
Once it says that an exclusion exists, test $J_B(0),J_B(1),\ldots$
by the reused finite NSF decision until one fails. Existence of
a failed depth, established independently by the safe-scheme
decision, proves that this search terminates.

If instead the decision establishes all depths, for a requested
$h$ conjoin, in one finite query, one complete predicate for each
$D_i$ and equal four-reply tests at every address through $h$.
NSF Lemma 5.1 and Theorem 5.2 decide this exact finite existential
query and reconstruct all original sources. The decision already
guarantees a positive answer. It supplies the tuple with all finite
signs and rows, without reconstructing a source from the lossy
pruning or choosing a common limiting contact. $\square$

**Theorem 6.4 (the source counterexample rules out two weaker transfers).**
The original-source family in Theorem 4.2 satisfies both unbounded
total $a$-count in its finite pruning language and unbounded
maximum branch $a$-count. Its pruning language is not
$\{a\}$-diagonal. Hence neither of those growth tests can replace
the every-branch predicate in Theorems 6.2–6.3, even on actual
entire signed-native row products.

Proof. Its displayed actual tuples have total marker count
$2^{n+2}$ and maximum branch count $n+2$. Every tuple in its
entire product, not merely the displayed sequence, has a
frontier path of count one at original $L$. Thus no pruning
has all branches of count at least two. This disproves
diagonality with its exact $n=2$ threshold while establishing
both weaker unboundedness properties. All source hypotheses
were proved in both directions in Theorem 4.2. $\square$

[Badyl and Parys, *Extending the WMSO+U Logic With Quantification
Over Tuples*, Theorem 2][BP] decides a supplied
$\mathrm{WMSO}+U_{\rm tup}$ sentence on a supplied unrestricted
recursion scheme. Its tuple quantifier in §3 requires one tuple
of finite sets with simultaneous arbitrarily large cardinalities;
its finite-output SUP construction in §4 counts labels. Theorem
6.4 prevents equating those raw counts with the cost here. It
does not preclude some separately proved encoding into that
logic. No translation of the weak-cost sentence (NMF.25) into
its unrestricted-scheme decision theorem is asserted. In
particular that theorem does not remove the safety premise of
the WCMSO supplier used above.

## 7. Boundary cases, attribution and the unresolved construction

**Definition 7.1 (empty and degenerate cases).** In Theorems 2.2,
3.1–3.3 an identical tuple has $\Delta=\varnothing$, $d=\infty$
and $W_q=0$. It has no $F$ or $K$ tree under Definition 2.4;
one may separately record its empty collection of mismatch paths.
One must not represent it by the leaf $e$, which would assign
cost zero. Identical tuples cannot occur in the distinct-row
product of Definition 1.2.

If some requested row is unattained, the product is empty and
$J_B(h)$ is false for every $h$. With the extended-real convention
$\inf\varnothing=+\infty$, zero infimum is also false. Its
pruning language is empty and fails the diagonal requirement
already at $n=0$, since that requirement still asks for a tree.
The finite exclusion can be $H=0$. The declared attained-row
task avoids this case, but none of the source directions accepts
a fictitious realization of an empty row.

For one attained row, $J_B(h)$ is trivially true by taking one
source, while its mismatch collection is empty. For zero rows,
the one empty tuple similarly satisfies the empty conjunction.
Neither case is represented by the nonempty finite-output diagonal
encoding of §6; they are settled separately. The entire product
task here assumes $m\ge2$.

Common early leaves contribute no frontier point and no descendant
constraint beyond equal absent replies. A root disagreement has
$\Delta=\{\varepsilon\}$, $d=0$, $F=K=e$ and $W_q=1$;
no inclusive depth-zero prefix can be witnessed by that tuple.
Empty original cuts or empty reached sets in a complete row keep
their exact exterior and empty partition. Distinct attained rows
at a root target cut cannot exist for these nonempty native sources.

**Definition 7.2 (mathematical dependencies and ownership).** NSF
Theorem 4.3, Lemma 5.1 and Theorem 5.2 supply finite signed
feasibility, guarded observation compilation and reconstruction
of original sources. NIC Theorems 3.2–3.3 and 4.3 supply entire
positive images, original-native signed pullbacks and exact
complete row strata. They are not new decision or image-cover
claims here. NLC's minimum leaf-depth statistic supplies the
minimum-versus-maximum depth distinction used in §2 and the
perfect-tree calculation in §4. [SPC][SPCEXT]'s entire productive family,
its finite witnesses, closed comparison results and §§7–10
representation and lifting boundaries retain their separate
scope. In particular no rational-contact, closed-value or
topological criterion replaces the finite tuples of (NMF.2).

The source definitions correspond to the existing declarations
$\mathsf{readout}$ in [ActualTreeReadoutAcquisition][READOUT],
$\mathsf{literalRecord}$ and
$\mathsf{canonicalRow\_record\_iff}$ in
[ActualCutPartitionDecoder][ROWS], and the whole-row
$\mathsf{rowFiberEquiv}$ in [NativeCutFibers][FIBERS]. The
private reconstruction and injectivity lemmas
$\mathsf{recover\_fill}$ and $\mathsf{fill\_injective}$ belong
to that last supplied correspondence. The reached-prefix decomposition is
$\mathsf{depthEquiv}$ in [NativeDepthPatterns][DEPTH], with
its private $\mathsf{fill\_decompose}$ and
$\mathsf{decompose\_fill}$ inverse helpers. These addresses
identify the meanings being reused; the proofs in this volume
are the mathematical arguments stated here.

The external decision supplier is Barozzini, Clemente, Colcombet
and Parys, *Cost Automata, Safe Schemes, and Downward Closures*,
arXiv:2004.12187v6, also published in *Fundamenta Informaticae*,
DOI [10.3233/FI-222145][BCCPDOI]. Its §4.2 supplies the precise
linear FTT rule class, §4.4 the every-branch diagonal definition,
and §5 the safe-scheme diagonal decision, WCMSO decision and
safety-preserving transduction closure. The section titles fix
the cited results without relying on the HTML's theorem counters.
The Kraft inequality is the attributed intermediate in Theorem
3.2. The finite native address pruning, its exact correspondence,
the joint mass equivalence, the complete native counterexamples
and their conditional consumer are deductions from the definitions
and those suppliers. No external originality or absolute
minimality assertion is attached to them.

**Open problem 7.3 (unrestricted faithful safe source-convolution
construction).** For arbitrary complete signed-native $I$ and
arbitrary finite distinct attained $B$ with $|B|\ge2$, construct
effectively a faithful safe carrier satisfying (NMF.23), or supply
a different terminating exact mechanism for the original
alternative (NMF.2). All exteriors, full partitions, reached
guards, actual epochs, multiple positive constraints, finite
negatives, shared values and image/rank correlations must remain.
No such unrestricted carrier construction is supplied by the
transducers of §5.

A finite zipper on a chosen tuple is not a proof that a whole
signed tuple language has a finite safe convolution scheme.
An eager whole-value generator can preserve sharing and still
be unsafe: an order-$k$ argument containing a free variable of
order less than $k$ fails the safety condition of Definition 6.1.
The transduction theorem here starts from an already safe exact
convolution carrier and does not repair that failure. Likewise,
ordinary finite-packet equality checking does not give effective
safe-scheme closure under all original signed constraints.

The mathematical obligation remaining before an unconditional
decision is therefore specific: provide both whole-source
directions for that constrained convolution and prove its safety,
or prove another exact stopping theorem. Once those premises
are supplied, (NMF.19), (NMF.24) and (NMF.25) already give the
faithful every-path cost and its decision consumer. Cardinality,
a long branch, matched-leaf endpoints and a critical balanced
sequence do not discharge that obligation, by Theorems 4.1,
4.2, 5.3 and 6.4.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[SPCEXT]: https://github.com/the-omega-institute/trureturing/blob/db23810980530aea4b6fc2a056615460c8cbecb9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[READOUT]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[ROWS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[FIBERS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[KRAFT]: https://doi.org/10.1002/047174882X
[BCCP]: https://arxiv.org/html/2004.12187v6
[BCCP42]: https://arxiv.org/html/2004.12187v6#S4.SS2
[BCCP44]: https://arxiv.org/html/2004.12187v6#S4.SS4
[BCCP5]: https://arxiv.org/html/2004.12187v6#S5
[BCCPDOI]: https://doi.org/10.3233/FI-222145
[BP]: https://arxiv.org/html/2311.16607v1

## 追加锚（本行以下为增补区）

## 8. Entire shift-copy products and normalized ray mass

**Definition 8.1 (the retained shift-copy input).** Fix a supplied
integer $a\ge1$, put $S=\rho^a$, and define

$$
U_a(x,y)=\langle x,\langle y,Sy\rangle\rangle.
\tag{NMF.8.1}
$$

The two occurrences of $y$ use the same whole finite native value.
Take $P=\{\varepsilon\}$ with its complete one-hole old row, final
epoch $N=a$, target cut $Q=\{L,RL,RR\}$ in that order, and exactly

$$
\begin{aligned}
H_0=\{&(0,\varepsilon,\mathsf{branch}),
       (0,R,\mathsf{branch}),\\
      &(a,\varepsilon,\mathsf{branch}),
       (a,R,\mathsf{branch})\},\\
H_{\rm rel}=\{&(a,RL,0,RR,=),\
              (0,RL,0,RR,\ne),\
              (0,\varepsilon,0,L,\ne)\}.
\end{aligned}
\tag{NMF.8.2}
$$

There are no other records or image/rank conditions in this instance.
Definition 1.1's paid-source and complete-state premise is retained.
The off-task root/left comparison is part of the input.

**Theorem 8.2 (entire source reconstruction and all attained rows).**
The entire fiber of Definition 8.1 is

$$
D^{(a)}=\{U_a(x,y):x,y\in\mathcal T\}.
\tag{NMF.8.3}
$$

Its complete target-row image has exactly three attained labels.
Every label has reached set $Q$ and the entire exterior
$\langle\square_1,\langle\square_2,\square_3\rangle\rangle$.
Their partitions and entire strata are

$$
\begin{aligned}
r_0&:\{\{1,2\},\{3\}\},&
D_0^{(a)}&=\{U_a(t,t):t\in\mathcal T\},\\
r_1&:\{\{1,3\},\{2\}\},&
D_1^{(a)}&=\{U_a(St,t):t\in\mathcal T\},\\
r_2&:\{\{1\},\{2\},\{3\}\},&
D_2^{(a)}&=\{U_a(x,t):x,t\in\mathcal T,\
                         x\ne t,\ x\ne St\}.
\end{aligned}
\tag{NMF.8.4}
$$

Both directions recover the original source itself, including every
literal, both endpoint guards of every sign, and the off-task negative.

Proof. The epoch-zero literals force
$u=\langle x,\langle y,z\rangle\rangle$, with $x,y,z$ nonempty.
Existing native branch nodes survive every iterate. Thus the epoch-$a$
root and $R$ literals hold, and the subtree at epoch-$a$ address $RL$
is $Sy$. The first relation in (NMF.8.2) has reached endpoints and
forces $z=Sy$.

For any finite $t$, all its original branch nodes survive $S$.
At each original alpha leaf the new root reply is beta for $a=1$
and branch for $a\ge2$. At each original beta leaf it is branch for
every $a\ge1$. These statements follow from the native leaf laws:
after beta becomes a branch, subsequent updates preserve that branch.
There is at least one original leaf, so $t\ne St$.
Consequently the second relation is true for every $U_a(x,y)$,
with both its original $RL,RR$ endpoints reached.

For the last relation, finite leaf count gives

$$
\ell(U_a(x,y))=\ell(x)+\ell(y)+\ell(Sy)>\ell(x),
$$

so the reached original root differs from its reached left subtree.
The old root row has one reached hole and one class for every
nonempty source. Therefore every $U_a(x,y)$ satisfies that old row,
all four literals, and all three guarded records. Together with
the forced decomposition, this proves (NMF.8.3) in both directions.

The target values are exactly $x,y,Sy$, and $y\ne Sy$ on the entire
finite domain. Thus $x$ can equal the second value, the third value,
or neither, giving exactly the partitions and conditions in
(NMF.8.4). The first two rows are attained for every $t$ by their
displayed sources. The third is attained with $x=S^2t$: one has
$S^2t\ne St$ by applying the preceding leaf argument to $St$, and
$S^2t\ne t$ by applying it to $\rho^{2a}$ on $t$.
No exterior or row label is discarded.

All relation epochs are $0$ or $a\le N$. Instantiating
[ARH, Proposition 2.1][ARH] with these fixed public coordinates
supplies their source-total paid acquisition correspondence,
conditional on its complete access cut. In particular every finite
source in (NMF.8.3) gives the same stipulated retained input.
This uses that producer's supplied contract and imposes no additional
cross-source equality or source-bearing field. $\square$

**Definition 8.3 (biased normalized frontier mass).** For a fixed real
$0<\theta<1$, give a finite address $p$ the weight

$$
\nu_\theta(p)=
 \theta^{\#_L(p)}(1-\theta)^{\#_R(p)}.
$$

For the first-disagreement frontier of Definition 2.1 put

$$
M_\theta(\mathbf u)=
 \sum_{p\in\Delta(\mathbf u)}\nu_\theta(p),
\qquad
D_\theta(s,t)=M_\theta(s,t).
\tag{NMF.8.5}
$$

These are per-original-address weights. In particular
$M_{1/2}=W_{1/2}$; inserted nodes of a marker presentation carry
no extra factor.

**Theorem 8.4 (exact infima on both entire products).** For every
$a\ge1$ and every $0<\theta<1$,

$$
\begin{aligned}
\inf_{(u_0,u_1)\in D_0^{(a)}\times D_1^{(a)}}
 M_\theta(u_0,u_1)
 &=\min(\theta,1-\theta),\\
\inf_{(u_0,u_1,u_2)\in
 D_0^{(a)}\times D_1^{(a)}\times D_2^{(a)}}
 M_\theta(u_0,u_1,u_2)
 &=\min(\theta,1-\theta).
\end{aligned}
\tag{NMF.8.6}
$$

Both infima are attained. The lower bounds hold for every tuple
in the stated entire products, with independent parameters across
alternative originals.

Proof. The elementary cylinder facts needed in this proof can be
expressed entirely at a finite level. Choose a level $n$ beyond the
heights of the finitely many trees being compared. Give a word
$w\in\{L,R\}^n$ weight $\nu_\theta(w)$; the weights sum to
$(\theta+(1-\theta))^n=1$. A cylinder with prefix $p$ has total
weight $\nu_\theta(p)$, since the suffix weights sum to one.
Disjoint cylinders of a prefix-free frontier therefore have total
weight equal to (NMF.8.5).

Along such a word, compare the original reply traces at all its
prefixes, including absent replies below leaves. The traces of $s,t$
differ if and only if that word extends a member of $\Delta(s,t)$.
Indeed any disagreement has a shortest disagreeing prefix.
If the traces of $s,t$ differ, then those of $s,z$ or those of $z,t$
differ. Summing this pointwise event inclusion proves

$$
D_\theta(s,t)\le D_\theta(s,z)+D_\theta(z,t).
\tag{NMF.8.7}
$$

It also proves $0\le D_\theta\le1$.
A pair's trace-disagreement event is contained in the corresponding
multiway event, so its mass is at most the tuple's mass.
Symmetry and positivity of every nonempty cylinder make
$D_\theta$ a metric on finite trees. Only the triangle inequality,
the upper bound one, and the event containment are used below.

The leaf argument in Theorem 8.2 identifies the exact frontier

$$
\Delta(t,St)=\operatorname{Leaf}(t).
\tag{NMF.8.8}
$$

Every original branch agrees before those leaves, and every leaf
already disagrees at its own root. No proper descendant can be a
first disagreement. The leaf cylinders of any finite full binary
tree partition the level-$n$ words for $n$ at least its height:
following any word meets exactly one leaf. Hence

$$
\sum_{p\in\operatorname{Leaf}(t)}\nu_\theta(p)=1,
\qquad D_\theta(t,St)=1.
\tag{NMF.8.9}
$$

This is the usual finite leaf-cylinder partition identity, used
as an intermediate step. It holds for arbitrary uneven finite
trees as well as for perfect trees. The same reasoning gives

$$
\Delta(t,St,S^2t)=\operatorname{Leaf}(t),
\tag{NMF.8.10}
$$

because all three trees retain every original branch of $t$, while
$t$ and $St$ already disagree at every leaf of $t$.

Now take arbitrary independent $s,t\in\mathcal T$.
By (NMF.8.4) these parameterize an arbitrary pair
$u_0=U_a(s,s)$, $u_1=U_a(St,t)$ in the entire pair product.
Set

$$
A=D_\theta(s,St),\qquad
B=D_\theta(s,t),\qquad
C=D_\theta(Ss,St).
$$

The two originals have identical branch exteriors. Their frontier
is the disjoint union of the local frontiers prefixed by $L,RL,RR$.
The multiplicative cylinder weights therefore give the exact identity

$$
M_\theta(u_0,u_1)
 =\theta A+\theta(1-\theta)B+(1-\theta)^2C.
\tag{NMF.8.11}
$$

Apply (NMF.8.7) to $(t,s,St)$ and to $(s,St,Ss)$.
Equation (NMF.8.9) gives respectively

$$
A+B\ge1,\qquad A+C\ge1.
$$

Since $0\le A\le1$ and all coefficients are nonnegative,

$$
\begin{aligned}
M_\theta(u_0,u_1)
 &\ge\theta A+
       \bigl(\theta(1-\theta)+(1-\theta)^2\bigr)(1-A)\\
 &=\theta A+(1-\theta)(1-A)\\
 &\ge\min(\theta,1-\theta).
\end{aligned}
\tag{NMF.8.12}
$$

No shared parameter was assumed in deriving this lower bound.
Taking $s=t$ makes $A=1,B=C=0$, attaining $\theta$.
Taking $s=St$ makes $A=0,B=C=1$, attaining $1-\theta$;
here the assertion about $C$ is (NMF.8.9) applied to $St$.
This proves the pair formula and attainment.

In every tuple of the entire three-row product, its first two
coordinates lie in that entire pair product. Pair-event containment
therefore proves the same lower bound for every triple, irrespective
of its third coordinate. To attain it, choose any finite $t$.
The following two triples belong respectively to all three strata:

$$
\begin{aligned}
\mathbf v_t
 &=\bigl(U_a(t,t),\ U_a(St,t),\ U_a(S^2t,t)\bigr),\\
\mathbf w_t
 &=\bigl(U_a(St,St),\ U_a(St,t),\ U_a(St,S^2t)\bigr).
\end{aligned}
\tag{NMF.8.13}
$$

For $\mathbf v_t$, row-two membership follows from
$S^2t\ne t,St$. Its complete right subtree is common to all
coordinates, and (NMF.8.10) gives

$$
\Delta(\mathbf v_t)=L\operatorname{Leaf}(t),
\qquad M_\theta(\mathbf v_t)=\theta.
\tag{NMF.8.14}
$$

For $\mathbf w_t$, its third coordinate has parameter $y=S^2t$
and $x=St$. The required negatives are $St\ne S^2t$ and
$St\ne S^3t$, obtained from positive shifts on $St$.
All left subtrees equal $St$. At $RL$ the value tuple is
$(St,t,S^2t)$, and at $RR$ it is $(S^2t,St,S^3t)$.
Equation (NMF.8.10), also applied with base $St$, gives

$$
\begin{aligned}
\Delta(\mathbf w_t)
 &=RL\operatorname{Leaf}(t)\ \cup\
   RR\operatorname{Leaf}(St),\\
M_\theta(\mathbf w_t)
 &=\theta(1-\theta)+(1-\theta)^2
 =1-\theta.
\end{aligned}
\tag{NMF.8.15}
$$

Both triples are finite originals satisfying the entire retained
input, by Theorem 8.2. Selecting $\mathbf v_t$ when
$\theta\le1/2$ and $\mathbf w_t$ when $\theta\ge1/2$ proves
the second exact infimum and its attainment. $\square$

**Theorem 8.5 (all-depth finite witnesses in the entire three-row
product).** Put $B=(r_0,r_1,r_2)$ for Definition 8.1.
Then $J_B(h)$ holds for every inclusive depth $h$.
For the perfect trees $A_n$ from the proof of Theorem 4.1,
the actual triple $\mathbf v_{A_n}$ of (NMF.8.13) satisfies

$$
d(\mathbf v_{A_n})=n+1,\qquad
W_q(\mathbf v_{A_n})=q(2q)^n\quad(q>0).
\tag{NMF.8.16}
$$

Proof. The reused perfect-tree calculation gives
$\operatorname{Leaf}(A_n)=\{w:|w|=n\}$.
Equation (NMF.8.14) thus identifies the entire first-disagreement
frontier as $\{Lw:|w|=n\}$. It has $2^n$ points, all at depth
$n+1$, proving both equalities. At requested depth $h$ choose
$n=h$. Theorem 2.2 gives agreement of all four original replies
through $h$, and Theorem 8.2 gives all three exact row labels and
every finite guarded history. These witnesses may change with $h$.
Restricting a triple to its first two coordinates also witnesses
every depth in the entire pair product. $\square$

## 9. The entire-product critical boundary

**Corollary 9.1 (normalized mass cannot replace joint depth).**
For the entire three-row product of Definition 8.1, and also for
its entire $r_0,r_1$ pair product,

$$
\forall h\ J_B(h),\qquad
\inf_{\mathbf u}W_{1/2}(\mathbf u)=\frac12.
\tag{NMF.9.1}
$$

For every fixed $0<\theta<1$, the normalized biased infimum is
$\min(\theta,1-\theta)>0$. For every real $q\ge1/2$,

$$
\inf_{\mathbf u}W_q(\mathbf u)\ge\frac12.
\tag{NMF.9.2}
$$

For every rational $0<q<1/2$, the infimum remains zero.

Proof. Combine Theorems 8.4–8.5 and $M_{1/2}=W_{1/2}$.
For $q\ge1/2$, every frontier term satisfies
$q^{|p|}\ge2^{-|p|}$, so every tuple has
$W_q\ge W_{1/2}\ge1/2$. For $0<q<1/2$ the finite triples
in (NMF.8.16) have masses tending to zero; their pair restrictions
have the same frontier. This also directly instantiates the valid
strict-discount equivalence of Theorem 3.2.

The paragraph following Theorem 4.1 leaves failure of the reverse
critical zero-infimum implication on entire signed row products
unasserted. Equations (NMF.8.12) and (NMF.9.1) supply that
entire-product counterexample. Theorem 4.1 itself concerns a
different input, (NMF.13), whose entire critical infimum is zero;
its conclusion remains as stated. A balanced subsequence alone
could not establish (NMF.9.1). The all-tuple lower bound is what
prevents an alternative source tuple from decreasing this
infimum to zero. $\square$

**Definition 9.2 (supplier scope and remaining recovery obligation).**
The complete-row and guarded-epoch meanings are those of
Definitions 1.1–1.2 and [ARH, Definitions 1.1–1.2][ARH].
The acquisition correspondence is conditional on ARH Assumption 1.3
and uses its Proposition 2.1. [NIC, Theorems 3.2 and 4.3][NIC]
already supply exact whole-source image normalization and reconstruction;
the direct descriptions (NMF.8.3)–(NMF.8.4) instantiate that scope
for this input. No missing positive residual normalizer is presumed.

The finite cylinder identity and triangle inequality in the proof
of Theorem 8.4 are standard intermediate facts. The deductions here
are their exact all-tuple native shift-copy bound, its attaining
three-row tuples, and its whole retained-source correspondence.
They carry no external-priority assertion.

The minimum original mismatch depth and the every-branch marker
count of Theorem 2.5 continue to agree on these witnesses.
The every-branch diagonal property of
[Barozzini, Clemente, Colcombet and Parys, §4.4][BCCP44]
counts markers on every branch of one chosen tree; it is not a
normalized branching probability. Its safe-scheme decision in
[§5][BCCP5] still has the exact-carrier premise of Definition 6.1.
Corollary 9.1 refutes substitution of normalized mass for that
depth property, and supplies no faithful safe carrier.

Thus Open problem 7.3 remains the unrestricted recovery and
classification obligation for the entire coupled original sources.
The finite negative $y\ne Sy$ is proved on each finite source.
It need not hold at the all-branch completion $\Omega$, where
$\rho\Omega=\Omega$. No infinite negative, free observer port,
acquisition cost bound, native undecidability or general stopping
theorem follows from the mass obstruction.

## 追加锚（本行以下为增补区）

## 10. Even substitution is a strict-discount contraction

**Definition 10.1 (the even substitution map).** Put

$$
E(u)=\rho^2u.
$$

The native equations give

$$
E(\alpha)=\langle\beta,\alpha\rangle,
\qquad
E(\beta)=\langle\langle\beta,\alpha\rangle,\beta\rangle,
\qquad
E(\langle s_0,s_1\rangle)=\langle E(s_0),E(s_1)\rangle.
\tag{NMF.10.1}
$$

Thus $E(u)$ is a branch for every finite nonempty native $u$.

**Lemma 10.2 (the complete root cases).** Fix a rational
$0<q<1/2$. For finite native $s,t$ the following cases exhaust the
roots.

1. If $s=t$, then $D_q(E(s),E(t))=0$.
2. If $s,t$ are distinct leaves, then
   $D_q(E(s),E(t))=2q$.
3. If exactly one of $s,t$ is a branch, then
   $D_q(E(s),E(t))\le2q$.
4. If $s=\langle s_0,s_1\rangle$ and
   $t=\langle t_0,t_1\rangle$, then

   $$
   D_q(E(s),E(t))
   =q\bigl(D_q(E(s_0),E(t_0))
          +D_q(E(s_1),E(t_1))\bigr).
   \tag{NMF.10.2}
   $$

Proof. The first case is substitution of equal terms. In the second,
the two roots in (NMF.10.1) are both branches. For the pair
$(\alpha,\beta)$, its left replies are $\beta$ and
$\langle\beta,\alpha\rangle$, and its right replies are $\alpha$ and
$\beta$; hence its frontier is exactly $\{L,R\}$ and its mass is
$2q$. The same calculation with the order of the leaves exchanged is
identical.

In the third case, (NMF.10.1) makes both transformed roots branches.
The metric recursion of Theorem 3.3 applies at this common branch root,
and each of the two child distances is at most one by that theorem.
Consequently the transformed distance is at most $q(1+1)=2q$.
The fourth case is the same metric recursion, now with the displayed
child identities in (NMF.10.1). These cases include every combination
of leaf and branch roots. $\square$

**Theorem 10.3 (two-step native contraction).** For every finite
nonempty native $s,t$ and every rational $0<q<1/2$,

$$
\boxed{
D_q(\rho^2s,\rho^2t)\le 2q\,D_q(s,t).}
\tag{NMF.10.3}
$$

Proof. Use structural induction on the pair $(s,t)$. Equal inputs give
zero on both sides. If $s,t$ are distinct leaves, their root frontier is
$\{\varepsilon\}$, so $D_q(s,t)=1$; Lemma 10.2 gives equality with
$2q$. If exactly one input is a branch, the original root is already a
first disagreement, hence again $D_q(s,t)=1$, and the third case of the
lemma proves the bound.

It remains that both inputs are branches. Their original metric
recursion is

$$
D_q(s,t)=q\bigl(D_q(s_0,t_0)+D_q(s_1,t_1)\bigr).
$$

Each child pair is structurally smaller, so the induction hypotheses and
(NMF.10.2) give

$$
\begin{aligned}
D_q(E(s),E(t))
&\le q\bigl(2qD_q(s_0,t_0)+2qD_q(s_1,t_1)\bigr)\\
&=2qD_q(s,t).
\end{aligned}
$$

This is a map-level Lipschitz estimate for $E$. The recursion in
Theorem 3.3 is only the equality for a pair whose two displayed roots
are both branches; it does not by itself cover the leaf--branch case
or the distinct-leaf case used above. $\square$

**Corollary 10.4 (all iterates, including equality and zero steps).**
For every finite nonempty native $s,t$, every rational $0<q<1/2$,
and every $n\in\mathbb N_0$,

$$
\boxed{
D_q(\rho^{2n}s,\rho^{2n}t)
\le (2q)^nD_q(s,t).}
\tag{NMF.10.4}
$$

For $n=0$ this is equality. If $s=t$, both sides are zero for every
$n$. For the induction step apply Theorem 10.3 to
$\rho^{2n}s,\rho^{2n}t$ and use
$\rho^{2(n+1)}=\rho^2\!\circ\rho^{2n}$:

$$
D_q(\rho^{2(n+1)}s,\rho^{2(n+1)}t)
\le2qD_q(\rho^{2n}s,\rho^{2n}t)
\le(2q)^{n+1}D_q(s,t).
$$
$\square$

**Proposition 10.5 (sharp coefficient at the atomic pair).** For every
rational $0<q<1/2$,

$$
D_q(\rho^2\alpha,\rho^2\beta)
=2q
=2q\,D_q(\alpha,\beta).
\tag{NMF.10.5}
$$

Hence no constant smaller than $2q$ can replace $2q$ in
(NMF.10.3) uniformly over finite native inputs. This is exact equality
at $(s,t)=(\alpha,\beta)$, not an asymptotic estimate.

## 11. Atomic trajectory and the critical boundary

**Definition 11.1 (the even atomic pair).** For $n\in\mathbb N_0$ put

$$
A_n=\rho^{2n}\alpha,\qquad B_n=\rho^{2n}\beta.
\tag{NMF.11.1}
$$

The finite-source supplier [SLH, Lemma 55.2 and Theorem 55.3][SLH]
already establishes, in its own source and readout contract, that the
first disagreement of $A_n,B_n$ has address depth $n$ and that a current
read at the right address $R^n$ distinguishes the atomic value. Those
are reused address-depth and one-read facts. They are not a new theorem
of this section and do not assert that one read, or the address $R^n$,
is an optimal physical read strategy.
This denial concerns physical-strategy optimality and leaves intact any
combinatorial address/call minima the supplier establishes under its own
contract.

The metric consequence supplied by Corollary 10.4 is the separate
inequality

$$
D_q(A_n,B_n)\le(2q)^nD_q(\alpha,\beta)=(2q)^n.
\tag{NMF.11.2}
$$

At the boundary $q=1/2$, for every finite nonempty native $s,t$ and
every $n\in\mathbb N_0$, the same finite root calculation gives the
nonexpansive inequality:

$$
D_{1/2}(\rho^{2n}s,\rho^{2n}t)\le D_{1/2}(s,t).
\tag{NMF.11.3}
$$

For the one-step bound, equal inputs have empty frontiers before and
after $E$. If the original roots disagree, then their frontier is
$\{\varepsilon\}$, so $D_{1/2}(s,t)=1$. By (NMF.10.1) both
$E$-images are branches, and each of their two corresponding child
distances is at most one by the finite prefix-free frontier/Kraft bound.
Their distance is therefore at most $\tfrac12(1+1)=1$. At a common
original branch, splitting the frontier into its $L$ and $R$ parts gives
one half of the sum of the child distances; structural induction on the
two smaller child pairs proves the one-step inequality there. Iterating
this inequality proves (NMF.11.3), including equality at $n=0$.

The already established balanced witnesses of Theorem 4.1, and the
pair restrictions recorded in Theorem 8.5, give the reused critical
trajectory

$$
W_{1/2}(\mathbf u_n)=\frac12\qquad(n\ge0).
\tag{NMF.11.4}
$$

Here $\mathbf u_n$ denotes the balanced tuple sequence of Theorem 4.1,
constructed from its recursively doubled perfect trees. This is a
different family from the even atomic pair $(A_n,B_n)$ in Definition 11.1.

Thus the strict-discount decay in (NMF.10.4) has the correct critical
boundary. Equation (NMF.11.4) is a reused consequence of those existing
frontier witnesses; it is not an additional claim about the metric value
of the atomic pair in (NMF.11.1).

## 12. Scope of substitution, resources, and the finite limit

**Definition 12.1 (scope of the pointwise estimate).** The domain of
(NMF.10.3) and (NMF.10.4) is the set of finite nonempty native trees.
No row label, acquired history, or joint original product is a parameter
of either inequality. Simultaneous substitution by $\rho^{2n}$ therefore
need not preserve a fixed acquired row/history fiber or carry a joint
tuple of original sources into the same product. The estimates are
pointwise statements about the native algebra and the frontier metric.

**Proposition 12.2 (separate depth, calls, cost, and limit statements).**
For the atomic pair in Definition 11.1, the supplier's depth statement
is an address-depth statement ($n$), and its one-read statement is a
call-count statement (one current read at $R^n$). The combinatorial word
$R^n$ has address length $n$; no physical fee, transport time, source
acquisition price, or physical-strategy optimality of that call follows
from either fact. This leaves intact any combinatorial address/call
minima the supplier establishes under its own contract.

For fixed finite $s,t$ and rational $0<q<1/2$, (NMF.10.4) gives the
separate scalar limit

$$
\lim_{n\to\infty}D_q(\rho^{2n}s,\rho^{2n}t)=0,
\tag{NMF.12.1}
$$

because $0<2q<1$. This is a limit of metric values for finite trees. It
does not assert an infinite native tree $\lim_n\rho^{2n}s$, an infinite
physical execution, a finite or infinite call bound, convergence of row
labels or histories, or any physical-cost theorem. At $q=1/2$ only
(NMF.11.3) and the reused critical boundary (NMF.11.4) are available.

[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md

## 追加锚（本行以下为增补区）

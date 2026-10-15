# Native cyclic information transport: component certificates and a sharp proper-subalphabet bound

## 1. Scope, predecessor and finite recovery semantics

**Convention 1.1 (mathematical scope and attribution).** This volume
develops ordinary finite mathematics for recovery of one requested
target from a constant answer or one reply. Its substantive predecessor,
denoted NCM, is *Recursive relational observation: an all-correlated
native memory lower bound*. NCM §2 proves transport through donors
whose reply capacity forces them to be locally admissible; NCM §6
supplies the five-tree alphabet, its mutual-assistance pair and its
paid native attainment. The results below retain closed donor components
as weighted cyclic sums and establish a sharp bound on that particular
proper subalphabet. The scope is every correlated joint fiber on that
subalphabet, with each target served separately.

The separately credited source
[NCE, *Recursive relational observation: a native cyclic entropy lower
certificate*](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md)
supplies a heavy-target squared-cell entropy certificate allowing
arbitrary cyclic donors (Theorem 2.2), exact complete-$S_3$ weights
and an all-joint fractional lower (Theorem 6.1), and a stronger
native full-family lower (Theorem 6.2). These are ordinary supplied
theory, without inherited kernel certification or certification of
its cited sources. Their endpoint and conditions are recalled in §9.3;
the exact component, proper-$P$ and cycle results below remain distinct.

NCM's exact temporal-factor interface and its actual-occurrence
transport are conditional inputs to the operational interpretation in
§8. FMR, AAR and NBP denote the predecessors credited by NCM: *Late
Target Fractional Memory Rate*, *Adaptive Acquired Reference Frontier*
and *Native Birth Provenance*, respectively. Their interfaces retain
their stated conditions. In particular the depth-two seed, cover
correspondence, harmonic rounding, rate existence and paid service
assumptions are predecessor results. Finite functional graphs, finite
product-weight summation, transfer matrices, Fibonacci--Lucas
recurrences and fractional covering are classical tools. The contribution
claimed here is the component certificate and its consequences relative
to the supplied NCM theory; no worldwide priority or formal certification
is asserted.

**Definition 1.2 (finite interface).** Let $S$ be a finite nonempty
set. Let $Q$ and $\mathcal A$ be finite sets of target and experiment
indices. For each $q\in Q$ and $a\in\mathcal A$ fix functions

$$
g_q:S\longrightarrow Y_q,\qquad
r_a:S\longrightarrow V_a.
\tag{CIT.1}
$$

Fix an integer $m\ge2$ such that $|r_a(S)|\le m$ for every
experiment. Only attained values of these functions matter. Constant
experiments may be included, and a constant answer always requires
zero experiments.

For an integer $n\ge1$, a nonempty $B\subseteq S^n$ is jointly
admissible if, for every coordinate $i\in[n]$ and target $q\in Q$,
either $g_q(x_i)$ is constant as $x$ ranges over $B$, or there are
$j\in[n]$ and $a\in\mathcal A$ such that

$$
\forall x,y\in B,\qquad
r_a(x_j)=r_a(y_j)\ \Longrightarrow\ g_q(x_i)=g_q(y_i).
\tag{CIT.2}
$$

The donor $j$ and experiment $a$ may depend on $B,i,q$. Every one
of these implications is required on the same unchanged $B$. Different
targets may use different experiments; there is no requirement that one
reply determine their vector. Local admissibility of $P\subseteq S$
means this condition in one coordinate. The empty set is admissible
vacuously whenever it is useful to include it. A nonempty $P$ is
range feasible if $|g_q(P)|\le m$ for every $q$; this is a necessary
condition on joint projections, without an assertion of sufficiency.

**Definition 1.3 (analytical weights).** Fix any function
$w:S\to[0,\infty)$. For $P\subseteq S$ and $B\subseteq S^n$ put

$$
w(P)=\sum_{z\in P}w(z),\qquad
\Omega(B)=\sum_{x\in B}\prod_{i=1}^n w(x_i).
\tag{CIT.3}
$$

These product weights are a device for summation. They impose no
probabilistic law, independence, product form or admissibility condition
on a competitor $B$. All products indexed by an empty set equal one.

## 2. A heterogeneous component certificate

**Theorem 2.1 (missing-target components and exact cyclic traces).**
Fix the finite interface and weights of §1, $n\ge1$ and a nonempty
jointly admissible $B\subseteq S^n$. Write $P_i=\pi_i(B)$, let
$G$ be the indices with locally admissible $P_i$, and let
$I=[n]\setminus G$. For each $i\in I$, choose any locally missing
target $h_i=g_{q_i}$: it is neither constant nor determined by an
own-coordinate experiment on $P_i$. Define

$$
V_i=h_i(P_i),\qquad t_i=|V_i|,\qquad
c_i=\max_{v\in V_i}\sum_{\substack{z\in P_i\\h_i(z)=v}}w(z).
\tag{CIT.4}
$$

For every such choice, joint admissibility gives a donor $j(i)$,
experiment $a_i$ and a decoder with precisely the domain and codomain

$$
d_i:r_{a_i}(P_{j(i)})\longrightarrow V_i,
\qquad
h_i(x_i)=d_i(r_{a_i}(x_{j(i)}))\quad(x\in B).
\tag{CIT.5}
$$

Necessarily $j(i)\ne i$ and $2\le t_i\le m$. Give each bad
vertex $i\in I$ its single edge $i\to j(i)$; good vertices have
no outgoing edge. Each weak component has one good terminal root or
one directed cycle of length at least two. Let $\mathcal K$ be the
set of these cycles and let $J$ be the bad vertices outside them.

For a cycle $C=(i_1,\ldots,i_\ell)$ ordered by
$j(i_s)=i_{s+1}$, with subscripts interpreted cyclically, define
$V_s=V_{i_s}$, $V_0=V_\ell$ and the rectangular matrix

$$
T_s(v_s,v_{s-1})=
\sum_{\substack{z\in P_{i_s}\\
h_{i_s}(z)=v_s\\
d_{i_{s-1}}(r_{a_{i_{s-1}}}(z))=v_{s-1}}}w(z),
\qquad (v_s,v_{s-1})\in V_s\times V_{s-1}.
\tag{CIT.6}
$$

Thus $T_s$ has $t_{i_s}$ rows and $t_{i_{s-1}}$ columns. Put
$\tau_C=\operatorname{tr}(T_\ell\cdots T_1)$. Then

$$
\boxed{
\Omega(B)\le
\prod_{i\in G}w(P_i)
\prod_{i\in J}c_i
\prod_{C\in\mathcal K}\tau_C,
\qquad
\tau_C\le\left(\min_{i\in C}t_i\right)\prod_{i\in C}c_i.
}
\tag{CIT.7}
$$

Proof. Local inadmissibility supplies a missing target by the
definition. Such a target is nonconstant because a constant target
has a zero-experiment answer. Apply (CIT.2) to it. On any attained
donor reply, choose a tuple of $B$ having that reply and define the
decoder to be its target value. The implication makes this value
independent of the chosen tuple. Every element of $P_{j(i)}$ occurs
in a tuple of the original $B$, so this defines $d_i$ on the whole
domain in (CIT.5). Its image equals $V_i$, since every target value
also occurs in a tuple. Therefore $2\le t_i\le|r_{a_i}(P_{j(i)})|
\le m$.

If $j(i)=i$, take any $u,v\in P_i$ and tuples of $B$ attaining
them at coordinate $i$. Equality of their $a_i$ replies forces
$h_i(u)=h_i(v)$. This is exactly an own-coordinate decoder on $P_i$,
contradicting the choice of $h_i$. Thus there are no self-loops.

Following outgoing edges in a finite graph either terminates at a
good vertex or eventually repeats a vertex, giving a directed cycle.
An edge has the same eventual terminal root or cycle at both ends.
Consequently this eventual object is the same throughout a weak
component. There is exactly one such object per component, and a
cycle has length at least two. The other vertices form directed trees
feeding it.

Consider the relational relaxation

$$
H=\left\{x\in\prod_{i=1}^nP_i:
h_i(x_i)=d_i(r_{a_i}(x_{j(i)}))\text{ for every }i\in I\right\}.
\tag{CIT.8}
$$

The decoder domains already proved make every equation meaningful on
the full product. We have $B\subseteq H$, whence
$\Omega(B)\le\Omega(H)$ by nonnegativity. No admissibility claim
is made about $H$, and $H$ is not substituted for an operational
competitor.

In any remaining directed tree, choose a bad noncycle vertex with no
remaining incoming edges. Its variable occurs only in its own outgoing
equation. At fixed values of every other remaining variable, summing
over this variable is summing one $h_i$-cell, of weight at most $c_i$.
Remove that variable and equation, replacing its sum by this constant
upper bound. Repeat until every off-cycle bad vertex has been removed.
Such a vertex exists whenever an off-cycle tree is nonempty, by taking
a vertex farthest from its terminal object. Already removed descendants
have contributed only constant nonnegative upper factors. This step
uses finite summation, without division or conditional independence.
A good terminal root then contributes its unrestricted sum $w(P_i)$.

For a surviving cycle put $v_s=h_{i_s}(x_{i_s})$. Its incoming
equation, from vertex $i_{s-1}$, requires the second condition in
(CIT.6). At fixed cyclic values $v_1,\ldots,v_\ell$, the sum over
the coordinate choices equals $\prod_sT_s(v_s,v_{s-1})$. The exact
remaining cycle sum is therefore

$$
\sum_{v_\ell\in V_\ell}
\sum_{v_1\in V_1,\ldots,v_{\ell-1}\in V_{\ell-1}}
T_\ell(v_\ell,v_{\ell-1})\cdots T_1(v_1,v_\ell)
=\operatorname{tr}(T_\ell\cdots T_1).
\tag{CIT.9}
$$

The product is conformable: $T_2T_1$ has rows $V_2$ and columns
$V_\ell$, and the full product is square on $V_\ell$. Distinct
components of $H$ have disjoint variables and constraints. Distributivity
of finite sums consequently separates their weights. Together with the
tree elimination this proves the first inequality in (CIT.7), even
though $B$ itself may have correlations between components.

For fixed $v_s$, every element of its $h_{i_s}$-cell contributes
to exactly one column of $T_s$: the predecessor decoder is defined
and takes a value in $V_{s-1}$. Thus each row sum equals the weight
of this cell and is at most $c_{i_s}$. If nonnegative conformable
matrices $A,B$ have row sums bounded by $a,b$, respectively, then

$$
\sum_k(AB)_{ik}
=\sum_j A_{ij}\sum_kB_{jk}
\le b\sum_jA_{ij}\le ab.
\tag{CIT.10}
$$

The cyclic square product has all row sums at most
$\prod_{i\in C}c_i$. Its trace is at most its number of rows
times this bound. The finite sum (CIT.9) is invariant under cyclic
renaming of its indices. Cutting it at any vertex gives the same
sum as a trace of order $t_i$, even for unequal state-set sizes.
Choose the smallest such order. This proves the second inequality.
$\square$

**Remark 2.2 (degenerate cases and the graph's meaning).** The graph
records a chosen valid witness for one actually missing target at each
bad projection. It is neither a pair-confusability graph nor a replacement
for the other target obligations. All their witnesses remain required
on $B$. Zero point weights, zero cell weights and zero traces are
permitted in every step of the proof. If any projection has weight
zero, every tuple of $B$ has product weight zero. There are no bad
coordinates when $n=1$: the joint condition is then the local one,
and (CIT.7) reduces to $\Omega(B)=w(P_1)$. The proof includes
$m=2$, where each cycle has at least two vertices and trace cost at
most twice its cell-weight product. An empty $B$ has weight zero
without any choice of projections or graph.

## 3. A sufficient uniform criterion and finite covering

**Theorem 3.1 (uniform cyclic certificate).** In the interface of §1
let $C>0$ and $c\ge0$. Assume that every locally admissible subset
has weight at most $C$, and that every nonempty range-feasible locally
inadmissible subset has at least one missing target whose every cell
has weight at most $c$. No deficient-reply-capacity hypothesis is
imposed on these subsets. For every nonempty jointly admissible
$B\subseteq S^n$, choose such targets and any of their actual joint
witnesses. If $g,b$ are the numbers of good and bad projections and
$\kappa$ is the number of cycles of the resulting graph, then

$$
\Omega(B)\le C^g c^b m^\kappa
\le C^g(\sqrt m\,c)^b
\le\max\{C,\sqrt m\,c\}^{\,n}.
\tag{CIT.11}
$$

In particular $\sqrt m\,c\le C$ suffices for
$\Omega(B)\le C^n$ for every $n\ge1$ and every joint fiber.

Proof. Every target on each exact projection of $B$ has at most
$m$ values: it is constant or factors through one of the allowed
replies on $B$. Thus every projection is range feasible and the
stipulated missing targets can be selected. Theorem 2.1 gives the
first bound because $c_i\le c$ and $\min_{i\in C}t_i\le m$.
Cycles are vertex-disjoint and use at least two bad coordinates each,
so $2\kappa\le b$. For $c>0$ this gives the remaining inequalities
directly, since $g+b=n$. If $c=0$ and $b>0$, all cells of a selected
target on a bad projection have weight zero. Their finite union is the
whole projection, hence $\Omega(B)=0$. If $b=0$, the empty
$c$-product equals one. This also proves (CIT.11) at $c=0$ without
division or an ambiguous power. Empty fibers again have weight zero.
$\square$

The criterion is sufficient only. NCM Theorem 2.2 instead forces each
bad donor edge directly to a good projection by a reply-capacity
separation and can use $c\le C$. Failure of either sufficient
criterion supplies no impossibility theorem for other certificates.

**Corollary 3.2 (nonnegative covering dual and integral rounding).**
Under the hypotheses of Theorem 3.1 with $\sqrt m\,c\le C$, let
$Z(n)$ and $K(n)$ be the fractional and integral covering optima of
$S^n$ by the entire family of nonempty jointly admissible subsets.
Then

$$
y(x)=C^{-n}\prod_iw(x_i),\qquad
\left(\frac{w(S)}C\right)^n\le Z(n),\qquad
\left\lceil\left(\frac{w(S)}C\right)^n\right\rceil\le K(n),
\tag{CIT.12}
$$

and the classical finite harmonic rounding bound is

$$
Z(n)\le K(n)\le H_{|S|^n}Z(n),\qquad
H_N=\sum_{j=1}^N\frac1j.
\tag{CIT.13}
$$

These formulas do not assert equality of either optimum with the
displayed weight lower bound.

Proof. Theorem 3.1 says $\sum_{x\in B}y(x)\le1$ for every
admissible $B$, and $y\ge0$. For any fractional cover
$\alpha_B\ge0$ with $\sum_{B\ni x}\alpha_B\ge1$,

$$
\left(\frac{w(S)}C\right)^n
=\sum_xy(x)
\le\sum_xy(x)\sum_{B\ni x}\alpha_B
=\sum_B\alpha_B\sum_{x\in B}y(x)
\le\sum_B\alpha_B.
\tag{CIT.14}
$$

This proves the dual direction. An integral cover gives the same
inequality with its number of members on the right, and that number
is an integer, proving the ceiling. Overlaps do not affect the argument.

For completeness, the finite harmonic rounding used here is purely
combinatorial. Singletons are admissible, so a cover exists. Greedily
choose a member covering the most uncovered points until all
$N=|S|^n$ points are covered. Charge each newly covered point the
reciprocal of the number newly covered in that step. Total charge is
the number of chosen members. For any fixed admissible set $A$, when
$j$ of its points remain uncovered, a greedy step covers at least
$j$ points overall, since $A$ itself is available. If that step
covers $r$ points of $A$, their total charge is at most $r/j$,
which is at most $1/j+1/(j-1)+\cdots+1/(j-r+1)$. Summing the
steps gives total charge on $A$ at most $H_{|A|}\le H_N$.
Multiply a fractional cover's inequalities by the nonnegative point
charges and sum. The greedy cover size is at most
$H_N\sum_A\alpha_A$. Minimizing over fractional covers proves
the upper bound in (CIT.13); the lower bound follows because every
integral cover is a fractional one. This reuses the classical covering
argument also credited in NCM and FMR. It supplies neither a new local
primal cover nor an operational acquisition procedure. $\square$

## 4. The native five-tree interface, with every experimental word

**Definition 4.1 (literal trees and canonical alphabet).** Trees have
the ordered grammar

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,\qquad
h(\langle x,y\rangle)=1+\max\{h(x),h(y)\}.
\tag{CIT.15}
$$

An experiment is any finite word $w\in\{L,R\}^{<\infty}$,
including $\varepsilon$. The original-root reply $r_u(w)$ is
$\alpha$ or $\beta$ at that leaf, $\mathsf{branch}$ at a pair,
and $\mathsf{absent}$ after a path passes beyond a leaf. Define the
canonical alphabets exactly as in NCM:

$$
S_1=\{\alpha,\beta,\langle\alpha,\alpha\rangle\},\qquad
S_{d+1}=\{\alpha,\beta\}\ \sqcup
\{\langle x,y\rangle:x,y\in S_d\},\qquad
W_d=\{q:|q|\le d-1\}.
\tag{CIT.16}
$$

The depth-three targets are the seven distinct words
$W_3=\{\varepsilon,L,R,LL,LR,RL,RR\}$. Put

$$
\begin{aligned}
A&=\alpha,& B&=\beta,& C_0&=\langle A,A\rangle,&
J_0&=\langle B,A\rangle,& Q_0&=\langle C_0,A\rangle,\\
u_0&=\langle A,A\rangle,&
u_1&=\langle B,A\rangle,&
u_2&=\langle C_0,C_0\rangle,&
u_3&=\langle J_0,J_0\rangle,&
u_4&=\langle A,Q_0\rangle,\\
P&=\{u_0,u_1,u_2,u_3,u_4\},&&
F=\{u_0,u_1,u_2,u_3\}.
\end{aligned}
\tag{CIT.17}
$$

This is the literal alphabet of NCM (NCM.25), with different names
for the auxiliary trees to avoid confusion with mass constants.
The five trees are distinct, each belongs to $S_3$, and
$P\subsetneq S_3$: the leaf $\alpha$ is in $S_3$ and outside $P$.
Membership follows directly from (CIT.16): $C_0\in S_1$,
$J_0,Q_0\in S_2$, and every child used to construct a $u_s$
belongs to $S_2$.

**Convention 4.2 (the supplied temporal factor).** Use the substitution
and the temporal factor of NCM §1, attributed there to AAR:

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{CIT.18}
$$

Write $s(r)=\#L(r)+2\#R(r)$ and $e(\alpha)=0,e(\beta)=1$.
If $q$ ends at an original branch, $\Gamma_q(u)=(0,0)$. Otherwise
let $\ell$ be the first original leaf on the path, at prefix $a$,
and write $q=ar$. The supplied static formula is

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{CIT.19}
$$

For attained pairs $(b,c)$ the supplied trajectory decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1\text{ and }k=b-1,\\
\alpha,&c=1\text{ and }k=b-2,\\
\mathsf{absent},&\text{otherwise},
\end{cases}\qquad k\in\mathbb N_0.
\tag{CIT.20}
$$

Here $c\in\{0,1\}$ and $c=1$ implies $b\ge2$. The conditional
interface used in §8 is
$r_{\rho^ku}(q)=\operatorname{Pred}(\Gamma_q(u),k)$ for all
$k\ge0$, with equality of factors equivalent to equality of the
entire trajectories. Its inverse identifies $b$ from the first branch
count and $c$ from the alpha stage. This is temporal-factor recovery,
not full-source or first-leaf-descriptor recovery. The formula and this
exact temporal correspondence retain their predecessor attribution;
the static tables and deductions below use them at that scope.

**Lemma 4.3 (complete replies, factors and finite-word reduction).**
On $P$, with columns in the order $u_0,u_1,u_2,u_3,u_4$, the reply
table at the seven boundary words is

$$
\begin{array}{c|ccccc}
q&r_{u_0}(q)&r_{u_1}(q)&r_{u_2}(q)&r_{u_3}(q)&r_{u_4}(q)\\\hline
\varepsilon&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}\\
L&\alpha&\beta&\mathsf{branch}&\mathsf{branch}&\alpha\\
R&\alpha&\alpha&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}\\
LL&\mathsf{absent}&\mathsf{absent}&\alpha&\beta&\mathsf{absent}\\
LR&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha&\mathsf{absent}\\
RL&\mathsf{absent}&\mathsf{absent}&\alpha&\beta&\mathsf{branch}\\
RR&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha&\alpha
\end{array}
\tag{CIT.21}
$$

The target table, evaluated by (CIT.19), is

$$
\begin{array}{c|ccccc}
q&\Gamma_q(u_0)&\Gamma_q(u_1)&\Gamma_q(u_2)&\Gamma_q(u_3)&\Gamma_q(u_4)\\\hline
\varepsilon&(0,0)&(0,0)&(0,0)&(0,0)&(0,0)\\
L&(2,1)&(1,0)&(0,0)&(0,0)&(2,1)\\
R&(2,1)&(2,1)&(0,0)&(0,0)&(0,0)\\
LL&(3,0)&(2,0)&(2,1)&(1,0)&(3,0)\\
LR&(4,1)&(3,1)&(2,1)&(2,1)&(4,1)\\
RL&(3,0)&(3,0)&(2,1)&(1,0)&(0,0)\\
RR&(4,1)&(4,1)&(2,1)&(2,1)&(2,1)
\end{array}
\tag{CIT.22}
$$

Every length-three experiment is a public function of its length-two
parent reply, and every length-at-least-four experiment is constant
absent. Thus the finite interface with the seven experiments in $W_3$
has exactly the same local and joint admissible sets on $P^n$ as the
interface allowing all finite experimental words. All experiments have
at most $m=4$ replies.

Proof. The root of each tree is a pair. Their left children are,
in order, $A,B,C_0,J_0,A$ and their right children are
$A,A,C_0,J_0,Q_0$, giving the first three reply rows. Following one
further edge gives respectively the four rows $LL,LR,RL,RR$ displayed
in (CIT.21): the only branch at depth two is $C_0$ at $RL$ in
$u_4$. Its two children are alpha leaves.

For the factor table, a branch endpoint contributes $(0,0)$ and an
actual alpha or beta leaf endpoint contributes $(2,1)$ or $(1,0)$.
These rules give the entire root, $L$ and $R$ rows. In $u_0,u_1,u_4$,
the left leaf precedes the $LL$ and $LR$ endpoint: the remaining
letter contributes $s(L)=1$ or $s(R)=2$, with last-letter bit zero
or one. This gives their entries $(3,0),(2,0),(3,0)$ in $LL$ and
$(4,1),(3,1),(4,1)$ in $LR$. The corresponding endpoints in
$u_2,u_3$ are actual leaves, giving $(2,1),(1,0)$ in $LL$ and
$(2,1),(2,1)$ in $LR$. In $u_0,u_1$, the right leaf is alpha,
so $RL$ and $RR$ give $(3,0)$ and $(4,1)$. In $u_2,u_3$ their
right children have leaves alpha or beta on the left, and alpha on
the right, giving the stated entries. Finally $u_4$ has a branch
at $RL$ and an alpha leaf at $RR$, giving $(0,0)$ and $(2,1)$.
This accounts for every entry of (CIT.22).

For a length-three word $ab$, where $|a|=2$ and $b$ is one letter,
its reply is alpha precisely if $r_u(a)=\mathsf{branch}$; otherwise
it is absent. Indeed the only possible depth-two branch just identified
has two alpha children, and an endpoint that is a leaf or absent has
no child. This supplies the same reply function for either final letter.
All trees of $P$ have height at most three, so a longer word is absent.
For any implication using a coarsened experiment, equality of the
parent replies entails equality of the coarsened replies and hence the
same target equality. The donor coordinate and unchanged joint set are
preserved. A constant reply can serve only a constant target. Conversely
the seven boundary experiments are available in the full interface.
This proves equivalence for every coordinate and target separately,
including arbitrary off-coordinate donors. $\square$

**Lemma 4.4 (all six nonmissing targets have local witnesses).** On
the whole $P$ the following complete attained-reply decoders recover
the indicated targets in their own coordinate:

| Target | Experiment | Decoder on all its attained replies |
| --- | --- | --- |
| $\varepsilon$ | none | constant $(0,0)$ |
| $L$ | $L$ | $\alpha\mapsto(2,1)$, $\beta\mapsto(1,0)$, $\mathsf{branch}\mapsto(0,0)$ |
| $R$ | $R$ | $\alpha\mapsto(2,1)$, $\mathsf{branch}\mapsto(0,0)$ |
| $LR$ | $L$ | $\alpha\mapsto(4,1)$, $\beta\mapsto(3,1)$, $\mathsf{branch}\mapsto(2,1)$ |
| $RL$ | $RL$ | $\mathsf{absent}\mapsto(3,0)$, $\alpha\mapsto(2,1)$, $\beta\mapsto(1,0)$, $\mathsf{branch}\mapsto(0,0)$ |
| $RR$ | $R$ | $\alpha\mapsto(4,1)$, $\mathsf{branch}\mapsto(2,1)$ |

Proof. The root factor is constant. For $L,R$, the corresponding
reply in (CIT.21) selects exactly the endpoint factor in (CIT.22).
For $LR$, the $L$ reply classes are $\{u_0,u_4\}$,
$\{u_1\}$ and $\{u_2,u_3\}$; their factors are respectively
$(4,1),(3,1),(2,1)$. The $RL$ reply classes are
$\{u_0,u_1\},\{u_2\},\{u_3\},\{u_4\}$, with precisely
the four indicated $RL$ factors. For $RR$, the $R$ reply classes
are $\{u_0,u_1\}$ and $\{u_2,u_3,u_4\}$, with factors
$(4,1)$ and $(2,1)$. These domains exhaust the replies attained on
$P$; no value on an unattained reply is needed. Every decoder
restricts to any subset of $P$. $\square$

## 5. Exact local characterization and sharp mass on the proper alphabet

**Theorem 5.1 (local admissibility inside $P$).** For every
$A\subseteq P$, with all seven $W_3$ targets and all finite native
experimental words, $A$ is locally admissible if and only if
$F\nsubseteq A$.

Proof. Denote the four $LL$ values by

$$
a=(3,0),\qquad b=(2,0),\qquad c_*=(2,1),\qquad d=(1,0).
\tag{CIT.23}
$$

On $F$, this target has the four different values $a,b,c_*,d$.
The numbers of replies on $F$ at the seven boundary experiments,
in their displayed order, are $1,3,2,3,2,3,2$. No experiment with
at most three reply classes can determine a four-valued target.
Lemma 4.3 excludes any additional distinguishing power from longer
words. Thus $LL$ is missing on $F$. Any decoder on a set containing
$F$ would restrict to such a decoder on $F$, so every such set is
locally inadmissible.

For the converse put $D_s=P\setminus\{u_s\}$, $0\le s\le3$.
Their exact $LL$ decoders are

| Set | Experiment | Decoder on all attained replies |
| --- | --- | --- |
| $D_0$ | $RL$ | $\mathsf{absent}\mapsto b$, $\alpha\mapsto c_*$, $\beta\mapsto d$, $\mathsf{branch}\mapsto a$ |
| $D_1$ | $RL$ | $\mathsf{absent}\mapsto a$, $\alpha\mapsto c_*$, $\beta\mapsto d$, $\mathsf{branch}\mapsto a$ |
| $D_2$ | $L$ | $\alpha\mapsto a$, $\beta\mapsto b$, $\mathsf{branch}\mapsto d$ |
| $D_3$ | $L$ | $\alpha\mapsto a$, $\beta\mapsto b$, $\mathsf{branch}\mapsto c_*$ |

For $D_0$, the four replies correspond to $u_1,u_2,u_3,u_4$.
For $D_1$, the absent and branch classes are $u_0$ and $u_4$,
both with value $a$, while alpha and beta select $u_2,u_3$.
For $D_2$, the $L$-branch class consists only of $u_3$; for
$D_3$ it consists only of $u_2$. In either case the alpha class
$\{u_0,u_4\}$ has value $a$ and the beta class $\{u_1\}$
has value $b$. Hence all these decoders are valid. The remaining
six targets have the witnesses of Lemma 4.4 on each $D_s$.
Any $A$ omitting a member $u_s$ of $F$ lies in $D_s$, so all
its required decoders restrict from this set. This includes the empty
subset vacuously and proves the equivalence. $\square$

**Theorem 5.2 (sharp weighted extremum over every joint fiber).** For
every real $0\le\theta\le1$ assign

$$
w_\theta(u_0)=w_\theta(u_1)=w_\theta(u_2)=w_\theta(u_3)=1,
\qquad w_\theta(u_4)=\theta.
\tag{CIT.24}
$$

For every integer $n\ge1$,

$$
\boxed{
\max_{\substack{B\subseteq P^n\\B\text{ jointly admissible}}}
\Omega_\theta(B)=(3+\theta)^n.
}
\tag{CIT.25}
$$

The target menu is exactly $W_3$ and the experiment menu includes
every finite word. The maximum ranges over all correlations and all
target-dependent donor choices. At $\theta=1$ this says $|B|\le4^n$.

Proof. By Theorem 5.1 any locally admissible set omits one of the
four unit-weight symbols in $F$, and therefore has weight at most
$C=3+\theta$. Each $D_s$ has exactly this weight. The only
nonempty bad subsets are $F$ and $P$. The target $LL$ is locally
missing on both. Its cells on $P$ are
$\{u_0,u_4\},\{u_1\},\{u_2\},\{u_3\}$, with weights
$1+\theta,1,1,1$; its cells on $F$ have weight one. Both sets
are range feasible, since every row of (CIT.22) has at most four
values. Thus the uniform hypotheses hold with

$$
C=3+\theta,\qquad c=1+\theta,\qquad m=4,
\qquad \sqrt m\,c=2+2\theta\le3+\theta.
\tag{CIT.26}
$$

The last inequality is equivalent to $\theta\le1$. Apply Theorem
3.1 to the finite boundary interface and use Lemma 4.3 to cover all
finite experimental words. This bounds every joint $B$ by $C^n$.
For equality use the actual product $D_0^n$. Every requested target
uses the appropriate own-coordinate decoder on $D_0$, so this product
is jointly admissible, and finite summation gives
$\Omega_\theta(D_0^n)=w_\theta(D_0)^n=C^n$.
At $\theta=0$, $u_4$ remains an actual symbol with all its
admissibility obligations; its zero analytical weight is allowed in
Theorems 2.1 and 3.1. The same equality construction gives $3^n$.
$\square$

This is an extremal fiber-mass theorem on $P^n$. It supplies a
covering dual of total $((4+\theta)/(3+\theta))^n$ there by
Corollary 3.2. It supplies no matching fractional primal cover, exact
covering number or full-$S_3$ extremum. The product used to attain
the mass bound places no restriction on the other competitors.

## 6. Native donor cycles of every length and their exact recurrence

**Theorem 6.1 (all-length cycle family).** On the full attained
$RL$ reply domain $\{\mathsf{absent},\alpha,\beta,\mathsf{branch}\}$
define

$$
\delta(\mathsf{absent})=a,\qquad
\delta(\alpha)=c_*,\qquad
\delta(\beta)=d,\qquad
\delta(\mathsf{branch})=b,
\qquad f(u)=\delta(r_u(RL)),\quad h(u)=\Gamma_{LL}(u).
\tag{CIT.27}
$$

For every integer $\ell\ge2$ put

$$
B_\ell=\{x\in P^\ell:h(x_i)=f(x_{i+1})
\text{ for all }i\in\mathbb Z/\ell\mathbb Z\}.
\tag{CIT.28}
$$

This is jointly admissible for the complete native interface. Each
of its coordinate projections equals $P$, hence is locally
inadmissible. The $LL$ witnesses have exactly the successor cycle
as their donor graph. With (CIT.24), the exact mass is

$$
\Omega_\theta(B_\ell)=\operatorname{tr}(T_\theta^\ell)
=R_\ell(\theta)+2,
\qquad
T_\theta=
\begin{pmatrix}
1&\theta&0&0\\
1&0&0&0\\
0&0&1&0\\
0&0&0&1
\end{pmatrix},
\tag{CIT.29}
$$

where

$$
R_0(\theta)=2,\qquad R_1(\theta)=1,\qquad
R_\ell(\theta)=R_{\ell-1}(\theta)+\theta R_{\ell-2}(\theta)
\quad(\ell\ge2).
\tag{CIT.30}
$$

Proof. The pairs $(h(u_s),f(u_s))$ for $s=0,1,2,3,4$ are
respectively

$$
(a,a),\quad(b,a),\quad(c_*,c_*),\quad(d,d),\quad(a,b).
\tag{CIT.31}
$$

For an $LL$ request in coordinate $i$, read $RL$ in its successor
coordinate and apply $\delta$. Equation (CIT.28) proves correctness
on the same $B_\ell$. For each of the other six targets, use the
own-coordinate witness of Lemma 4.4. Every target is therefore served
separately with zero or one experiment. These words have length at most
two, and all longer native words remain allowed by Lemma 4.3.

The constant tuples $u_0^\ell,u_2^\ell,u_3^\ell$ belong to
$B_\ell$. To realize the other two symbols at every position, put
$u_1$ at any chosen position, $u_4$ at its successor, and $u_0$
everywhere else. The equation at $u_1$ is $b=f(u_4)$, and the
equation at $u_4$ is $a=f(u_0)$ if $\ell>2$ or $a=f(u_1)$
if $\ell=2$. Every remaining position has target $a$ and successor
with $f$-value $a$. Thus the tuple belongs to the relation for every
$\ell\ge2$. Rotating it realizes $u_1$ and $u_4$ at any
coordinate. All projections consequently equal $P$, without a hidden
locally admissible donor. The selected missing target is $LL$ at
every coordinate and its donor is the successor, giving the asserted
cycle of length $\ell$.

Order states as $(a,b,c_*,d)$. A symbol $u$ contributes its weight
in row $h(u)$ and column $f(u)$ of the local transfer matrix.
The five pairs in (CIT.31) give exactly $T_\theta$ in (CIT.29).
The cycle equation identifies the column state at coordinate $i$
with the row state at its predecessor. Summing the products of local
entries over these cyclic state choices gives the trace, by the same
finite-sum identity as (CIT.9). Here it is equality for the actual
relation (CIT.28), since that relation imposes exactly these equations.

Let

$$
A_\theta=\begin{pmatrix}1&\theta\\1&0\end{pmatrix}.
\qquad
A_\theta^2=
\begin{pmatrix}1+\theta&\theta\\1&\theta\end{pmatrix}
=A_\theta+\theta I_2.
\tag{CIT.32}
$$

Define $R_j(\theta)=\operatorname{tr}(A_\theta^j)$ for
$j\ge0$. The identity matrix has trace two and $A_\theta$ has
trace one. Multiplying (CIT.32) by $A_\theta^{\ell-2}$ and
taking traces proves (CIT.30). The two scalar unit blocks in
$T_\theta$ each contribute one to every positive power, proving
(CIT.29) for every $\ell\ge2$. No enumeration or limiting
argument is needed. $\square$

**Corollary 6.2 (the credited pair and the classical Lucas sequence).**
For length two, $B_2$ is precisely the predecessor's relation

$$
B_*=
\{(u_0,u_0),(u_1,u_4),(u_4,u_1),(u_2,u_2),(u_3,u_3)\},
\quad
\Omega_\theta(B_*)=3+2\theta.
\tag{CIT.33}
$$

For length three, $\Omega_\theta(B_3)=3+3\theta$. At
$\theta=1$, the sequence $R_j(1)$ is the classical Lucas sequence
$L_0=2,L_1=1,L_j=L_{j-1}+L_{j-2}$, so
$|B_\ell|=L_\ell+2$ for every $\ell\ge2$.

Proof. In a two-cycle a state $c_*$ or $d$ can only be paired
with itself, giving $(u_2,u_2)$ and $(u_3,u_3)$. In the two-state
block, the possible two-step closed transitions are the $a$ loop
twice and the two orientations of the $a$--$b$ return, giving the
other three listed pairs. Their weights sum to $3+2\theta$.
Alternatively the recurrence gives $R_2=1+2\theta$ and
$R_3=1+3\theta$, proving both mass formulas. At $\theta=1$,
the initialization and recurrence coincide with the classical Lucas
definition, so equality follows inductively. $\square$

The values $R_0,R_1$ initialize a matrix recurrence only. No
empty-cycle or length-one fiber with full $P$ projections is
constructed. At $\theta=0$, the recurrence gives $R_j=1$ for
every $j\ge1$, so all $B_\ell$ with $\ell\ge2$ have mass
three while their projections still equal the five-symbol $P$.
Equation (CIT.29) describes this particular family, not every
admissible cycle-shaped fiber or every joint fiber.

## 7. The exact cell-only extension that fails

**Theorem 7.1 (a uniform exponential obstruction at the same cell
charge).** Fix any $\theta\in[0,1]$ and the missing-target cell
allowance $c=1+\theta$. There is no positive sequence $A_n$ with
$\log_2 A_n/n\to0$ such that every jointly admissible
$B\subseteq P^n$ with all coordinate projections locally
inadmissible satisfies

$$
\Omega_\theta(B)\le A_n c^n.
\tag{CIT.34}
$$

More precisely, for every integer $N\ge1$, the actual relation
$B_*^N\subseteq P^{2N}$ forces

$$
A_{2N}\ge
\left(\frac{3+2\theta}{(1+\theta)^2}\right)^N,
\qquad
\frac{3+2\theta}{(1+\theta)^2}\ge\frac54.
\tag{CIT.35}
$$

Proof. Pair the $2N$ coordinates and put the five-element relation
$B_*$ in each pair. All targets use the pair's witnesses from §6
and Lemma 4.4, which remain valid with arbitrary values in the other
pairs. This gives a jointly admissible relation with all projections
equal to $P$. Distributivity over this specifically constructed
product gives $\Omega_\theta(B_*^N)=(3+2\theta)^N$.
Inserting it into (CIT.34) yields the first inequality in (CIT.35).
For the uniform gap, the exact polynomial identity

$$
4(3+2\theta)-5(1+\theta)^2
=(1-\theta)(5\theta+7)\ge0
\tag{CIT.36}
$$

holds on $[0,1]$, and the denominator in (CIT.35) is positive.
Consequently

$$
\frac{\log_2 A_{2N}}{2N}
\ge\frac12\log_2\frac{3+2\theta}{(1+\theta)^2}
\ge\frac12\log_2\frac54>0.
\tag{CIT.37}
$$

This contradicts the stipulated limit, even if a different correction
sequence is allowed for each fixed $\theta$. Equality in the uniform
ratio bound occurs at $\theta=1$. At $\theta=0$ the pair still
has mass three while its cell allowance is one. $\square$

The failed extension drops the deficient-donor-capacity hypothesis of
NCM while retaining only the smaller cell charge and trying to hide
every cyclic contribution in a subexponential factor. The theorem
does not refute a bound with a larger per-coordinate allowance, an
additional simultaneous-target constraint, different weights or sharper
cycle traces. Indeed Theorem 5.2 proves a valid bound with allowance
$3+\theta$ on the same alphabet. The obstruction uses a positive
density of short cycles; it says nothing equivalent about the loss per
coordinate of one isolated long cycle. The full traces in (CIT.7)
remain available. Nor is (CIT.34) the full-family memory converse.

## 8. Conditional native correspondence and paid exact attainment

**Assumption 8.1 (stationary source, complete export and lawful entry).**
For public $D\ge1$ use the unchanged source and request families

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
\mathcal P_D=\{Rq:|q|\le D-1\}.
\tag{CIT.38}
$$

One actual initial tree remains stationary throughout preparation and
the later Read. Its formal iterates under $\rho$ are prediction
targets, not source evolution. A common deterministic effective
preparation starts source-blind with public $D$ and installed common
tables, terminates on every source, and acquires all source distinctions
through charged original-root literal Reads. It receives neither a
later request nor a later count. Before those are supplied it exports
a finite complete name $E(t)$. Every accessible surviving
source-dependent distinction is included in that name: control,
selectors, buffers, operands, lengths, allocation, handles, counters
and accessible timing distinctions. Every other accessible field is a
fixed function of this name and public data. A separately paid handoff
and isolation service makes all earlier transcripts and other acquired
descriptions inaccessible and supplies lawful reader entry.

After export, a public source-independent request $p\in\mathcal P_D$
is supplied. One common deterministic effective reader receives
$E(t),D,p$ and public installed tables, chooses zero Reads or one
finite original-root literal, and obtains at most one actual reply
from the same stationary tree. It then exports a predictor $Z$.
For every subsequently supplied authentic $k\ge0$, with no further
Reads, correctness requires

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p).
\tag{CIT.39}
$$

The authentic count is not available before the Read. Neither a
source-dependent request nor inaccessible preparation information is
a reader input. There is no native subtree, equality, source-identity,
age, reset, copying, navigation or free-advice port. Local computation
on actually acquired finite descriptions is distinguished from such
ports. Handoff, complete isolation, authentication, source continuity
and entry are service premises, not physical operations established
by the following mathematics.

We retain the exact factor/trajectory interface (CIT.19)--(CIT.20)
and the supplied actual-occurrence transport: at a present original
subtree occurrence $u$ at address $a$, every subsequent predicted
reply at $aq$ is the predicted reply of that subtree at $q$.
For the wrapper, $\Gamma_{Rq}(\langle\alpha,v\rangle)
=\Gamma_q(v)$. These are the conditional interfaces of NCM,
attributed there to AAR and its native transport suppliers. No
recertification of their underlying interfaces is part of this volume.

**Proposition 8.2 (every original competitor restricts to an admissible
joint fiber).** Let $D\ge3$, $h=D-3$ and $n=2^h$. In the right
subtree of the actual wrapper, place a perfect ordered scaffold of
height $h$, with frontier words $a_1,\ldots,a_n$ of length $h$,
and substitute $x_i\in P$ at each frontier. Let $t_x$ denote the
resulting source. For any preparation and reader correct under
Assumption 8.1 and any attained code $e$, the nonempty restricted
fiber

$$
B_e=\{x\in P^n:E(t_x)=e\}
\tag{CIT.40}
$$

is jointly admissible for all seven targets and every finite native
experiment. Hence $\Omega_\theta(B_e)\le(3+\theta)^n$ for
every $\theta\in[0,1]$.

Proof. All frontier occurrences are present in the same original
tree, the construction is injective in $x$, and the right subtree
has height at most $h+3=D$. Thus every $t_x$ lies in the original
$\mathcal F_D$. For every $i$ and $q\in W_3$, the actual request
$p=Ra_iq$ has length at most $1+h+2=D$, so is in
$\mathcal P_D$. Transport at the present block root identifies its
factor with $\Gamma_q(x_i)$. The suffix endpoint need not itself
be present initially: the factor interface already describes its
entire future trajectory, including stages after an initial absence.

Fix $e,i,q$. Completeness of the retained name and determinism of
the reader fix its zero-Read decision or its one literal before any
reply or count. Account for every possible finite original-root
experimental word as follows. The empty word reads the wrapper branch.
A word beginning with $L$ reads the fixed wrapper leaf or passes
beyond it. A word beginning with $R$ and stopping strictly before
the frontier reads a scaffold branch. All these replies are constant
on the slice. Every other word in the right cone has a unique frontier
prefix $Ra_j$ and a finite suffix $a$ in that actual block. There
is no restriction that $j=i$ and no restriction on $|a|$.

For $|a|\le2$ it is a boundary experiment of Lemma 4.3. For
$|a|=3$ it is the stated public function of its length-two parent
reply. For $|a|\ge4$ it is absent. This classification includes
words going beyond earlier leaves. If the reader uses no Read or
a constant experiment, (CIT.39) gives the same trajectory for every
tuple of $B_e$, and the exact temporal interface makes the target
factor constant there. Otherwise two tuples with the same selected
boundary reply have the same actual reply, even when the latter is
a coarsening. The common reader therefore produces the same $Z$
and the same trajectory for every later authentic $k$. Equality of
trajectories gives equality of $\Gamma_q(x_i)$.

This is exactly (CIT.2) on the original $B_e$, separately for each
$i,q$. The boundary reply is used to establish the implication;
no operational conditioning, source replacement or new information
is supplied to the reader. Theorem 5.2 now applies. $\square$

**Theorem 8.3 (paid attainment on the entire variable-shape family).**
Let $h\ge1$, $n=2^h$ and $D=h+3$. In the scaffold of Proposition
8.2 choose any public pairing of the frontier positions. The set
of actual sources with block tuple in $B_*^{n/2}$ can be exactly
one attained complete-code fiber of a preparation and one common
reader on all of $\mathcal F_D$, under Assumption 8.1. Every
other source can have a singleton code. A sufficient preparation uses

$$
2^{D+1}-1\text{ Reads},\qquad
D+1\text{ maximum literal length},\qquad
D\,2^{D+1}+1\text{ submitted letters}.
\tag{CIT.41}
$$

The common-name reader needs at most one actual Read of length at
most $D$, before the authentic count, and works for every allowed
request and every later authentic $k\ge0$. Singleton names need
zero later Reads.

Proof. Use one source-blind preparation on every source in
$\mathcal F_D$. It actually submits every literal $Rw$ with
$|w|\le D$, including words with absent replies. Since the right
subtree has height at most $D$, these replies determine every node
and every terminal alpha/beta label. Starting at its root, a branch
reply requires inspecting its two children, while a terminal reply
specifies the corresponding leaf. No branch can remain at depth
$D$. Thus the finite array determines the entire right subtree and
hence the actual source. This is a paid acquisition of a finite
description, not an identification oracle.

There are $\sum_{j=0}^D2^j=2^{D+1}-1$ submitted words, with
maximum length $D+1$. Their total length is
$\sum_{j=0}^D(j+1)2^j=D2^{D+1}+1$. The latter identity follows
by induction: its value for $D=0$ is one, and its increment from
$D-1$ to $D$ is $(D+1)2^D$. These formulas prove (CIT.41).

Using only this acquired description and public finite tables, compute
membership in the selected set of scaffold sources. Give all sources
in that set one common name, and each other acquired source a distinct
name in a fixed public order. The selected set is nonempty. If its
cardinality is $s$ and $f_D=|\mathcal F_D|$, there are
$L=f_D-s+1$ attained names. Encode them in a common public width
$\lceil\log_2 L\rceil$, with any unused bit strings unattained.
Every assigned name is attained by its designated sources. Export
exactly this complete name and invoke the separately paid service to
isolate every other acquired distinction, including residual buffers,
selectors, control, handles and timing. The name's fixed width and
the complete-export condition prevent additional accessible distinctions
from serving as a data channel. The installed public tables depend
on $D$ and the selected relation, not on the actual unknown source.
Their size and the local preparation computation are not asserted small.

On the common name, every permitted request has the form $p=Rb$
with $|b|\le D-1=h+2$. If $|b|<h$, it stops at a fixed
scaffold branch and has constant factor $(0,0)$. Otherwise it has
a unique representation $p=Ra_iq$ with $q\in W_3$. For $LL$
at a block, use $RL$ in its paired block with decoder $\delta$.
For the other targets use Lemma 4.4. A selected block experiment
$a$ at donor $j$ is submitted as the full actual original-root
literal $Ra_ja$, never as an operation on a copied subtree.
Its length is at most $1+h+2=D$. Constant targets use zero Reads.
The decoded factor and (CIT.20), transported from that actual block
occurrence, give the correct reply for every subsequently supplied
$k\ge0$. This includes requests whose block suffix initially goes
beyond a leaf.

On a singleton name, a fixed public finite table identifies the
source that the preparation actually acquired and supplies the
factor for each permitted target. Formula (CIT.20) then gives a
predictor with zero further Reads. This completes one common
deterministic reader for every variable-shape source, with all allowed
requests, rather than merely a reader on the selected scaffold slice.
No source evolution, reset or copy is used. All source-bearing data
have come from the charged literals, and every hidden preparation
description is covered by the paid isolation premise. $\square$

**Corollary 8.4 (credited counts and a native subsequence of the
obstruction).** In Theorem 8.3 the selected set has cardinality
$s=5^{n/2}$. The total source count and attained alphabet size are

$$
f_0=2,\qquad f_{j+1}=2+f_j^2,\qquad
L=f_D-5^{n/2}+1.
\tag{CIT.42}
$$

At $D=4$, these are exactly the NCM Proposition 6.2 construction
and its supplied counts: $31$ preparation Reads, maximum length
$5$, $129$ submitted letters, $f_4=2{,}090{,}918$ sources and
$2{,}090{,}914$ attained names, with late Read length at most $4$.
The cell-only obstruction of §7 is therefore realized by exact
attained fibers at every $n=2^h$, $h\ge1$, under the stated
services.

Proof. The five pairs of (CIT.33) can be chosen independently in
the selected relation, and the scaffold map is injective, giving
$5^{n/2}$. A height-at-most-zero right subtree is one of two
leaves; a height-at-most-$(j+1)$ right subtree is a leaf or an
ordered pair of height-at-most-$j$ subtrees. These disjoint cases
give the recurrence for $f_j$, and merging $s$ names into one
gives the formula for $L$. The predecessor's values are
$f_1=6,f_2=38,f_3=1446,f_4=2{,}090{,}918$; at $D=4$ one
merges the same five sources as NCM. In particular its $LL$
requests $RLLL$ and $RRLL$ read respectively $RRRL$ and $RLRL$.
These exact numerical counts retain their NCM credit.

For the realized fibers, $N=n/2=2^{h-1}$ in Theorem 7.1. Their
weight is $(3+2\theta)^{n/2}$ and their ratio to the same cell
charge $c^n$ is $((3+2\theta)/(1+\theta)^2)^{n/2}$.
The normalized logarithmic gap in (CIT.37) persists along this
unbounded native subsequence. A subexponential correction on all
block sizes would have a vanishing normalized logarithm on this
subsequence too, which is impossible. This does not optimize the
large supporting code or contradict a full-family memory lower bound.
$\square$

**Proposition 8.5 (paid arbitrary-length cycles with public padding).**
For every $\ell\ge2$ choose $h$ with $2^h\ge\ell$, put
$D=h+3$, select $\ell$ public frontier positions in the perfect
scaffold, and place $B_\ell$ in these positions in any fixed cyclic
order. Fill every other position with the fixed tree $u_0$. This
relation of actual sources can also be one exact attained fiber on
all of $\mathcal F_D$ under Assumption 8.1, with the acquisition
bounds (CIT.41) and late Read length at most $D$.

Proof. The variable positions use the successor $RL$ decoder for
$LL$ and the local decoders for the remaining targets. They may
query any other selected frontier position; adjacency in the scaffold
is not required. Every target in a padding block has a publicly
known factor, so uses no Read. Every target above the frontier is
again a constant branch factor. These cases exhaust the permitted
request lengths as in Theorem 8.3. A query in a padding block is
source-independent on this fiber, so padding provides no hidden data
port. It also contributes analytical weight one because
$w_\theta(u_0)=1$.

Acquire the whole source with the same paid literal array, assign
one common fixed-width name to precisely this finite selected relation,
and give all other sources singleton names. Export completely and
apply the same paid isolation and lawful-entry services. The one
common reader uses the displayed witnesses at the full literals
$Ra_ja$ or zero Reads; singleton completion is unchanged. The
actual block transport and temporal decoder prove correctness for
every authentic subsequent count. Thus every cycle length is attained
without asserting a length-one construction or a free operational
subtree interface. $\square$

Preparation work, temporary descriptions, membership computation,
installed table generation and storage, literal lengths, submitted
letters, predictor size, authentic-count representation, handoff,
isolation and physical time remain separate resources. Equations
(CIT.41)--(CIT.42) are sufficient counts for this particular
full-family completion, without a claim of optimal acquisition or
optimal retained alphabet.

## 9. Credit, exact proof scope and unresolved boundaries

**Convention 9.1 (separate predecessor contributions).** The following
attributions distinguish the input theory from the deductions of this
volume.

| Predecessor or classical method | Retained contribution and boundary |
| --- | --- |
| NCM §2 | The deficient-reply-capacity theorem forces a missing target's donor to a good projection. The component trace theorem permits the closed components that its hypothesis excludes. |
| NCM §§3--5 and FMR Theorem 5.1 | The full depth-two $25/17$ local seed, its all-correlated mass theorem, exact regularized fractional value, block error and predecessor rate lower are credited results. The lower remains valid as predecessor context; NCE's stronger rate lower is recalled in §9.3. None is a new conclusion of the sharp $P$ theorem. |
| NCE, Theorems 2.2, 6.1 and 6.2 | The heavy-target squared-cell entropy certificate handles arbitrary cyclic donors under one joint law. Its exact full-$S_3$ weights, all-joint fractional lower and stronger native full-family lower are separate credited results, recalled in §9.3. |
| NCM §6, Propositions 6.1--6.2 | The literal $P$, the five-element $B_*$, its mutual assistance and the paid $D=4$ construction with exact counts are predecessor results. Merely repeating that pair is not a new component theorem. |
| AAR, as supplied through NCM §1 and §7 | The exact temporal factors, their trajectory decoder and known-menu acquisition results retain their original scope. The operational proofs here assume the stated temporal and actual-occurrence interfaces. |
| FMR, as supplied through NCM | Canonical simulation, native covering correspondence, finite harmonic rounding, rate existence and the strict upper rate bound retain predecessor credit. Abstract covering inequalities alone do not construct native preparation. |
| NBP, as supplied through NCM | Paid stationary handoff and authenticated-entry service disciplines remain assumptions at their specified task scope; they construct no physical isolation or authentication here. |
| Classical finite mathematics | Functional components, nonnegative finite product sums, transfer-matrix traces, Fibonacci--Lucas recurrence and covering duality/rounding are used as established methods. Their application is not a claim of inventing these methods. |

**Convention 9.2 (scope of the present proofs).** Theorems 2.1 and
3.1 cover every finite interface of §1, every $n\ge1$, every
nonnegative analytical weight, and every joint fiber under the stated
local bounds; the graph is chosen from actual missing-target witnesses.
The proof includes rectangular dimensions, arbitrary donor choices,
empty fibers, zero weights, $m=2$ and $n=1$. Corollary 3.2 states
the correct nonnegative dual direction, ceiling lower bound and
classical finite rounding upper bound.

Theorems 5.1--5.2 cover exactly the proper alphabet $P$, the seven
$W_3$ targets, every finite native experiment, all joint correlations,
all $n\ge1$ and $0\le\theta\le1$. Theorem 6.1 constructs every
cycle length $\ell\ge2$, with full bad projections and an exact
trace/recurrence for that family. Theorem 7.1 refutes only (CIT.34)
at the same charge $1+\theta$, uniformly by a ratio at least $5/4$.
The operational restriction and attainments in §8 depend on every
condition of Assumption 8.1 and the credited temporal/occurrence
interfaces. They do not discharge those service conditions.

The component certificate with rectangular traces, sharp proper-$P$
extremum and exact all-length recurrence for the particular $B_\ell$
family are additional conclusions relative to the supplied NCM text.
NCE Theorem 2.2 already handles arbitrary donor cycles through its
entropy certificate; it does not supply these exact rectangular-trace,
proper-$P$ extremum or particular Lucas-recurrence statements. The
classical recurrence, original pair, predecessor depth-two lower and
NCE full-$S_3$ lower retain their separate credit. This comparison
supplies no worldwide priority claim or claim of originality against
unsearched literature.

**Open problem 9.3 (credited full-$S_3$ lower and unresolved sharpness).**
The sharp $P^n$ mass theorem remains a proper-subalphabet result. It
supplies neither an all-$S_3$ extremum nor a full depth-three fractional
optimum, and no full-$S_3$ rate advance follows from $P$ alone.
The depth-two predecessor bounds

$$
M_1(D)\ge
\left\lceil\left(\frac{25}{17}\right)^{2^{D-2}}\right\rceil
\quad(D\ge2),\qquad
\frac14\log_2\frac{25}{17}\le\lambda<0.216605159
\tag{CIT.43}
$$

retain their NCM and FMR attribution and remain valid weaker lower
bounds. Here $M_1(D)$ is the minimum complete attained alphabet in
Assumption 8.1 and
$\lambda=\lim_{D\to\infty}2^{-D}\log_2 M_1(D)$ is the supplied
existing rate. The strict upper remains credited to FMR.

NCE Theorem 2.2 supplies a separate entropy certificate: every heavy
range-feasible projection of weight greater than $C$ must have an
own-coordinate missing target whose cell weights $A_z$ satisfy
$\sum_z A_z^2\le C^2$. For the positive weights below and a nonempty
fiber, each selected target is a deterministic function of both its own
coordinate and its donor coordinate under the same joint law
$\Pr[X=x]=\prod_iw(x_i)/\Omega_w(B)$ on the same unchanged joint
fiber $B$. No independence, locally admissible donor or acyclic donor
graph is required. This is
a credited sufficient mass certificate, without a completeness claim
or an identification with the trace criterion of Theorem 3.1.

The exact full-$S_3$ weights used by NCE Theorem 6.1 are, with the
canonical alphabets of (CIT.16),

$$
\begin{aligned}
v(\alpha)&=v(\beta)=4,&
v(\langle x,y\rangle)&=1\quad(x,y\in S_1),\\
w(\alpha)&=88,&w(\beta)&=52,\\
w(\langle x,y\rangle)&=v(x)v(y)\quad(x,y\in S_2),&
C&=169,\qquad w(S_3)=429.
\end{aligned}
\tag{CIT.43a}
$$

NCE Theorems 6.1 and 6.2 give the credited current lower. Together
with the unchanged FMR upper recalled by NCE Corollary 6.3, the
bounds are:

$$
\begin{aligned}
Z_3(n)&\ge\left(\frac{33}{13}\right)^n
&& (n\ge1),\\
M_1(D)&\ge
\left\lceil\left(\frac{33}{13}\right)^{2^{D-3}}\right\rceil
&& (D\ge3),\\
\frac18\log_2\frac{33}{13}&\le\lambda<0.216605159.
\end{aligned}
\tag{CIT.43b}
$$

Here $Z_3(n)$ is the fractional covering optimum over every jointly
admissible subset of the complete $S_3^n$, with all seven targets
and every finite native experimental word retained. NCE Corollary
6.3 establishes the strict improvement over the depth-two rate lower.
These are recalled NCE conclusions, not stronger lower bounds proved
by this volume's component, proper-$P$ or Lucas results.

The native conclusion retains every condition of Assumption 8.1 and
the credited exact temporal and actual-occurrence interfaces: one
stationary source, source-blind paid preparation, complete export,
separately paid handoff and isolation, lawful entry and source
continuity, source-independent late requests, and one common reader
using zero or one charged original-root Read before the subsequently
supplied authentic count. All allowed sources, targets, off-target
queries and correlated fibers remain in scope. The services and the
separate resource charges are not discharged by the entropy lower.

The exact original $\lambda$, effective lower endpoints converging
to it with certified gaps, and a uniform all-depth lower hierarchy
remain unresolved here and in the supplied NCE conclusions. A single
all-length depth-three certificate does not supply that hierarchy,
and a depth-specific normalized rounding error does not supply a
uniform all-depth error. The exact finite values of $M_1(D)$ in
general, including the credited unresolved $M_1(3)\in\{3,4\}$,
are not determined by these results. Exact $Z_3(n)$ and $\sigma_3$
remain unresolved as well. Neither an attained mass cap, an exact
fractional value nor a cycle partition sum alone determines a finite
integral memory optimum. Failure of either sufficient certificate
would not prove that a stronger full-family lower is impossible.

**Convention 9.4 (limits of interpretation).** The proved recovery
relation, conditionally interpreted in the native task, is

$$
(E(t),D,p,\text{zero or one actual reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{CIT.44}
$$

It does not recover the full unknown source, an unknown age,
provenance, hidden history, physical storage, or physical space and
time. There is no neural, machine-learning, training, generalization,
pure critical-renewal or physical-transfer theorem here, and no
completion of the broader minimal-relations/internal-observer
programme. The statements are ordinary mathematical proofs with
explicit conditional interfaces, without Lean/kernel certification.

## 追加锚（本行以下为增补区）

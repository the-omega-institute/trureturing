# Signed local-prefix lifting and scalar-support closure

## 1. Scope and exact normalized pieces

This volume proves a local bridge between finite signed feasibility and
prefix witnesses on exact Cartesian pieces. It uses the native trees

$$
\mathcal T ::= \alpha\mid\beta\mid\langle s,t\rangle,
\qquad
\rho\alpha=\beta,
\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle s,t\rangle=\langle\rho s,\rho t\rangle .
$$

The unary symbol is interpreted by these equations. It is not a free
constructor. A completion tree may be finite or infinite; its finite prefix
of depth $h$ is the four-valued reply table on words of length at most $h$.
An infinite coordinate means a completion tree with an infinite branch. A
finite tree is isolated by the replies through one more level than its height.

In this volume a normalized Cartesian piece has the form

$$
C(\mathbf n,\mathbf z)
 := P(\mathbf n)\ \land\
\bigwedge_{j=1}^{s} A_j(\mathbf n,\mathbf z)\ne B_j(\mathbf n,\mathbf z),
\tag{SLP.1}
$$

where $P$ is Presburger, and every $A_j,B_j$ is a finite mixed native
template built from fixed finite trees, $T_{n_i+c}=\rho^{n_i+c}\alpha$,
decorated residuals $\rho^a z_r$, and ordered pairing. Repeated residual
names are shared. The conjunction is empty when $s=0$. For an acquired-source
application, both directions of its owning image correspondence must prove
that all endpoint guards, positive links, complete-row tests, navigation
cases and the whole old exterior and partition are retained by this formula
and its source map. The residual product before the negatives must be the
full Cartesian product $\mathcal T^m$. These are input hypotheses;
[NIC, Theorem 4.3][NIC] does not assert that every arbitrary signed image
piece eliminates all residual restrictions into this form.

For a finite set $F\subseteq\{1,\ldots,m\}$ and a finite tuple
$f\in\mathcal T^F$, write

$$
S_f=\{\mathbf n\in\mathbb N^k:
 P(\mathbf n)\land
 \exists \mathbf z_{\bar F}\in\mathcal T^{\bar F}
 \;\bigwedge_j A_j(\mathbf n,f,\mathbf z_{\bar F})\ne
 B_j(\mathbf n,f,\mathbf z_{\bar F})\}.
\tag{SLP.2}
$$

$S_f$ is the entire feasible scalar support after the finite residual
coordinates have been fixed. It is not a selected representative support.
NSF supplies a decision and a finite witness for membership in (SLP.2) when
the supplied finite $f$ is present; no decision for unknown $f$ is assumed.

## 2. Prefix restriction reflects native identities

The next lemma is the local statement absent from NSF and URR. It is a
finite construction for one fixed scalar tuple, not a solver for arbitrary
pieces.

**Lemma 2.1 (prefix-preserving simultaneous disequality).** Fix $\mathbf n$
and finite $f$. Let $I=\bar F$. Assume the residual conjunction in (SLP.2)
has one finite witness. Let $(\eta_i)_{i\in I}$ be any tuple of infinite
completion trees. For every prescribed finite prefix of every $\eta_i$ there
is a tuple of finite trees $(z_i)_{i\in I}$ with those prefixes such that

$$
\bigwedge_j A_j(\mathbf n,f,\mathbf z)\ne B_j(\mathbf n,f,\mathbf z).
\tag{SLP.3}
$$

If $I=\varnothing$, the assertion means that the already fixed tuple $f$
itself is the witness. If $s=0$, any finite extensions of the prescribed
prefixes are witnesses.

**Proof.** Fix $\mathbf n,f$ throughout. Their atoms and decorated finite
coordinates are now finite grounds. The remaining syntax is exactly a
finite ground, a decorated original residual $\rho^a z_i$, or a native pair.

Represent the prescribed inclusive prefix of $\eta_i$ by a finite native
context $C_i(w_{i,1},\ldots,w_{i,q_i})$. Retain every observed branch and
leaf. At a branch at the last observed depth, replace each unobserved child
by a separate hole. Earlier leaves retain their entire absent descendant
region. This construction also applies after refining any finite set of
prescribed replies to one depth. Because $\eta_i$ has an infinite branch,
$q_i\ge1$. Each hole occurs once in $C_i$. Holes of different original
names are independent. Every finite filling of these holes has precisely
the prescribed prefix, and every finite tree with that prefix is such a
filling. Repeated occurrences of $z_i$ always use this same context and
the same hole tuple; they do not receive independent copies.

Use the native mass and clock from [URR, Definition 2.1][URR]. In particular
$\gamma(\rho^a t)=\gamma(t)$, and a native pair having a positive-mass
child has mass $1+\gamma(u)+\gamma(v)$. The exceptional atomic-code
collapse occurs only when both children have mass zero. The finite comb
called $C_r$ in [URR, Definition 2.2][URR] realizes every integer mass $r\ge1$.
For the following identity argument fill each hole with an arbitrary
positive-mass tree, of mass $M_{i,r}$.

There is a fixed nonnegative integer $c_i$ such that

$$
\gamma(C_i(\mathbf w_i))
 =c_i+\sum_{r=1}^{q_i}M_{i,r}.
\tag{SLP.9}
$$

Here $c_i$ counts each pair having a hole descendant as one, plus the
actual native masses of the maximal hole-free subtrees. Induction on the
context proves (SLP.9): a hole has positive mass; any ancestor of a hole
has a positive-mass child, so uses the additive pair formula; every
hole-free subtree has its fixed actual mass. Thus finite constructor
contributions and unequal frontier multiplicities are retained exactly.
Decoration of the entire context does not change this mass.

For a residual template $E$, let $o_i(E)$ count its occurrences of the
original name $z_i$, including repetitions and ignoring decorations.
Define $b(E)$ recursively. If $E$ is residual-free, put $b(E)=\gamma(E)$
after evaluating its fixed grounds. Put $b(\rho^a z_i)=0$. At a pair
containing a residual put $b(\langle E_1,E_2\rangle)=1+b(E_1)+b(E_2)$.
The same positive-child induction gives the exact formula

$$
\gamma(E(\mathbf C(\mathbf w)))
 =b(E)+\sum_{i\in I}o_i(E)
       \left(c_i+\sum_{r=1}^{q_i}M_{i,r}\right).
\tag{SLP.10}
$$

In particular $b(E)\ge1$ when the root is a pair containing a residual.
No common mass or variable clock for the filled original residuals is
assumed. The quantities $M_{i,r}$ vary independently over all positive
integers, by filling with the finite combs just cited.

We now prove the needed reflection, for any two templates $A,B$:

$$
\begin{aligned}
&\forall\mathbf w\in\prod_{i\in I}\mathcal T^{q_i},\quad
 A(\mathbf n,f,\mathbf C(\mathbf w))
   =B(\mathbf n,f,\mathbf C(\mathbf w))\\
&\hspace{12mm}\Longrightarrow
 \forall\mathbf z\in\mathcal T^I,\quad
 A(\mathbf n,f,\mathbf z)=B(\mathbf n,f,\mathbf z).
\end{aligned}
\tag{SLP.11}
$$

Induct on the sum of the two syntax sizes. If both sides are residual-free,
their equality is independent of the residuals. If exactly one is
residual-free, (SLP.10) contradicts universal equality: the coefficient of
a hole belonging to an occurring original name is positive on one side
and zero on the other. To see coefficient equality without an asymptotic
argument, set all masses to one, then increase that single hole mass by
one and subtract the two equalities.

Suppose both sides contain residuals. If their roots are decorated
original variables with different names, that same coefficient comparison
contradicts equality, since each name has at least one independent hole.
For the same name, equality at any finite filling and
$\kappa(\rho^a t)=\kappa(t)+a$ force the two decorations to agree. The
original templates then agree under every assignment. This use of the
clock does not require that a prefix allow variation of $\kappa(t)$.

Consider a decorated original variable $\rho^a z_i$ against a compound
$E$ whose root is a pair. If $E$ is residual-free, the preceding case
applies. Otherwise equality for every positive-mass filling forces
$o_i(E)=1$ and $o_j(E)=0$ for all $j\ne i$, by comparing a hole
coefficient for each name. Substituting these counts in (SLP.10), equality
of masses requires

$$
c_i+\sum_r M_{i,r}
 =b(E)+c_i+\sum_r M_{i,r},
$$

which contradicts $b(E)\ge1$. This includes compounds containing a
shared occurrence of that same residual and any fixed prefix contributions.
The reversed compound/variable case is identical. Finally, if both roots
are pairs, injectivity of actual native pairing makes their corresponding
children equal for every hole filling. Induction applies to each child
comparison and reconstructs the global equality. These cases exhaust the
declared syntax and prove (SLP.11). A global identity also plainly holds
on the cylinder. Native code nodes have only supplied the mass invariant;
they have not been treated as free native constructors.

It remains to produce one tuple for all negatives, rather than separate
witnesses. Substitute the contexts $C_i$ into the entire finite list.
Distribute every fixed power of $\rho$ through their finite pairs and
evaluate it on their finite grounds. The resulting list is in URR's mixed
grammar on the independent hole variables, with no scalar variables.
The assumed original conjunction witness implies that no original listed
equality is a global identity. By (SLP.11), none of its substituted
equalities is an identity on the hole product either. Apply [URR,
Theorem 3.1 and Corollary 3.2][URR] to this entire substituted list. Its
single explicitly constructed finite tuple of hole values therefore
breaks every equality together. Fill each $C_i$ with that tuple. The
result is one actual finite original residual tuple satisfying (SLP.3),
with all prescribed replies and all shared repetitions retained. This is
a terminating construction from the fixed input, grounds and prefixes.
For $I=\varnothing$ use the assumed fixed witness, and for $s=0$ fill
arbitrarily. $\square$

The lemma also records the barrier condition. A finite residual coordinate
cannot be perturbed past a leaf; it is therefore fixed in $f$ and its
feasibility is tested by $S_f$. An infinite coordinate has a live frontier,
so no such finite barrier exists. No retained signed predicate or finite
partition is inferred for an infinite limit tree.

## 3. The exact closure criterion

Compactify each scalar coordinate by
$\overline{\mathbb N}=\mathbb N\cup\{\infty\}$. Finite points are isolated,
and a neighborhood of $\infty$ contains all integers above a prescribed
bound. Give completion trees the finite-prefix topology. For
$\lambda\in\overline{\mathbb N}^{\,k}$ and a completion tuple
$\eta\in\widehat{\mathcal T}^{\,m}$, let

$$
F=\{i:\eta_i\text{ is finite}\},\qquad f=\eta_F.
$$

Write $\overline C$ for the set of pairs $(\lambda,\eta)$ each of whose
finite scalar/prefix neighborhoods contains a finite member
$(\mathbf n,\mathbf z)$ satisfying (SLP.1). This is a closure definition;
it does not extend the signed predicates to a limit.

**Theorem 3.1 (signed local-prefix lifting and support closure).** For every
normalized piece (SLP.1),

$$
(\lambda,\eta)\in\overline C
\quad\Longleftrightarrow\quad
\lambda\in\overline{S_f},
\tag{SLP.4}
$$

where $f$ consists exactly of the finite residual coordinates of $\eta$.
The closure on the right is in $\overline{\mathbb N}^{\,k}$. When these
equivalent conditions hold, for every vector of lower bounds on coordinates with
$\lambda_i=\infty$, one scalar tuple in $S_f$ satisfies all those bounds
simultaneously; finite coordinates of $\lambda$ are equalities, not limits.

**Proof.** For the forward implication, take a finite witness in every
neighborhood of $(\lambda,\eta)$. A neighborhood that isolates each finite
$\eta_i$ forces $z_i=f_i$ for $i\in F$. The scalar projection of that witness
therefore lies in $S_f$. Shrinking scalar neighborhoods gives
$\lambda\in\overline{S_f}$, with one witness tuple for all simultaneous
lower bounds.

For the reverse implication, take any finite scalar neighborhood of $\lambda$
and any finite prefix of every infinite $\eta_i$. By
$\lambda\in\overline{S_f}$, choose one $\mathbf n\in S_f$ in that scalar
neighborhood. The definition of $S_f$ supplies some finite completion of the
remaining residuals, so the hypothesis of Lemma 2.1 holds at this same
$\mathbf n$ and $f$. Apply that lemma to the prescribed prefixes. The result
keeps the finite coordinates exactly $f$, satisfying their requested
prefixes too. It is a finite member of $C$ in the chosen product
neighborhood. Since the neighborhood was arbitrary,
$(\lambda,\eta)\in\overline C$. $\square$

**Corollary 3.2 (feasible finite-neighborhood reconstruction).** Supply
the finite tuple $f$, a basic scalar neighborhood $U$ of $\lambda$, and
for each remaining coordinate a valid finite prefix of an infinite
completion $\eta_i$. Prefix holes of distinct names must be independent,
and repetitions of one name must use the same prefix and filling. Assume
the exact feasibility antecedent

$$
U\cap S_f\ne\varnothing.
\tag{SLP.12}
$$

Here $U$ is specified by finite-coordinate equalities and finitely many
simultaneous lower bounds at divergent coordinates. One can reconstruct a
finite member of (SLP.1) in that scalar/prefix neighborhood as follows.

1. After inserting the supplied finite $f$, use [URR, Corollary 3.2][URR]
   to compute the Presburger support $S_f$, conjoined with $P$. Use
   Presburger witness extraction for $U\cap S_f$ to choose one
   $\mathbf n$ satisfying every bound at once.
2. At this same $\mathbf n,f$, finite NSF feasibility supplies a finite
   residual seed satisfying the full negative conjunction.
3. Apply Lemma 2.1's context substitution and the single URR hole tuple
   to reconstruct a finite tuple with every prescribed prefix.

Each step terminates under (SLP.12). The reconstructed tuple satisfies the
complete normalized piece and every retained native negative. For all
neighborhoods $U$ of one proposed $\lambda$, the sufficient and necessary
antecedent is $\lambda\in\overline{S_f}$ by Theorem 3.1. A separately
supplied finite residual prefix that isolates a finite tree must instead
be added to $f$ and the support recomputed with that coordinate fixed.
Inconsistent prescribed replies or extra coupling of frontier variables
are outside the prefix hypotheses. No sign or partition is inferred at
$(\lambda,\eta)$, and no unknown $f$ is decided by this statement.
Conversely any finite witness in the requested neighborhood projects to
$U\cap S_f$, so (SLP.12) is necessary as well as sufficient under these
valid independent infinite-prefix hypotheses.

The statement includes the degenerate cases. With $k=0$, the scalar closure
is the singleton truth value of $S_f\ne\varnothing$. With no remaining
residuals, $f$ itself is the only possible completion and (SLP.4) is exactly
the finite feasibility test. With no negatives, the support is the
Presburger set $P$ and arbitrary finite prefix extensions supply witnesses.
In particular, when $k=m=0$, $P=\mathsf{true}$ and the only negative is
$\alpha\ne\alpha$, $S_f=\varnothing$. The scalar space still contains its
one empty tuple, but (SLP.12) fails even for the whole scalar space; no
witness is reconstructed. The empty negative conjunction, in contrast,
does admit that empty tuple.

## 4. What this closes, and what it does not

The theorem is an exact parameter-closure criterion, not a finite
description of all closures. It says that a proposed limit fails precisely
when either a finite residual coordinate is a barrier with no feasible
completion, or the scalar point is outside the closure of the whole support
after that barrier is fixed. It does not turn the support of unknown $f$ into
a solver, and it does not replace the general NIC stopping alternative by
enumeration of supplied depths.

For each fixed depth, NSF's complete native query machinery checks the
normalized piece and reconstructs the finite source. Theorem 3.1 adds the
missing simultaneous prefix choice; URR's global section remains useful for
one completion at every feasible scalar tuple but does not, by itself,
match prescribed infinite-tree prefixes. The new step is (SLP.11)'s
identity reflection through arbitrary independent nonground native prefix
contexts; the supplied unrestricted URR separator is applied only after
that step. Arbitrary positive residual constraints and a complete search
for common source contacts are not eliminated by this argument.

## 5. A five-hole entire-fiber consumer

Put

$$
F(y)=\langle\alpha,\rho y\rangle,
\qquad
V(x,y,z)=\langle x,\langle y,\langle z,\langle F(y),F(z)\rangle\rangle\rangle\rangle.
\tag{SLP.5}
$$

Use the original root cut $P=\{\varepsilon\}$ and its complete one-hole
old row. The target cut is

$$
Q=\{L,RL,RRL,RRRL,RRRR\}.
$$

Retain the four epoch-zero branch replies at
$\varepsilon,R,RR,RRR$, the epoch-zero $\alpha$ replies at
$RRRLL,RRRRL$, and the positive copied records

$$
(0,RRRLR,1,RL,=),
\qquad
(0,RRRRR,1,RRL,=),
\tag{SLP.6}
$$

including both endpoint guards. All occurrences concern one original
source. The full fiber of these records alone is

$$
D_V=\{V(x,y,z):x,y,z\in\mathcal T\}.
\tag{SLP.7}
$$

Indeed the branch literals give the four-node outer skeleton. The two
$\alpha$ literals force branches at $RRRL,RRRR$ with left child
$\alpha$. Write the first three whole holes as $x,y,z$. Distribution of
$\rho$ through the outer skeleton makes the epoch-one subtrees at
$RL,RRL$ exactly $\rho y,\rho z$. The two guarded equalities therefore
force the last two original holes to be $F(y),F(z)$. Conversely every
$V(x,y,z)$ has every stated literal, both reached endpoints and both
whole-subtree equalities. The original root row supplies no further
restriction. This proves both domain directions on the full source fiber.

Let $\mathcal H$ be any supplied finite list, retaining repetitions, of
negative records between members of $Q$ at supplied nonnegative epochs.
Write $H(u)$ for their conjunction with both guards. The complete protected
input fiber is

$$
D=D_V\cap\{u:H(u)\}.
\tag{SLP.13}
$$

Every position of $Q$ remains reached under every finite iterate of
$\rho$, because the outer branches persist. A history predicate therefore
compares the appropriate entire transformed holes, not just their replies.
If $W_q(x,y,z)$ is the hole value at $q\in Q$, a record
$(a,q,b,q',\ne)$ becomes exactly
$\rho^a W_q(x,y,z)\ne\rho^b W_{q'}(x,y,z)$; its guards hold on $D_V$.
Fixed powers distribute through $F$ and the native pairs. No history
predicate is discarded. The retained successful output is obtained by
[ARH, Proposition 2.1][ARH]'s deterministic source-total paid producer for
these public coordinates, conditional on the complete accessible-state cut.
The same register reaches an authentic common final epoch

$$
N\ge\max\bigl(\{1\}\cup\operatorname{epochs}(\mathcal H)\bigr).
\tag{SLP.14}
$$

The epoch-zero literals and epoch-one positive records are included in
this bound. On a successful protected-history output the fiber is exactly
(SLP.13), not $D_V$ alone. An impossible output is an empty mathematical
fiber; no physical acquisition of that output is asserted.

The five hole values are $x,y,z,F(y),F(z)$. Let $C_Q$ be the complete
outer context, with its four branches and all five reached holes. The two
prescribed complete row labels have this same entire concrete exterior,
and partitions

$$
\begin{aligned}
\pi_=&\ \{\{L,RL\},\{RRL\},\{RRRL\},\{RRRR\}\},\\
\pi_F=&\ \{\{L,RRRL\},\{RL\},\{RRL\},\{RRRR\}\}.
\end{aligned}
\tag{SLP.15}
$$

Denote the labels by $r_=(C_Q,\pi_=)$ and $r_F=(C_Q,\pi_F)$.
They are distinct, and their exact whole strata in $D$ are

$$
\begin{aligned}
D_=^\circ&=\{V(y,y,z):
 y,z,F(y),F(z)\text{ are pairwise distinct},\ H(V(y,y,z))\},\\
D_F^\circ&=\{V(F(y),y,z):
 F(y),y,z,F(z)\text{ are pairwise distinct},\ H(V(F(y),y,z))\}.
\end{aligned}
\tag{SLP.8}
$$

These descriptions retain every pairwise negative, including any redundant
ones, and every history repetition. Their forward direction follows by
filling $C_Q$. For the reverse direction, a source in $D$ is exactly
$V(x,y,z)$ by (SLP.7). The specified partition forces respectively
$x=y$ or $x=F(y)$ and all the other classes distinct, yielding exactly
(SLP.8). No other source shape or exterior has been admitted. Each stratum
predicate, after the displayed substitution for $x$, is a finite mixed
negative conjunction on the entire Cartesian product of finite $y,z$.

For an inhabited protected-history example, repeat any number of times
$(0,RL,0,RRRL,\ne)$. Its predicate is $y\ne F(y)$ on both strata.
Native leaf count satisfies $\ell(\rho t)\ge\ell(t)$ by induction on the
finite tree, so $\ell(F(t))=1+\ell(\rho t)>\ell(t)$. With $y=T_r$ and
$z=T_{r+1}$, the four values are distinct: the two atoms have mass zero,
their $F$ images have mass one, and injectivity of $F$ distinguishes
those images. Thus both strata are nonempty for this history, without
restricting the underlying input fiber to these witnesses.

**Theorem 5.1 (joint finite choice for the prescribed five-hole pair).**
For every finite protected history $\mathcal H$ just specified, there is
a terminating choice for

$$
J(h)\iff\exists u_0\in D_=^\circ,\ u_1\in D_F^\circ,
\quad u_0\equiv_h u_1.
\tag{SLP.16}
$$

If either stratum is empty, $\neg J(0)$. If both are nonempty, a finite
construction supplies actual witnesses for $J(h)$ for every supplied
$h\ge0$, retaining both complete labels and all of $\mathcal H$.

Proof. Finite NSF feasibility decides each full stratum predicate and
returns a finite seed when nonempty. This is a terminating test on the
entire negative conjunction, not a search through a chosen subfamily.
If either predicate is empty, no pair can satisfy (SLP.16), even at zero.
If both are empty there is no surviving stratum. If exactly one is
nonempty, its returned seed retains its label and all history, but is
not a witness for $J$.

Suppose now both are nonempty. Apply [SPC, Theorem 4.2][SPC] to the
proper one-hole context $\langle\alpha,\text{hole}\rangle$ and shift
$a=1$. It supplies the infinite native completion

$$
K=\langle\alpha,\rho K\rangle=F(K).
$$

Let $\Omega$ be the all-branch completion and put

$$
W=V(K,K,\Omega).
\tag{SLP.17}
$$

Both source maps agree at these residuals:
$V(K,K,\Omega)=V(F(K),K,\Omega)$. This equality uses the interpreted
fixed point, not arbitrary common residual limits. No signed history or
finite partition is assigned to $W$.

Here is the required source-level locality. If two finite or completion
trees agree through depth $d$, their images under any fixed $\rho^a$
agree through depth $d$. For one update, prove this by induction on
$d$: matching leaf roots have identical entire finite images; matching
branch roots remain branches and their children are handled at $d-1$.
At $d=0$ only the matching root cases are needed. Absent descendants of
matching leaves therefore agree as well. Iterate for $a$ updates.
Pairing and substitution into a fixed finite constructor context also
preserve depth-$d$ agreement. Consequently, if finite $y,z$ satisfy
$y\equiv_h K$ and $z\equiv_h\Omega$, then

$$
\begin{aligned}
V(y,y,z)&\equiv_h W,\\
V(F(y),y,z)&\equiv_h V(F(K),K,\Omega)=W.
\end{aligned}
\tag{SLP.18}
$$

This checks every original word of length at most $h$. Inside a reached
hole at address $q$, only residual replies through depth $h-|q|$ are
required; the supplied residual depth $h$ suffices for every hole and its
fixed transforms. The complete fixed exterior agrees outright.

For an explicit finite construction of the required prefixes, compute
$q_h=F^{h+1}(\alpha)$. SPC's fixed-point proof gives agreement below
$t$ for consecutive $F^t(\alpha),F^{t+1}(\alpha)$; stabilization therefore
gives $q_h\equiv_h K$. Use the replies of $q_h$ through $h$ for $y$,
and branch replies at every word through $h$ for $z$. These are valid
prefixes of the infinite $K,\Omega$ and have independent live frontiers.
Apply Lemma 2.1 to the entire first stratum conjunction using its NSF
seed, obtaining finite $y_0,z_0$ with these prefixes. Apply it to the
entire second conjunction using its seed, obtaining finite $y_1,z_1$.
Both applications keep every history predicate at its supplied epochs,
every repetition and all six pairwise comparisons of the four distinct
values. Form the actual finite original sources

$$
u_h^=V(y_0,y_0,z_0),\qquad
u_h^F=V(F(y_1),y_1,z_1).
\tag{SLP.19}
$$

By (SLP.8) they belong to $D$, with exactly $r_=$ and $r_F$.
By (SLP.18) each agrees with $W$ through $h$, so
$u_h^=\equiv_h u_h^F$. Thus these two actual sources witness $J(h)$.
Every operation in this mathematical construction is finite for supplied
$h$. The finite feasibility choices plus this proved construction terminate
for every history in the declared class. $\square$

A nonempty surviving stratum in the either-empty case has the same
individual prefix lifting toward $W$, by the corresponding half of the
construction; the pair still has exclusion depth zero. When both are
nonempty the joint witnesses show failure of whole-row prefix determination
on the entire $D$ at every depth. Under the paid common-state premises,
[ARH, (ARH.2.3)][ARH] then excludes a uniform finite-new-read lawful service
on that entire fiber. In the either-empty case, exclusion of this pair
says nothing about the remaining row pairs or their service. All other
row labels belonging to $D$ remain included in both cases.

## 6. Service boundary and attribution

The source contract is the paid source-total acquisition just described,
the complete accessible-state cut, an authentic common epoch, original-root
arbitrary-word `Read`, same-register forward `ApplyRho`, and variable
absorbing `Halt`. The construction supplies no rank, chart, equality, reset,
clone, reroot, identity port, or source-size cutoff. It proves no new cost
optimum: coordinate-worst costs remain distinct from same-run weighted costs,
zero weights remain allowed, and no acquisition, memory, ML-efficiency or
physical-time gain is claimed.

The new deduction is the prefix-substitution identity reflection
(SLP.11), proved using the exact independent-frontier mass coefficients.
The simultaneous cylinder witness then directly consumes URR's existing
separator. The closure equivalence consumes this new reflection and the
whole feasible support. The five-hole application combines it with SPC's
supplied fixed point to preserve arbitrary finite negative protected
histories at one common original-source contact. The fixed-point theorem,
unrestricted separator, scalar support algorithm and finite feasibility
algorithms themselves are credited results.

| Source | Exact reused interface and boundary |
| --- | --- |
| [URR, Definitions 2.1–2.2, Theorem 3.1, Corollary 3.2 and §7][URR] | Native mass, clock and injectivity; one actual simultaneous finite separator; Presburger scalar support with finite grounds. The unrestricted reflection is applied to free frontier variables after substitution. It does not itself reflect identities back through prescribed original prefixes. |
| [NSF, §§4–6][NSF] | Terminating finite signed feasibility, finite original witnesses and each supplied-depth test. These do not decide the all-depth alternative. |
| [NIC, Theorem 4.3 and §§5.1–5.5][NIC] | Exact complete signed image covers, actual finite pair predicate and the unrestricted stopping obligation. No assertion that every cover piece has unrestricted Cartesian residuals is imported. |
| [ARH, Definitions 1.1–1.2, Assumption 1.3 and §§2–3][ARH] | Entire old row and repeated classes, both guarded signs, authentic epoch, paid source-total acquisition, complete cut and original-prefix/service correspondence. The consumer retains the whole protected fiber. |
| [SPC, Theorem 4.2 and its proof][SPC] | The unique interpreted fixed point for the proper context and positive shift, with computable stabilized prefixes. This supplies $K$; arbitrary additional negative histories are preserved here by Lemma 2.1, not by asserting SPC's seed invariant for them. |
| [NLC, Lemma 3.1][NLC] | The accepted atomic minimum-depth and prefix-growth supplier used by SPC. No additional atomic-depth theorem or free native rank constructor is introduced. |
| [Comon–Lescanne, §3.2 Lemma 1, Appendix B.3 and §6.2][CL] | Simultaneous discrimination for the stated infinite free-signature carriers; the one-variable finite-solution argument does not transfer to interpreted native $\rho$. |

H. Comon and P. Lescanne, *Equational Problems and Disunification*,
Journal of Symbolic Computation 7 (1989), 371–425,
DOI 10.1016/S0747-7171(89)80017-3, is the primary mature comparison.
Lemma 1 and Appendix B.3 use finite, in the relevant induction at-most-one,
one-variable solution sets in the free-term setting. Section 6.2 states
that the preceding results do not hold for general nontrivial equational
theories. The native infinite atomic solution family of [URR,
Proposition 7.1][URR] is a concrete reason to retain that boundary. Here
(SLP.9)–(SLP.11) supply the native prefix argument instead. This comparison
is not a literature-wide priority or originality claim.

The statements and constructions are ordinary mathematics. No kernel
verification, implemented solver, undecidability result or actual ML
benefit is claimed.

## 7. Scope and open continuation

Theorem 3.1 gives the exact signed local-prefix lifting criterion for the
entire declared Cartesian grammar (SLP.1), including arbitrary fixed finite
coordinates, simultaneous scalar divergence, both closure implications,
zero dimensions and empty negative conjunctions. Corollary 3.2 requires
explicit neighborhood feasibility. Theorem 5.1 gives the terminating
empty-stratum versus actual all-depth joint-witness choice for the specified
five-hole pair and every protected negative history in its stated class.
It uses neither a partition nor a signed predicate assigned to a limit.

The general NIC5.5 alternative remains open. Arbitrary positive residual
relations, coupled navigation restrictions and the complete search for
source-compatible contacts of arbitrary row pairs are not covered by the
Cartesian premise. Deciding each supplied depth, checking a supplied
productive certificate or deciding feasibility for supplied finite $f$
does not give a terminating all-depth choice for the full declared NIC
class. Additional retained root-depth or $Q$-support restrictions must
likewise be preserved or eliminated by an exact domain correspondence;
they are not presumed Cartesian.

**Open problem 7.1 (contact charts beyond the Cartesian premise).**
Determine whether an arbitrary pair of complete NIC signed image covers
can be refined into finitely many source-faithful charts whose remaining
joint-prefix obligation admits independent live prefix contexts as in
Lemma 2.1, possibly after separate atomic coordinates and finite barriers
have been retained. Such a reduction must preserve every positive residual
relation, every guarded sign and both exact source maps in both directions.
A finite contact certificate would still need a terminating synthesis and
coverage proof for the entire original class. A concrete native obstruction
to this proposed chart reduction would instead identify a different proof
route. Neither result is supplied by the present volume.

[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf

## 追加锚（本行以下为增补区）

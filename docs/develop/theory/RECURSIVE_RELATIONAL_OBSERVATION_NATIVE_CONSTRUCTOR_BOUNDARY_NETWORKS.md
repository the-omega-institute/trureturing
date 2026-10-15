# Recursive relational observation: native constructor boundary networks

## 1. The original native task and its credited finite interface

**Definition 1.1 (source, substitution and literal replies).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,\qquad
h(\langle u,v\rangle)=1+\max\{h(u),h(v)\}.
$$

Pairing is free and ordered. Every finite word in $L,R$, including
$\varepsilon$, is a legal original-root literal. Its reply $r_t(w)$ is
alpha or beta at that leaf, branch at a pair, and absent beyond a leaf.
Write

$$
\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\},
\qquad
\rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

For each public integer $D\ge1$, retain exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
W_D=\{q:|q|\le D-1\},\qquad
\mathcal P_D=\{Rq:q\in W_D\}.
\tag{CBN.1}
$$

All logarithms are base two. The iterates $\rho^kt$ specify prediction
targets; the one actual initial source remains stationary during
preparation and later acquisition.

**Assumption 1.2 (paid preparation and complete retained alphabet).**
A deterministic effective preparation starts source-blind from $D$ and
common installed tables, does not receive the later target, and
terminates on every $t\in\mathcal F_D$. Its source dependence is acquired
only by charged original-root literal Reads. It exports a finite code
$E(t)$. Every accessible surviving source distinction is part of this
code, including control, selectors, buffers, operands, lengths,
allocation, handles, counters and accessible timing distinctions. Any
other accessible field is a function of $E(t)$ and public inputs.
A separately paid handoff and isolation service removes access to all
other preparation material and supplies lawful reader entry.

Only after export is a public source-independent $p\in\mathcal P_D$
supplied. A common deterministic effective reader uses $E(t),D,p$ and
the installed tables to choose zero Reads or one fresh Read of the same
stationary source at an arbitrary finite original-root word. The choice
precedes both its reply and every supplied count. The resulting final
predictor must satisfy

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad(t\in\mathcal F_D,\ p\in\mathcal P_D,\ k\ge0)
\tag{CBN.2}
$$

for every subsequently supplied authentic $k$, with no further Reads.
Define $M_1(D)=\min |E[\mathcal F_D]|$ over these jointly correct
procedures. There is no subtree, equality, source-identity, age, reset,
copying, free-navigation or free-advice port. Export, access isolation,
entry, source continuity and count authentication are declared services.
Preparation work, temporary storage, installed codebooks, post-request
workspace, final predictor size, submitted lengths and letters, authentic
count representation and physical time are separate resources.

**Convention 1.3 (the supplied temporal factor).** Reuse [AAR,
Definition 12.2, Theorem 12.3 and Proposition 13.3][AAR], with
$s(w)=\#L(w)+2\#R(w)$ and $e(\alpha)=0,e(\beta)=1$.
At an original branch endpoint set $\Gamma_q(u)=(0,0)$. Otherwise the
path has a first original blocking leaf at $a$, of label $\ell$, and
$q=ar$. Put

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{CBN.3}
$$

The credited exact decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{CBN.4}
$$

On attained factors $c=1$ implies $b\ge2$. For every $k$ this is
$r_{\rho^ku}(q)$. Conversely the trajectory recovers $b$ as its first
branch count and $c$ by the occurrence of an alpha stage. Thus factors
classify complete trajectories, including initially absent targets.
Different blocking positions can have the same factor. Transport applies
at the actually present blocking leaf, never at an absent target. For
$t=\langle\alpha,v\rangle$,
$\Gamma_{Rq}(t)=\Gamma_q(v)$ and $b\le2D$ for permitted requests.

**Definition 1.4 (all correlated native fibers and complete templates).**
Use [FMR, Definitions 2.1 and 6.1][FMR] and [NDR, Definition 2.1][NDR].
Let

$$
C_0=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup
\{\langle x,y\rangle:x,y\in S_d\}.
\tag{CBN.5}
$$

For $d,n\ge1$, a nonempty $B\subseteq S_d^n$ is jointly admissible if
every target $(i,q)\in[n]\times W_d$ has either a constant value
$\zeta\in G_q:=\Gamma_q(S_d)$ on $B$, or a donor $(j,a)\in[n]\times W_d$
and a total map $\delta:\mathcal A\to G_q$ such that

$$
\Gamma_q(x_i)=\delta(r_{x_j}(a))\quad(x\in B).
\tag{CBN.6}
$$

The witnesses may depend on $B,i,q$, may be off-target, and may form
cycles. All equations refer to the same tuple $x$ and the same relation
$B$. A complete template $\Theta$ chooses one such constant equation or
one donor/decoder equation for every target. Its simultaneous solution
set is $C_\Theta\subseteq S_d^n$, possibly empty. Unattained donor
replies may be assigned any value in the nonempty $G_q$.

Write $K_d(n)$ and $Z_d(n)$ for integral and fractional cover optima of
$S_d^n$ by all nonempty admissible sets. Fractional coefficients are
nonnegative, with covering sum at least one at every tuple. No
independence, donor acyclicity or bound on component size is assumed.
NDR Theorem 2.2 proves that every admissible $B$ lies in a complete
$C_\Theta$ with its chosen witnesses, without changing these optima.

**Convention 1.5 (whole-encoder normalization and supplier boundaries).**
For $h(v)\le d$, the FMR canonical completion $\pi_d(v)$ keeps every
constructor through depth $d-1$ and replaces each branch at that cutoff
by $C_0$. It fixes $S_d$, preserves every $\Gamma_q$, $q\in W_d$, and
preserves all replies on $W_d$. On a canonical tree, a length-$d$ word
returns alpha precisely when its length-$(d-1)$ parent is branch, and
absent otherwise; every longer word returns absent. Thus every finite
probe is simulated by one boundary reply in its original queried block,
or by a constant. This includes arbitrary off-target probes.

FMR Theorems 2.3–2.5 replace the whole encoder by
$E(\langle\alpha,\pi_d(v)\rangle)$ with no increase in attained
alphabet, and identify $M_1(d)=K_d(1)$ by paid cover acquisition. This
does not project children of an unchanged correlated fiber. FMR
Theorems 6.3–6.4 supply the joint restriction and rate relations used
in §8. NCM's depth-two value and cyclic example, and NCE's all-cyclic
mass certificate, keep their original scopes. The public [D3,
Theorems 2.3 and 4.1][D3] supply $M_1(3)=4$ and $\lambda<3/16$.
These are credited results, separate from the constructor correspondence.

## 2. Exact four-valued coordinates on actual canonical trees

**Definition 2.1 (legal constructor arrays).** Put $a_d=2^d-1$ and
$V=[n]\times W_d$. Define

$$
c_d(u)_w=r_u(w),\qquad
c(x)_{(i,w)}=r_{x_i}(w).
\tag{CBN.7}
$$

Let $H_d\subseteq\mathcal A^{W_d}$ consist of arrays $z$ whose root is
not absent and for which every parent-child pair within $W_d$ belongs to

$$
P=\{(\mathsf{branch},\alpha),(\mathsf{branch},\beta),
(\mathsf{branch},\mathsf{branch}),
(\alpha,\mathsf{absent}),(\beta,\mathsf{absent}),
(\mathsf{absent},\mathsf{absent})\}.
\tag{CBN.8}
$$

Thus $(z_w,z_{ws})\in P$ whenever $s\in\{L,R\}$ and $ws\in W_d$.
The joint legal image is $H_d^n$, on the fixed public variable set $V$.
Absent coordinates retain variable-shape information inside the same
four-symbol alphabet.

**Theorem 2.2 (faithful constructor representation).** For all $d,n\ge1$,

$$
c_d:S_d\longrightarrow H_d,\qquad
c:S_d^n\longrightarrow H_d^n
\tag{CBN.9}
$$

are bijections. They use exactly $n(2^d-1)$ four-valued variables, with
no auxiliary realization choice.

Proof. At $d=1$, the nonabsent root symbols alpha, beta and branch
represent exactly $\alpha,\beta,C_0$. This proves both directions at
the cutoff, including a branch whose two alpha children lie just outside
the represented menu.

Inductively suppose $d>1$. If the root of $z\in H_d$ is alpha or beta,
(CBN.8) forces both children absent and then every deeper coordinate
absent. This is precisely the array of that root leaf. If the root is
branch, both children are nonabsent. The two child subarrays separately
satisfy $H_{d-1}$ and so reconstruct unique trees $u_L,u_R\in S_{d-1}$.
Their ordered pair belongs to $S_d$ and has exactly array $z$.

Conversely every actual leaf or pair in (CBN.5) obeys these root and
parent-child rules. Induction therefore makes reconstruction and $c_d$
mutually inverse. Taking products gives $c$, with the stated number of
coordinates. In particular two appearances of the same $(i,w)$ name
one actual reply, rather than independent choices. $\square$

**Convention 2.3 (the canonical boundary, not an additional read port).**
The inverse of $c_d$ reconstructs a canonical tree. It does not recover
unobserved deeper labels of an arbitrary original $v$. For the latter,
$c_d(\pi_d(v))$ is precisely its actual $W_d$ reply table, and
Convention 1.5 is the required whole-encoder bridge. These arrays are
mathematical coordinates; Assumption 1.2 supplies no array to the late
reader. The actual source and all its original-root literals remain as
in Definition 1.1.

## 3. Native temporal levels and every blocking-position collision

**Definition 3.1 (prefix cylinders and factor levels).** Fix $q\in W_d$,
let $l=|q|$, and let $a_i$ be its prefix of length $i$, $0\le i\le l$.
A leaf descriptor $(i,\ell)$ means that the first original leaf on this
path is $\ell$ at $a_i$. Its cylinder in $S_d$ is

$$
D_{i,\ell}=\{u\in S_d:r_u(a_i)=\ell\}.
\tag{CBN.10}
$$

A nonabsent leaf reply already forces every strict ancestor on its path
to be branch. For $\zeta\in G_q$, let

$$
L_{q,\zeta}=\{u\in S_d:\Gamma_q(u)=\zeta\},\qquad
P_{q,v}(\zeta)=\{r_u(v):u\in L_{q,\zeta}\}\quad(v\preceq q).
\tag{CBN.11}
$$

**Theorem 3.2 (relative prefix boxes, with the terminal exception).**
For every $d\ge1$, $q\in W_d$ and $\zeta\in G_q$,

$$
L_{q,\zeta}
=\{u\in S_d:r_u(v)\in P_{q,v}(\zeta)
                         \text{ for every }v\preceq q\}.
\tag{CBN.12}
$$

Relative to actual-tree consistency, every such level is defined by at
most two prefix-reply tests. More precisely it has exactly one of these
forms:

1. $\zeta=(0,0)$, with the test $r_u(q)=\mathsf{branch}$.
2. A single descriptor $(i,\ell)$, with the test $r_u(a_i)=\ell$.
3. Two descriptors $(i,\beta),(i+1,\alpha)$, where the intervening
   letter is $L$ and $i+1<l$, with the tests

$$
r_u(a_i)\in\{\beta,\mathsf{branch}\},\qquad
r_u(a_iL)\in\{\mathsf{absent},\alpha\}.
\tag{CBN.13}
$$

There are no other collisions of complete factors between distinct leaf
descriptors. In particular an adjacent collision at $i+1=l$ is excluded
by the second factor coordinate.

Proof. Every blocked factor has first coordinate at least one, so only
the branch endpoint can give $(0,0)$. Its displayed test is exact.
For descriptor $(i,\ell)$, (CBN.3) has first coordinate

$$
b_i(\ell)=s(q)-s(a_i)+2-e(\ell),
\tag{CBN.14}
$$

also when $i=l$. If $i<j$ and $b_i(\ell)=b_j(\ell')$, then

$$
s(a_j)-s(a_i)=e(\ell)-e(\ell').
\tag{CBN.15}
$$

The left side is a positive integer; the right side is at most one.
Equality therefore forces a single $L$ step, $j=i+1$,
$\ell=\beta$, and $\ell'=\alpha$. For a fixed $i$ the labels give
different first coordinates. Three positions cannot have the same first
coordinate: the first and last would be separated by weight at least
two. These exhaust all possible collisions of first coordinates.

If $j=l$, the earlier descriptor has a nonempty residual consisting of
that last $L$, hence second coordinate zero. The terminal alpha has
second coordinate one. Their complete factors differ. If instead
$j<l$, both residuals are nonempty and end in the same last letter of
$q$. Their second coordinates agree, so these two descriptors do give
the same complete factor. Their cylinders are nonempty in $S_d$:
a path to $a_i$ or $a_j$, with alpha in every unused sibling, has height
at most $l\le d-1$. A branch at $q$ is also feasible, since it needs
height at most $l+1\le d$ and its cutoff completion is allowed.

It follows that each nonbranch level is either one cylinder or the union
of exactly the two cylinders in case 3. A single cylinder is recognized
by its leaf reply. In the two-cylinder case, a beta reply at $a_i$
forces absent at $a_iL$; a branch reply at $a_i$ forces a present child,
which the second test in (CBN.13) makes alpha. The two tests therefore
recognize exactly the union. Each is itself a projection condition of
that level: both beta/absent and branch/alpha alternatives occur.

Every member of a level satisfies all its prefix projection conditions.
Conversely these conditions include the one or two exact tests just
proved, and so imply membership in the level. This proves (CBN.12).
When $q=\varepsilon$ only the three nonabsent root constructors occur,
and the single tests above apply. When $|q|=d-1$, the branch test still
allows $C_0$ at the cutoff; the collision analysis still excludes the
terminal-alpha coincidence. Initially absent $q$ has a strict blocking
prefix and was included throughout. $\square$

**Convention 3.3 (source of the native content).** The all-count formula
is the credited AAR result. The collision classification and relative
prefix-box identity (CBN.12) are repository-derived consequences of that
formula on actual constructor paths. A factor level is a box only
relative to consistent path replies. Neither (CBN.12) nor (CBN.13)
supplies two observations to an execution with one allowed Read, or a
free descriptor locating its blocker.

## 4. Exact compilation of every complete native template

**Definition 4.1 (four-state unary and binary constraints).** For a
chosen donor equation in (CBN.6) and each $v\preceq q$, define

$$
R_{q,v,\delta}
=\{(b,y)\in\mathcal A^2:b\in P_{q,v}(\delta(y))\}.
\tag{CBN.16}
$$

Its variable references are $(i,v)$ and $(j,a)$. If these are the same
reference, use the unary diagonal restriction
$\{b:(b,b)\in R_{q,v,\delta}\}$. For a constant target $\zeta$, use
the unary constraint $z_{(i,v)}\in P_{q,v}(\zeta)$ for every
$v\preceq q$. Include the root nonabsence and parent-child constraints
of Definition 2.1 in every block. Let $\mathcal N_\Theta$ be this
conjunction for all the targets of $\Theta$.

**Theorem 4.2 (auxiliary-free exact native binary realization).** For
every $d,n\ge1$ and every complete template $\Theta$,

$$
c(C_\Theta)=\{z\in\mathcal A^V:z\models\mathcal N_\Theta\}.
\tag{CBN.17}
$$

This is a bijective representation with one array per original tuple,
including when the solution set is empty. In addition to $n$ root and
$n(a_d-1)$ parent-child constraints, at most

$$
n\bigl((d-1)2^d+1\bigr)
\tag{CBN.18}
$$

target constraints suffice. Every relation is unary or binary on the
same four-element domain $\mathcal A$; all relation types belong to a
fixed finite collection independent of $d,n$.

Proof. First restrict to legal arrays by the root and parent-child
constraints. Theorem 2.2 then supplies a unique $x\in S_d^n$ with
$z=c(x)$. Consider one donor equation, and fix its actual donor reply
$y=z_{(j,a)}$. Its compiled constraints say exactly

$$
r_{x_i}(v)\in P_{q,v}(\delta(y))\quad(v\preceq q).
$$

Theorem 3.2 makes this equivalent to
$\Gamma_q(x_i)=\delta(y)$, the original equation. If a reference
coincides with the donor, the diagonal restriction substitutes the same
value $y$ and expresses that very same condition. No independently
chosen copy of $y$ is introduced. For a constant target the unary
constraints are equivalent to its original constant equation by the
same theorem. Conjoining all targets proves both directions of
(CBN.17). Reconstruction is unique, so there is no existential
multiplicity affecting counts.

A target word of length $l$ contributes $l+1$ conditions. There are
$2^l$ such words, and

$$
\sum_{l=0}^{d-1}(l+1)2^l=(d-1)2^d+1.
$$

Induction on $d$ verifies the identity, starting with one at $d=1$.
The rooted binary menu has $a_d-1$ parent-child incidences. These give
the stated counts. There are only $2^4$ unary and $2^{16}$ binary
relations on $\mathcal A$, so the available relation collection is
finite without any depth-dependent domain enlargement. The donor
indices and decoder choices remain part of the specified template.
$\square$

**Convention 4.3 (completeness of target witnesses).** A native network
in Theorem 4.2 carries a declared valid witness for every $(i,q)$,
together with the actual-tree constraints. Arbitrary binary relations
on four states do not by themselves certify native admissibility.
The graph of variable incidences is also different from a graph whose
vertices are whole source rows. NDR §2 and FMR §7 already distinguish
binary relations inside a fiber from pairwise confusability of rows.

## 5. All-competitor constructor-pair saturation

**Definition 5.1 (constructor projection join).** For nonempty
$B\subseteq S_d^n$ put

$$
\begin{aligned}
J_c(B)=\{x\in S_d^n:\;&c(x)_v\in\pi_vc(B)\quad(v\in V),\\
 &(c(x)_v,c(x)_u)\in\pi_{v,u}c(B)
                                      \quad(v,u\in V,\ v\ne u)\}.
\end{aligned}
\tag{CBN.19}
$$

Equivalently, form the unary/binary projection join of $c(B)$ in
$\mathcal A^V$, intersect it with $H_d^n$, and apply $c^{-1}$.
Actual-tree consistency is part of this definition. A repeated variable
is still the same reference, so unary information supplies its diagonal.
For comparison, NDR's whole-block join is

$$
J_2(B)=\{x\in S_d^n:x_i\in\pi_iB,\quad
                (x_i,x_j)\in\pi_{i,j}B\ (i\ne j)\}.
\tag{CBN.20}
$$

**Theorem 5.2 (same-witness saturation for all native competitors).**
For every $d,n\ge1$ and every nonempty admissible $B\subseteq S_d^n$,

$$
B\subseteq J_2(B)\subseteq J_c(B),
\tag{CBN.21}
$$

and $J_c(B)$ is admissible with every chosen donor and every chosen
reply-to-factor decoder of $B$ unchanged, including chosen constants.
Moreover $J_c(J_c(B))=J_c(B)$. Every inclusion-maximal admissible set
is constructor-pair closed, and every $C_\Theta$ is constructor-pair
closed when nonempty. Restricting cover members to constructor-pair
closed admissible sets leaves $K_d(n)$ and $Z_d(n)$ unchanged. The
maximum of any nonnegative mass on $S_d^n$ over admissible sets is
also unchanged by this restriction.

Proof. Fix all the witnesses on $B$. Let $x\in J_c(B)$ and consider
a target $(i,q)$ with donor $(j,a)$ and decoder $\delta$. Put
$y=r_{x_j}(a)$. For each $v\preceq q$, when $(i,v)\ne(j,a)$,
its pair projection with the donor provides a tuple $b^{(v)}\in B$
such that

$$
r_{b^{(v)}_i}(v)=r_{x_i}(v),\qquad
r_{b^{(v)}_j}(a)=y.
\tag{CBN.22}
$$

The witness on $B$ gives $\Gamma_q(b^{(v)}_i)=\delta(y)$.
Consequently $r_{x_i}(v)\in P_{q,v}(\delta(y))$. If the two references
coincide, unary membership supplies a tuple in $B$ with that reply,
and gives the same conclusion. Different prefixes may lift to different
tuples $b^{(v)}$; no common lift is asserted. Their target values are
nevertheless all the same $\delta(y)$ because they have the same donor
reply under the same fixed decoder.

Apply (CBN.12) to the actual tree $x_i$ to obtain
$\Gamma_q(x_i)=\delta(y)$. For a constant target, unary projection
membership alone puts every prefix reply in the corresponding fixed
level's projection, and (CBN.12) gives that constant. Thus every
selected original equation holds throughout $J_c(B)$.

Inclusion $B\subseteq J_c(B)$ follows from its projections. If
$x\in J_2(B)$, two constructor references in different blocks lift
together through the corresponding whole-block pair projection. Two
references in the same block lift through that block's unary projection.
The constructor unary conditions follow too. This proves
$J_2(B)\subseteq J_c(B)$, and $B\subseteq J_2(B)$ is immediate.

For any $B$, enlargement to $J_c(B)$ leaves all its constructor unary
and binary projections unchanged: the defining inclusions give one
direction and $B\subseteq J_c(B)$ gives the other. This proves
idempotence. Maximality now implies $B=J_c(B)$ for maximal admissible
$B$. For nonempty $C_\Theta$, its complete chosen witnesses remain
valid on its join by the first part. Since $C_\Theta$ already consists
of all solutions of those equations, the join cannot add a solution
outside it. Hence $J_c(C_\Theta)=C_\Theta$.

Finally enlarge each member of any integral or fractional cover to its
constructor join. Coverage increases, and its number or total
coefficient does not increase; duplicate members can be combined.
The enlarged sets are admissible, while the restricted class was already
a subclass of all competitors. Both optimum inequalities follow.
Every nonnegative mass is monotone under this enlargement. Since the
universe is finite, a mass maximum exists, and the same argument proves
its equality over the restricted class. $\square$

**Proposition 5.3 (strict one-block separation from the whole-block join).**
There is a native admissible $B\subset S_3$ with

$$
|B|=|J_2(B)|=4,\qquad |J_c(B)|=8.
\tag{CBN.23}
$$

All eight trees use the same donor and decoder witnesses as the four.

Proof. Put $\operatorname{bit}(0)=\alpha$,
$\operatorname{bit}(1)=\beta$, and

$$
u_{a,b,c}=\langle\langle\operatorname{bit}(a),\operatorname{bit}(b)\rangle,
                \langle\operatorname{bit}(c),\alpha\rangle\rangle,
\qquad
B=\{u_{a,b,c}:a\mathbin\oplus b\mathbin\oplus c=0\}.
\tag{CBN.24}
$$

These height-two trees belong to $S_3$. The targets
$\varepsilon,L,R$ are constantly branch. Each of $LL,LR,RL$ is
served by its own literal, mapping alpha to $(2,1)$ and beta to
$(1,0)$. The target $RR$ is constantly $(2,1)$. Thus all seven
native targets have witnesses, and (CBN.4) answers every authentic count.

Exactly the three constructor coordinates $LL,LR,RL$ vary. Every unary
projection of their bits is full, and every binary projection is the
full two-bit square: prescribing two bits determines one
parity-completing third bit. All other coordinates are fixed by unary
projections. The legal constructor join therefore consists exactly of
the eight $u_{a,b,c}$ with unrestricted bits. It has no additional
shapes or labels because those fixed unary projections already fix all
other constructors. The same constant and own-reply witnesses work on
these eight trees. For one whole-block coordinate the unary projection
in (CBN.20) is $B$ itself, so $J_2(B)=B$. $\square$

## 6. Exact counting, shared interfaces and ownership of block weights

**Definition 6.1 (owned block potentials).** For nonnegative functions
$w_i:S_d\to[0,\infty)$, define on legal arrays

$$
\widehat w_i(z_i)=w_i(c_d^{-1}(z_i)),\qquad z_i\in H_d.
\tag{CBN.25}
$$

This potential is owned once by its original block $i$. It can depend
jointly on every constructor coordinate in that block. Let
$\mathcal I_\Theta$ denote the target-constraint occurrences in
Definition 4.1; write $\mathbf1_F(z)$ for the indicator of each
specified constraint $F$. Root and parent-child indicators can instead
be included explicitly when summing over all $\mathcal A^V$, with
block potentials extended by zero off $H_d$.

**Theorem 6.2 (exact native counting with owned potentials).** For every
complete native template and every choice of the nonnegative $w_i$,

$$
\boxed{
\sum_{x\in C_\Theta}\prod_{i=1}^n w_i(x_i)
=\sum_{z\in H_d^n}
       \left(\prod_{F\in\mathcal I_\Theta}\mathbf1_F(z)\right)
       \prod_{i=1}^n\widehat w_i(z_i).}
\tag{CBN.26}
$$

In particular unit weights count each original tuple once. Equality
constraints on incidence replicas, if such replicas are used, preserve
this identity with one valid lift per array. Arbitrary incidence copies
without equality do not have this property.

For this exact carrier, the usual separator and sum-product identities
apply with a single shared separator assignment and with the original
block potentials owned once. A width bound for weighted tables must
include the scopes of these potentials.

Proof. Theorem 4.2 gives a bijection between the tuples in the left
sum and the legal arrays whose target indicators in the right sum
are one. Under this bijection (CBN.25) preserves each weight factor
exactly once. All other arrays have a zero indicator. This proves
(CBN.26), including empty solution sets and zero weights.

Here are the precise intermediate separator identities. They are
standard finite constraint/sum-product reasoning, as in [Forney, §2.2][Forney]
and [Dechter, §§3.1.2, 3.2 and 4][Dechter], applied to (CBN.26).
First take unit weights and form the graph of all binary constraints,
including parent-child constraints. Let $U\subseteq V$ be any chosen
vertex separator and let $\mathcal C$ be the components after removing
$U$. For $\sigma\in\mathcal A^U$, let $I_U(\sigma)$ indicate the
constraints entirely in $U$, and let $N_C(\sigma)$ count assignments
in $C$ satisfying all its constraints and its constraints to $U$.
Then

$$
|C_\Theta|=\sum_{\sigma\in\mathcal A^U}
                 I_U(\sigma)\prod_{C\in\mathcal C}N_C(\sigma).
\tag{CBN.27}
$$

Indeed every extension of a fixed $\sigma$ restricts to one choice
in each component relation. Conversely any such component choices
concatenate with that same $\sigma$ to satisfy every constraint:
there is no binary edge between different components. Restriction
and concatenation are inverse. The sections for different $\sigma$
are disjoint, so summing gives (CBN.27), over at most $4^{|U|}$
assignments. Incompatible sections have zero contribution.

For weights, include every block-potential scope in the factor graph.
Equivalently, join all pairs of variables sharing such a scope in the
primal graph. Choose $U$ so each remaining factor scope lies in
$U\cup C$ for one component $C$, or entirely in $U$. Assign each
factor to that component or to $U$ exactly once. Replace $I_U$ by
the product of the factors owned by $U$, and $N_C$ by the sum of
products of the factors owned by $C$, with $\sigma$ substituted.
The same restriction bijection and finite distributivity prove the
weighted identity. If a block potential straddles two components of
the unweighted graph, that graph alone fails this premise; its joint
potential must be retained or the interface enlarged.

For completeness the corresponding elimination step replaces all
factors $f$ involving a variable $v$ by

$$
g(z_S)=\sum_{a\in\mathcal A}
                  \prod_{f:\,v\in\operatorname{scope}(f)}f(z_S,a),
\quad
S=\left(\bigcup_{f:\,v\in\operatorname{scope}(f)}
                     \operatorname{scope}(f)\right)\setminus\{v\}.
\tag{CBN.28}
$$

All other factors are constant with respect to this sum, so finite
distributivity proves preservation of the total at each step. A supplied
tree decomposition with at most $b$ variables per bag and every factor
scope covered gives exact tables with at most $4^b$ entries. To see the
usual elimination justification, root the decomposition; variables
exclusive to a leaf bag occur nowhere beyond its intersection with the
parent, by connectedness of their bags. Eliminate those variables in
that bag and pass the resulting factor on the intersection to the
parent. Repeating after removing each leaf never requires a scope
outside the current bag. This is the credited finite-width method,
not an assertion that these native networks have a uniform $b$.

Finally replace repeated incidences of any variable by replicas and
constrain them all equal, retaining one representative even if the
variable has no target-constraint incidence. Each original assignment
has exactly one equal-replica lift, and each satisfying replica
assignment descends to that original assignment. Preserve each owned
weight on one designated copy of its arguments. This gives the claimed
one-use identity, the equality-normalization principle in Forney §2.2.
No linear-code or group-duality theorem is needed. $\square$

**Convention 6.3 (interface values and source dependence).** The
$\sigma$ in (CBN.27) is an analytical summation variable. Giving its
actual value to a reader would change the complete attained alphabet
to $|\{(E(t),\sigma(t)):t\in\mathcal F_D\}|$, unless it is already
a function of the code and public data. Acquiring it after the request
must obey the original one-Read rule. Similarly the compiled relations,
donor addresses and graph can be public codebook data selected by $E$;
a further source-varying topology is retained information and must be
included in the code. Nothing in (CBN.26) makes that information free.

## 7. Paid transfer to the unchanged full native task

**Theorem 7.1 (exact original-memory correspondence).** For every
$D\ge1$, $M_1(D)$ is the minimum number of constructor-pair closed
admissible subsets of $S_D$ covering $S_D$. From any correct original
complete code with $m$ attained values, one obtains such a cover with
at most $m$ members and a correct full-family preparation/reader using
at most that many attained names. It retains every original late target,
every authentic subsequent count, and at most one original-root late
Read. Sufficient preparation bounds on every $t\in\mathcal F_D$ are

$$
T_{\rm prep}\le2^D-1,\qquad
Q_{\rm prep}\le D,\qquad
A_{\rm prep}\le(D-1)2^D+1.
\tag{CBN.29}
$$

Every source-bearing late query has length at most $D$. These are the
credited FMR acquisition bounds, not new acquisition optima. The same
cover-restriction equality holds for every joint $K_d(n)$ and $Z_d(n)$,
without removing correlations.

Proof. First use FMR Theorem 2.3's whole-encoder normalization. The
restriction of $E$ to the explicit canonical sources
$\langle\alpha,x\rangle$, $x\in S_D$, has at most $m$ nonempty
fibers. For a fixed name and target, its late query or zero-Read
decision is fixed before a reply and before $k$. Equal replies give
identical predictors, hence identical complete trajectories and factors.
FMR's every-word simulation replaces that arbitrary query by one
boundary experiment or a constant. Thus each canonical fiber is
admissible. This inference changes no child projections and imposes
no target-prefix restriction.

Choose its actual witnesses and enlarge each fiber to $J_c(B)$.
Theorem 5.2 keeps those witnesses and decoders unchanged. The resulting
sets are closed admissible sets covering $S_D$, with at most $m$
members. This proves the required lower inequality against every original
competitor.

Conversely order any such cover, install its witnesses and decoders,
and use the first containing member to name each canonical tree.
The sets may overlap; the actual disjoint name fibers are subsets
of these members and need not themselves be closed. Every chosen
witness remains valid on its assigned subset.

Before any request, submit the actual literals $Rw$, $w\in W_D$,
on the stationary unknown source, including absent replies. These paid
replies determine $c_D(\pi_D(v))$ and hence its canonical tree. Compute
its first-containing-member index and export only that complete name.
There are $2^D-1$ calls, peak length $D$, and
$\sum_{l=0}^{D-1}(l+1)2^l=(D-1)2^D+1$ letters, giving (CBN.29).
Use a fixed-width name and public scan, allocation and padded finite
computation schedule. All other source dependence, including the acquired
array and selection workspace, is isolated under Assumption 1.2.

The installed cover and witness tables are source-independent. In the
construction starting from $E$, its values on canonical trees can be
computed by simulating its terminating preparation on those finitely
many explicitly known finite trees, computing their replies locally.
This is a finite public table-generation computation, rather than
advice about the unknown actual source. Finite enumeration also supplies
a minimum closed cover when no encoder is given. Installation and
membership computation are separate resources.

After $p=Rq$ arrives, the exported index selects its fixed donor literal
$Ra$ or a constant witness. A constant needs no Read. Otherwise one
fresh actual Read at $Ra$ gives the same reply as on the canonical
representative. Its unchanged decoder produces $\Gamma_q(v)$.
Equation (CBN.4) then gives the required reply for every subsequent
authentic $k$. The literal is chosen from $E,D,p$ and common tables,
before any $k$, and no further Read is used. This proves the converse
inequality and the full-family attainment. A minimum cover has no
redundant member; its first-membership naming therefore attains every
name, since a member with no assigned point could be deleted.

For $K_d(n)$ and $Z_d(n)$, Theorem 5.2 gives equality of the cover
optima directly. FMR Lemma 6.2 supplies paid joint attainment by the
same first-membership construction on the entire acquired tuple.
No tuple coordinate is independently recolored or projected.
$\square$

**Proposition 7.2 (joint coordinates at actual occurrences).** Suppose
the block roots $Ra_i$ are public prefix-free, actually present
occurrences in one stationary source, with $|a_i|\le H$. Each block
has height at most $d$. Its canonical coordinate $(i,w)$ is acquired
by the actual original-root literal $Ra_iw$, $w\in W_d$. A sufficient
scan for a joint cover code uses

$$
\begin{aligned}
T&\le n(2^d-1),\qquad Q\le H+d,\\
A&\le n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr).
\end{aligned}
\tag{CBN.30}
$$

A joint target $Ra_iq$ is served by zero Reads or one actual literal
$Ra_jw$ of length at most $H+d$. At every such present occurrence,
its predicted trajectory is the original source's trajectory there.
When $H+d\le D$, these block targets are permitted original targets.

Proof. Original replies at these boundary words equal the corresponding
subtree replies, and canonicalization preserves them. There are
$2^d-1$ suffixes per block. The prefix has length at most $H+1$;
their suffix lengths sum to

$$
\sum_{l=0}^{d-1}l2^l=(d-2)2^d+2.
$$

This proves (CBN.30), also at $d=1$. Acquire the whole tuple and
export its joint first-membership name, with the complete-code isolation
of Theorem 7.1. A declared donor is then implemented by the one
specified original-root word, without moving a subtree into a new
register. Iterating the pairing homomorphism along present ancestors
gives

$$
r_{\rho^kt}(Ra_iq)=r_{\rho^k(t|_{Ra_i})}(q).
\tag{CBN.31}
$$

Here $t|_{Ra_i}$ is mathematical notation for a subtree already
assumed present. It is not an operational input. A virtual wrapper
$\langle\alpha,u\rangle$ has public constant replies at its root
and left cone, and its virtual $Rw$ is implemented only by the actual
literal at the occurrence followed by $w$, as in FMR Lemma 3.1.
It supplies no second source port. The length inequality puts every
$Ra_iq$, $q\in W_d$, in $\mathcal P_D$ when stated.
$\square$

**Convention 7.3 (variable shapes and separate resource coordinates).**
Proposition 7.2 assumes presence; it never transports an absent slot as
a subtree. Theorem 7.1, using the full boundary of the original source,
handles every variable shape without a separately exported cut descriptor.
Its constructor arrays and table membership computation are preparation
workspace isolated at handoff. A finite predictor factor $(b,c)$ has
$0\le b\le2D$, $c\in\{0,1\}$ and can use at most
$\lceil\log_2(2D+1)\rceil+1$ bits, separately from the retained name
and authentic count. Theorems 7.1–7.2 impose no bound on combined
installation, work, workspace, isolation or physical-time efficiency.

## 8. Exact limits of splitting and the remaining global quantifier

**Proposition 8.1 (independent replicas and generic dependence fail).**
Neither of the following replacements is valid: treating repeated
native replies as independent copies, or inferring constructor-pair
saturation for an arbitrary functional-dependence problem without the
native level-set premise.

Proof. For the first assertion take the two actual sources
$\langle\alpha,\alpha\rangle$ and $\langle\alpha,\beta\rangle$
in $\mathcal F_1$. Their literal $R$ has the values alpha and beta.
Two analytic occurrences of this same reply have exactly the two pairs
$(\alpha,\alpha)$ and $(\beta,\beta)$. Independent copies permit
four pairs, including $(\alpha,\beta)$, which no single stationary
source realizes. Equality restores the unique lift.

For the second assertion take $\{0,1\}^3$, experiments $r_j(x)=x_j$,
target $g(x)=x_1\mathbin\oplus x_2$, and
$B=\{x:x_3=x_1\mathbin\oplus x_2\}$. On $B$, $g=r_3$.
All unary and binary coordinate projections are full, so its projection
join is the whole cube. On that cube no one coordinate determines $g$:
with $x_1$ fixed vary $x_2$, with $x_2$ fixed vary $x_1$, and with
$x_3$ fixed vary either of the first two. Thus even a single declared
functional dependence need not survive pair closure. The level
$g=0$ is not a relative box in the first two coordinates. Theorem 3.2,
together with actual-tree consistency, is the extra native premise used
in Theorem 5.2. $\square$

**Proposition 8.2 (arbitrary block potentials need not factor by
constructor).** The potential in (CBN.25) cannot in general be replaced
by a product of unary and binary potentials on its actual constructor
coordinates, even on a fixed actual shape.

Proof. Use the eight actual $u_{a,b,c}\in S_3$ of (CBN.24). Give a tree
weight two when $a\mathbin\oplus b\mathbin\oplus c=0$, and weight
one otherwise. Only the three constructor coordinates $LL,LR,RL$
vary. Any unary or binary factor on constructor coordinates therefore
depends on at most two of these bits. Every assignment to two bits
occurs once among the four even-parity trees and once among the four
odd-parity trees. A unary assignment occurs twice in each; a constant
occurs four times in each. Thus the product of any one such factor's
values over the even-parity trees equals its product over the odd-parity
trees. The same equality holds for any product of these factors.

For the specified weight the corresponding products are $2^4=16$ and
$1$, a contradiction. All weights are positive, so a putative
nonnegative factorization has no zero on any argument attained by these
eight trees; zeros elsewhere cannot avoid this contradiction. Extend
the weight by one to all remaining canonical states. A factorization
on $S_3$ would restrict to the excluded factorization on these eight
trees. Thus even binary compilation of the native indicator constraints
does not binary-factor an arbitrary original block mass. Exact weighted
separator calculations require the ownership and scopes in Theorem 6.2.
$\square$

**Convention 8.3 (conditional all-size lower certificates).** The
all-competitor carrier in (CBN.26) retains NDR Proposition 3.3's
quantifier. If $w:S_d\to[0,\infty)$ has total $W>0$, and a positive
$C$ satisfies

$$
\sum_{z\in H_d^n}
       \left(\prod_{F\in\mathcal I_\Theta}\mathbf1_F(z)\right)
       \prod_{i=1}^n\widehat w(z_i)\le C^n
\quad\text{for every }n\ge1\text{ and every complete }\Theta,
\tag{CBN.32}
$$

then the credited native mass/restriction argument gives

$$
M_1(D)\ge\left\lceil(W/C)^{2^{D-d}}\right\rceil\quad(D\ge d),
\qquad \lambda\ge2^{-d}\log_2(W/C).
\tag{CBN.33}
$$

Indeed every admissible fiber is contained in a $C_\Theta$ by NDR
Theorem 2.2, so (CBN.26) and (CBN.32) bound its mass by $C^n$.
Restrict the original code to the one actual perfect-scaffold slice
with $n=2^{D-d}$ canonical blocks. Its arbitrary original-root query
is a constant or a function of one reply in a single actual block,
by FMR Theorem 6.3's restriction. Each restricted fiber is admissible,
and these fibers partition mass $W^n$. Their number is at least
$\lceil(W/C)^n\rceil$ and at most the original complete alphabet.
The limit defining $\lambda$ gives (CBN.33). This is the existing
mass argument on the exact new carrier, with no new numerical bound.

The carrier has $n(2^d-1)$ variables and unrestricted donor topology.
Binary arity and a four-element alphabet place no bound on $n$, a
chosen separator or the bags needed to cover all factors. Equations
(CBN.27)–(CBN.28) evaluate specified finite networks; they provide no
uniform estimate for (CBN.32).

**Definition 8.4 (effective lower-convergence obligation for the original rate).**
With the unchanged native quantities, FMR supplies

$$
\begin{aligned}
\sigma_d&=\inf_{n\ge1}\frac{\log_2K_d(n)}n,
\qquad \lambda=\sup_{d\ge1}2^{-d}\sigma_d,\\
0&\le\lambda-2^{-d}\sigma_d\le2^{-d}\phi,\qquad
\phi=\lim_{h\to\infty}2^{-h}\log_2U_h,\quad
U_0=1,\ U_{h+1}=1+U_h^2.
\end{aligned}
\tag{CBN.34}
$$

Theorem 5.2 preserves these optima over every length. It leaves open
an explicit effective error

$$
\sigma_d\ge\frac{\log_2K_d(n)}n-\eta_d(n),\qquad
\eta_d(n)\longrightarrow0,
\tag{CBN.35}
$$

or a complete effective all-template lower hierarchy with certified
approximation error. At fixed $d,n$, finite enumeration computes cover
optima and network masses. A finite $K_d(n)$ bounds its defining
infimum from above. Finite maximal masses bound an all-length supremum
from below; they cannot certify the upper bound needed in (CBN.32).
No reversal of these inequalities follows from an exact recoding.
The constructor correspondence alone does not establish completeness
of product-weight certificates for $\sigma_d$.

The general exact $M_1(D)$, sharp $\lambda$ and broader recovery
programme therefore retain their original goals. A relation requiring
further control is the all-size family of complete native constructor
networks with their owned block potentials, or a lawful alternative
with a proved uniform loss. The strict example in Proposition 5.3
does not give such a loss estimate. NDR's bounded-original-block
obstruction does not exclude lawful finer cuts or global recoloring.
No noncomputability, physical geometry, causal realization or universal
two-body sufficiency follows from this constructor representation.

## 9. Attached source correspondences and mathematical attribution

**Convention 9.1 (native mathematical suppliers).** NDR and FMR
citations refer to the public repository at
`b45e51761afc5b5f00d7d336389675c4354c2ed7`. NDR §§1–3 supply the
all-count factor notation, complete whole-block templates, whole-block
binary join and finite mass obligations. Its §§7–9 concern a fixed
original-block repair obstruction and one particular paired-module
recut; Theorem 5.2 instead covers every $d,n$ and every admissible
native relation, with the strict separation (CBN.23). FMR §§2–3 and
6 supply the global canonicalization, actual-literal simulation,
paid cover attainment, native gluing and regularized rates.

AAR §§12–13 supply the exact temporal factor and its real blocking
collisions; Theorem 16.3 supplies canonical boundary realizations,
including terminal branches within the height bound. Its fixed-menu
passive codes and exact acquisition endpoint differ from the late-target
one-Read objective. NCM Theorem 4.1 gives
$\sigma_2=\log_2(25/17)$ and a finite-length error; NCM Proposition
6.1 supplies a cyclic native fiber. NCE Theorems 2.2 and 6.1–6.2
give the all-cyclic heavy-target mass certificate and its full-family
consequence. Neither is an assertion of matching covers. The public D3
source is cited at `adcbf94cc7e654c1baeecbdb57a843c7a1ecaef5`;
its exact depth-three value and improved upper keep their stated
full-family, arbitrary-query scopes.

**Convention 9.2 (precise D5 carriers and hypotheses).** In
[GenealogicalFiberTransport][D5G], `Source = FreeMagma Bool`, true
labels alpha, false labels beta, and `substitution` is the lifted map
in Definition 1.1. In [ActualTreeReadoutAcquisition][D5A],
`Address = List Bool`, false means $L$, true means $R$, and
`Reply`/`readout` give every literal's four-valued reply. Its
`Positive`/`Strategy` recognition task is a different endpoint.

In [NativeDepthPatterns][D5N], `original_present_transport` assumes
`subtree a u = some t`; Proposition 7.2 uses exactly actual present
occurrences. `original_prefix_locality` requires original replies to
agree through the requested word length. Its `depthEquiv` and
`frontier_geometry` describe reached positions and actual fillings
mathematically, rather than supplying operational navigation.

The theorem `target_family_minimal_quotient` in
[TargetFamilyMinimalQuotient][D5T] assumes every target passively
factors through one readout; it gives the joint-kernel quotient,
without one-probe repair geometry. The theorem
`compact_observation_factorization` in [CompactObservationFactorization][D5C]
assumes a nonempty compact space, compatible continuous surjective
finite discrete observations whose fibers form a topological basis,
and continuous finite readouts. Its bounded action-window clause also
assumes a finite action type and continuous actions. Finite-level
existence under those hypotheses supplies neither an effective native
acquisition bound nor a memory-rate convergence modulus.

**Convention 9.3 (primary correspondences and failed transfers).** The
standard representation and elimination ingredients in Theorem 6.2 are
`literature-attested` intermediates. The native level geometry,
constructor compilation, same-witness saturation, strict original
example and operation-preserving transfer are `repo-derived` ordinary
deductions. These attributions make no worldwide-originality claim.

| Primary source | Exact use and boundary |
| --- | --- |
| G. David Forney Jr., *Codes on Graphs: Fundamentals*, §2.2, [arXiv:1306.6264v2][Forney] | Normal realization replaces multiple incidences by equality-constrained replicas. Equality gives one lift per assignment in Theorem 6.2. Linear/group duality and minimal-realization results are not applied to these nonlinear native relations. |
| Rina Dechter, *Bucket elimination: A unifying framework for probabilistic inference*, UAI 1996, §§3.1.2, 3.2 and 4, [primary PDF][Dechter] | Multiply factors and eliminate a variable by summation; complexity depends exponentially on induced width, and conditioning enumerates shared assignments. Native constraint indicators and owned block potentials give exactly this finite sum-product setting. No native uniform-width hypothesis is supplied by the paper. |
| Martin Dyer and David Richerby, *An Effective Dichotomy for the Counting Constraint Satisfaction Problem*, finite-domain language setup, [arXiv:1003.3879v4][DR] | A fixed finite language on a finite domain has arbitrarily large finite instances. The four-state language here retains complete native witness provenance; no complexity classification or effective regularized-cover convergence follows from this setup. |
| Tomasz Gogacz and Szymon Toruńczyk, *Entropy bounds for conjunctive queries with functional dependencies*, Theorem 1 and Corollary 1, [arXiv:1512.01808v1][GT] | A fixed schema's size exponent is characterized by the almost-entropic cone under relation-size and dependency constraints; submodularity gives an outer relaxation. A native witness gives $H(\Gamma_q(X_i)\mid r_{X_j}(a))=0$ under one common law. Variable-database achievability does not prove completeness over all native lengths, maps and donors. |
| Jeroen Zuiddam, *The asymptotic spectrum of graphs and the Shannon capacity*, Theorem 1.1, [arXiv:1807.00169v2][Z] | Requires closure under disjoint union and strong product, inclusion of $K_1$, and the cohomomorphism preorder; spectral maps are monotone, additive, multiplicative and normalized. Constructor constraint graphs are not source-confusability graphs. No cardinality-preserving native semiring/product/preorder identification is assumed. |
| David de Boer, Pjotr Buys and Jeroen Zuiddam, *The asymptotic spectrum distance, graph limits, and the Shannon capacity*, §§1–3 and Theorem 3.7, [arXiv:2404.16763v2][DBZ] | Fraction-graph approximations from above converge in the specified full spectrum distance. These native relations have no proved identification with that family or effective spectrum-distance control. The continuity result supplies no native numerical modulus. |
| Nicolas Charpenay, Maël Le Treust and Aline Roumy, *On the Linearization of Optimal Rates for Independent Zero-Error Source and Channel Problems*, §§II–III, [arXiv:2407.02281v2][CLR] | The independent problems use specified source/channel graph products. Native fibers may correlate every block and use off-target donors. No replacement of those fibers by independent graph interfaces is made. |
| Holger Boche and Christian Deppe, *Computability of the Zero-Error Capacity with Kolmogorov Oracle*, Theorem 12 and Remark 38, [arXiv:2001.11442v3][BD] | Capacity suprema, Fekete limits, oracle semicomputability and computable converse approximants are distinguished. General Shannon-capacity computability is stated as unknown. There is no reduction giving a native computability or noncomputability conclusion here. |

[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[NCM]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[D3]: https://github.com/the-omega-institute/trureturing/blob/adcbf94cc7e654c1baeecbdb57a843c7a1ecaef5/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[D5G]: ../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[D5A]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[D5N]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5T]: ../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean
[D5C]: ../../../D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.lean
[Forney]: https://arxiv.org/html/1306.6264v2
[Dechter]: https://arxiv.org/pdf/1302.3572
[DR]: https://arxiv.org/html/1003.3879v4
[GT]: https://arxiv.org/html/1512.01808v1
[Z]: https://arxiv.org/html/1807.00169v2
[DBZ]: https://arxiv.org/html/2404.16763v2
[CLR]: https://arxiv.org/html/2407.02281v2
[BD]: https://arxiv.org/html/2001.11442v3

## 追加锚（本行以下为增补区）

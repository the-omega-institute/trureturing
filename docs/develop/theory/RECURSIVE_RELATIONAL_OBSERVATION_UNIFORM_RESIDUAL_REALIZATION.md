# Uniform residual realization for native mixed templates

## 1. Native objects and the exact quantifiers

**Definition 1.1 (native trees).** Throughout,

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle x,y\rangle&=\langle\rho x,\rho y\rangle,\\
T_j&=\rho^j\alpha\qquad(j\in\mathbb N).
\end{aligned}
\tag{URR.1}
$$

Trees are nonempty, finite, ordered and free as binary trees. The operation
$\rho$ has the displayed interpreted constant laws. It is not an extra
free unary constructor. All finite trees are allowed; there is no common
size, depth or rank bound.

**Definition 1.2 (mixed templates).** Fix finite dimensions $k,m\ge0$.
A mixed template has grammar

$$
A::=g\mid T_{n_j+c}\mid\rho^a(z_i)\mid\langle A,A\rangle,
\qquad 1\le j\le k,\quad1\le i\le m,
\tag{URR.2}
$$

where $g\in\mathcal T$ is a supplied finite ground tree and $a,c$ are
supplied nonnegative integers. Different occurrences may have different
fixed exponents and offsets. Repeated names $n_j,z_i$ always have the same
value. Evaluation uses $\mathbf n\in\mathbb N^k$ and
$\mathbf z\in\mathcal T^m$.

Let $\mathcal L=((A_\ell,B_\ell))_{\ell=1}^s$ be a finite list, retaining
repetitions, and write

$$
D(\mathbf n,\mathbf z)=
\bigwedge_{\ell=1}^s A_\ell(\mathbf n,\mathbf z)
\ne B_\ell(\mathbf n,\mathbf z).
\tag{URR.3}
$$

Each negative compares the entire two evaluated trees. It is not a
conjunction of inequalities between corresponding children. The empty
conjunction is true. The products $\mathbb N^0$ and $\mathcal T^0$ each
contain exactly the empty tuple.

The residual quantifier is over the **full Cartesian product**
$\mathcal T^m$. It contains no additional positive equation, image
condition, language restriction, endpoint-reach predicate or source-size
promise. Section 4 proves this premise for a specified acquired family;
it is not presumed for arbitrary positive histories.

**Definition 1.3 (policies).** A rank policy $P$ is any subset of
$\mathbb N^k$ when discussing logical quantifier exchange. An effective
Presburger description of $P$ is additionally required when claiming an
effective Presburger description or decision for the policy-restricted
support. An arbitrary subset is not declared Presburger merely by calling
it a policy. No policy supplies the unknown source's ranks to an observer.

## 2. Native invariants and the separating tuple

**Definition 2.1 (coding and mass suppliers).** Use [ABC, Theorems
2.2–2.3][ABC]. A normal atomic code is a tree over primitive leaves $[j]$
and a binary constructor $F$, with no subtree $F([j+1],[j])$. Native
pairing is represented by

$$
J(X,Y)=
\begin{cases}
[j+2],&X=[j+1],\ Y=[j],\\
F(X,Y),&\text{otherwise}.
\end{cases}
\tag{URR.4}
$$

The canonical coding $B$ and expansion $E$ are effective inverse maps
between $\mathcal T$ and the normal codes. In particular $B(T_j)=[j]$,
$j\mapsto T_j$ is injective, and $\rho^a$ adds $a$ to every primitive
rank while preserving every $F$ node. Consequently $\rho$ is injective;
its image is not all of $\mathcal T$.

Let $\gamma(u)$ count the $F$ nodes of $B(u)$, as in [CAR, Definition
2.1 and the proof of Theorem 2.2][CAR]. The supplied identities give

$$
\begin{aligned}
\gamma(T_j)&=0,&\gamma(\rho^a u)&=\gamma(u),\\
\gamma(\langle u,v\rangle)&\le1+\gamma(u)+\gamma(v),\\
\gamma(\langle u,v\rangle)&=1+\gamma(u)+\gamma(v)
&&\text{if }\gamma(u)>0\text{ or }\gamma(v)>0.
\end{aligned}
\tag{URR.5}
$$

The last equality holds because a pair with a nonprimitive child cannot
be the exceptional pair in (URR.4). The parent mass is always at least
either child mass, including when both children have mass zero. This is
constructor mass, not native leaf count. Atomic trees have mass zero at
arbitrarily large rank and arbitrarily large native size.

We also reuse the clock from [ARH, Lemma 19.2][ARH]:

$$
\kappa(\alpha)=0,\qquad\kappa(\beta)=1,\qquad
\kappa(\langle u,v\rangle)=2+\kappa(v),\qquad
\kappa(\rho u)=\kappa(u)+1.
\tag{URR.6}
$$

Thus $\rho^p u=\rho^q u$ implies $p=q$ for every finite native $u$.
No positive period or invertible physical action is introduced.

**Definition 2.2 (one finite tuple).** Define a weight on the finite
input syntax by

$$
\begin{aligned}
w(g)&=\gamma(g),&w(T_{n_j+c})&=0,&w(\rho^a z_i)&=0,\\
w(\langle A,B\rangle)&=1+w(A)+w(B).
\end{aligned}
\tag{URR.7}
$$

Let $M$ be the maximum of zero and the weights of all sides in
$\mathcal L$, and let $d$ be the maximum of zero and all residual
decoration exponents occurring there. Put

$$
\begin{aligned}
G&=M+1,&C_0&=\alpha,&C_{r+1}&=\langle C_r,\alpha\rangle,\\
b_i&=(i-1)(d+1),&z_i^\star&=\rho^{b_i}(C_G)
\quad(1\le i\le m).
\end{aligned}
\tag{URR.8}
$$

This is a terminating construction from the finite input alone. It never
evaluates an unknown rank or source. For $m=0$ its output is the empty
tuple. Unused residual names may still be assigned by (URR.8).

**Lemma 2.3 (three separation facts).** For every rank vector:

1. A residual-free subtemplate of the input has mass at most $M$.
2. A subtemplate containing a residual occurrence has mass at least $G$
   at $\mathbf z^\star$. If its root is an explicit pair, its mass is
   at least $G+1$.
3. For occurring decorations, equality
   $\rho^a(z_i^\star)=\rho^b(z_j^\star)$ implies $i=j$ and $a=b$.

Proof. In the first assertion, induction on the residual-free syntax
using (URR.5) bounds its mass by its weight. Subtemplate weights are at
most the weight of a containing input side, since every pair adds one
and all weights are nonnegative. Fixed ground trees are included by the
definition of $w$; their native sizes need not be small.

The code of $C_1=\langle\alpha,\alpha\rangle$ is
$F([0],[0])$, so $\gamma(C_1)=1$. For $r\ge1$ its successor has a
positive-mass left child. Equation (URR.5) gives
$\gamma(C_{r+1})=1+\gamma(C_r)$, and hence $\gamma(C_G)=G$.
All decorated chosen residuals have mass $G$ by invariance. Moving up
from any such occurrence never decreases mass. At a pair containing
such an occurrence, the positive child prevents collapse and contributes
the strict additional one. This proves the second assertion.

For the third, both trees are iterates of the same $C_G$. Applying
(URR.6) to their equality gives $b_i+a=b_j+b$. The integer intervals
$[b_i,b_i+d]$ are pairwise disjoint, because their starting points differ
by multiples of $d+1$. Since $0\le a,b\le d$, first $i=j$ and then
$a=b$. Conversely identical labels certainly have identical values.
This also accounts for every repeated occurrence. $\square$

## 3. Uniform equality reflection and common completion

**Theorem 3.1 (rank-independent residual equality reflection).** The
computable tuple in Definition 2.2 satisfies, simultaneously for every
$\mathbf n\in\mathbb N^k$ and every listed pair,

$$
A_\ell(\mathbf n,\mathbf z^\star)=B_\ell(\mathbf n,\mathbf z^\star)
\quad\Longleftrightarrow\quad
\forall\mathbf z\in\mathcal T^m\quad
A_\ell(\mathbf n,\mathbf z)=B_\ell(\mathbf n,\mathbf z).
\tag{URR.9}
$$

Proof. Fix $\mathbf n$ only for the proof; Definition 2.2 has already
been performed without it. Prove the forward implication for any two
input subtemplates by induction on the sum of their syntax sizes,
assuming their values at $\mathbf z^\star$ are equal.

If neither contains a residual, both values are independent of the
residual assignment, so the implication holds. If exactly one contains
a residual, their masses lie respectively above or equal to $G$ and
below $G$, contradicting equality by Lemma 2.3.

It remains that both contain residuals. Each root is either a decorated
variable or an explicit pair. A decorated variable has mass exactly $G$;
a residual-containing pair has mass at least $G+1$. Thus a variable/pair
comparison cannot be equal. If both roots are decorated variables,
Lemma 2.3 forces their names and exponents to agree. Their values then
agree for every assignment, with the shared-variable convention intact.
If both are pairs, injectivity of the actual native ordered constructor
gives equality of both corresponding children at $\mathbf z^\star$.
Both child comparisons have smaller total syntax size. Induction makes
each a universal residual equality at this same $\mathbf n$; reassembling
the pairs gives the desired equality.

These cases exhaust (URR.2). They use native pair injectivity even when
its atomic code collapses; they never infer free-code syntax from a
native equality. The reverse implication is evaluation at the finite
tuple $\mathbf z^\star$. The argument works for every rank vector using
the very same constants $M,d,G,b_i$.

The mass argument in the proof of Theorem 3.1 uses the equal-mass
variable/compound separation method of [NativeGroundSeparation][NGS].
Its finite Boolean free-magma length bound becomes a rank-uniform bound
here through $\gamma(T_{n_j+c})=0$. The clock then separates all the
listed decorations of each shared residual. The infinite solution family
in Proposition 7.1 explains why the syntactic finite-exception argument
of [Comon–Lescanne, §3.2 Lemma 1 and Appendix B.3][CL] is not a substitute
for that native mass-and-clock proof; their §6.2 distinguishes general
equational theories from the free-term case. $\square$

**Corollary 3.2 (one simultaneous completion at every feasible rank).**
For all $\mathbf n\in\mathbb N^k$,

$$
\exists\mathbf z\in\mathcal T^m\ D(\mathbf n,\mathbf z)
\quad\Longleftrightarrow\quad D(\mathbf n,\mathbf z^\star).
\tag{URR.10}
$$

Define the entire feasible-rank support and coordinate domain by

$$
S=\{\mathbf n:\exists\mathbf z\ D(\mathbf n,\mathbf z)\},
\qquad X=\{(\mathbf n,\mathbf z):D(\mathbf n,\mathbf z)\}.
\tag{URR.11}
$$

The map $\sigma:S\to X$, $\sigma(\mathbf n)=(\mathbf n,\mathbf z^\star)$,
is a section of the rank projection: $\operatorname{pr}_1\sigma$ is
the identity on **all** of $S$. It does not assert $X=\sigma(S)$.

One can compute a Presburger formula $\Psi(\mathbf n)$ defining
exactly $S$. For a Presburger rank condition $K$, the exact support of
$K(\mathbf n)\land D(\mathbf n,\mathbf z)$ is
$K(\mathbf n)\land\Psi(\mathbf n)$, and the same section restricts
to that entire support.

Proof. If a tuple satisfies all the negatives, no listed equality is
universal in the residuals. By Theorem 3.1 none holds at
$\mathbf z^\star$, so that one tuple satisfies all the negatives
together. Conversely it is itself a finite witness. This is a joint
argument for the conjunction, not a choice of different tuples for its
different conjuncts.

Equation (URR.10) proves the section identity on all of $S$.

For the arithmetic formula, substitute the concrete finite tuple in
every listed side. Each
side becomes a finite pair template over $T_{n_j+c}$ and constant-rank
atoms: expand fixed ground trees using $T_0=\alpha,T_1=\beta$.
The residual substitutions and their fixed powers are finite ground
trees and are treated in the same way.

Apply the equality part of [CAR, Lemma 4.1][CAR]. For completeness of the
parameter match, at each pair of primitive children $[r],[s]$ split
into the Presburger cases $r=s+1$ and $r\ne s+1$. The former gives
$[s+2]$, the latter retains $F([r],[s])$. A nonprimitive child forces
the ordinary $F$ case. There are finitely many pair nodes. Each branch
has a fixed normal shape and nonnegative affine primitive ranks.
Two such normal codes are equal exactly when the shapes agree and all
corresponding ranks agree. ABC's inverse maps make this native equality.

Let $E_\ell(\mathbf n)$ be the resulting equality formula. Then

$$
\Psi(\mathbf n)=\bigwedge_{\ell=1}^s\neg E_\ell(\mathbf n)
\tag{URR.13}
$$

is exact by (URR.10). In this grammar it can be expressed using Boolean
combinations of affine rank equalities. No rank enumeration or finite
rank cutoff is involved. Conjunction with $K$ proves the restricted
statement. Presburger decisions and witness extraction use [CAR, §4][CAR].

For this arithmetic step, projection alone does not require Theorem 3.1.
The proof of [NSF,
§§2–4, especially Lemma 3.2 and Theorem 4.3][NSF] already gives the
following parameter extension. Leave designated atomic-leaf scalars
$n_j$ free, allow a primitive definition $Z=[n_j+c]$, and carry the
resulting offset constraints through the same finite branches. These
primitive shapes are the same constant shape as NSF's other explicit
scalar leaves. NSF's completeness proof retains the actual scalar ranks
at explicit leaves when it replaces residual shape blocks. It therefore
retains the designated $n_j$ as well. Its separation of scalar and block
constraints prevents that replacement from silently changing a parameter.

The resulting finite disjunction of scalar formulas, existentially
quantified over the auxiliary ranks only, is already a Presburger
projection in $\mathbf n$. Soundness expands the same normal codes;
completeness keeps the same parameter values. This is the scalar-preserving
projection supplied by NSF, alongside its native existential feasibility
and supplied-depth consequences. Its residual replacement may depend on
the scalar parameters; (URR.9)–(URR.12) use one fixed native tuple.

For a non-Presburger policy $P$, the set is exactly $P\cap S$ and the
same section restricts to it. No effective presentation of an arbitrary
$P$ is inferred. $\square$

**Corollary 3.3 (policy-uniform quantifier exchange).** For every subset
$P\subseteq\mathbb N^k$, with the same tuple constructed before $P$,

$$
\begin{aligned}
&\forall\mathbf n\in P\ \exists\mathbf z\in\mathcal T^m\
 D(\mathbf n,\mathbf z)\\
\Longleftrightarrow\;&
\exists\mathbf z\in\mathcal T^m\ \forall\mathbf n\in P\
 D(\mathbf n,\mathbf z)\\
\Longleftrightarrow\;&
\forall\mathbf n\in P\ D(\mathbf n,\mathbf z^\star).
\end{aligned}
\tag{URR.12}
$$

Proof. The first statement and (URR.10) give the third at every member
of $P$. The third gives the second by choosing $\mathbf z^\star$.
The second gives the first by using its witness at each rank. If $P$
is empty, the universal statements are true and the existential statement
is true because $\mathcal T^m$ is nonempty, including $m=0$.
For $k=0$ the rank space is a singleton, so the same proof applies to
its two possible policies. If the list is empty, $S=\mathbb N^k$ and
every displayed assertion has its literal empty-conjunction meaning.
For $m=0$, equality reflection simply compares residual-free values,
and the empty tuple supplies all claimed witnesses. $\square$

## 4. An entire acquired feedback and packing family

**Definition 4.1 (finite family descriptions).** Choose $k,m,s\ge0$ and
the following finite data.

- A finite ordered binary context $C$ with a fixed concrete exterior.
  Its hole occurrences have role labels
  $\mathcal H=\{A_1,\ldots,A_k,Z_1,\ldots,Z_m,V_1,\ldots,V_s\}$.
  Every role occurs at least once; a role may occur arbitrarily many
  times. Number actual holes in address order. The intended old partition
  puts two occurrences in the same class exactly when their role labels
  agree. Fix one original representative address $p_H$ for each role.
- For each payload role $V_t$, a mixed template $E_t$ of (URR.2), using
  only the rank generators $n_j$ and residual generators $z_i$.
  Different payloads may share any of these generators and may contain
  any finite number of their repeated decorated occurrences.
- The mandatory finite literals and positive links in Definition 4.2,
  any finite list of the rank-only refinements in Definition 4.4, and
  any finite list of whole negative records at the structural endpoints
  in Definition 4.3. These lists, including all repetitions, are the
  complete retained history for this family.

The old original cut $A$ is exactly the hole-address set of $C$; it is
finite and prefix-free. The old row $R=(C,\pi)$ includes its entire
concrete exterior, numbered holes and the complete role partition $\pi$.
If there are no roles, $C$ is a supplied finite ground tree and $A$ is
empty. The context may otherwise be a single root hole. Nothing permits
dropping an old class because it is irrelevant to a later task.

**Definition 4.2 (literal and positive installation).** For each atomic
role $A_j$ retain the literal $(0,p_{A_j},\mathsf{branch})$ and the
positive record

$$
(1,p_{A_j}L,\ 0,p_{A_j},\ =).
\tag{URR.14}
$$

For a payload $E_t$, traverse its finite template syntax at the original
representative $p_{V_t}$. At every explicit pair position $q$, retain the
literal $(0,p_{V_t}q,\mathsf{branch})$. At a ground token $g$, retain
the exact finite constructor/leaf description of $g$ at that position:
read every node of $g$, with its branch, $\alpha$ or $\beta$ reply.
At a token $\rho^a(z_i)$ retain the positive link

$$
(0,p_{V_t}q,\ a,p_{Z_i},\ =),
\tag{URR.15}
$$

and at a token $T_{n_j+c}$ retain

$$
(0,p_{V_t}q,\ c,p_{A_j}R,\ =).
\tag{URR.16}
$$

All are actual history coordinates on the same original source. Template
tokens are merely the public rule for choosing those finite coordinates;
they are not semantic replies. The endpoint predicates include reach
on both sides of every link. If a token is at the payload root, $q$ is
empty. Copies of a role have the same entire value by the old partition,
so installing at the representative also fixes every copy.

Introduce the mathematical reconstruction

$$
\begin{aligned}
F_{A_j}(\mathbf n,\mathbf z)&=\langle T_{n_j+1},T_{n_j}\rangle=T_{n_j+2},\\
F_{Z_i}(\mathbf n,\mathbf z)&=z_i,\\
F_{V_t}(\mathbf n,\mathbf z)&=E_t(\mathbf n,\mathbf z),\\
\Theta(\mathbf n,\mathbf z)&=C[(F_H(\mathbf n,\mathbf z))_{H\in\mathcal H}].
\end{aligned}
\tag{URR.17}
$$

Every occurrence of one role in $C$ uses that same $F_H$.

**Definition 4.3 (structural endpoints and whole negatives).** Expand
the finite syntax of (URR.17), displaying each atomic-role value as the
pair in its first line and expanding fixed ground tokens when needed.
A structural position follows only the displayed pair skeleton and may
stop at any displayed node or token. It does not descend into an unknown
residual token or into an undisplayed atomic expansion. Such a position
$p$ has a definite subtemplate $F_p$ of grammar (URR.2). It is reached
in every $\Theta(\mathbf n,\mathbf z)$.

At any fixed epoch $e\ge0$, that same original position is still reached,
with entire subtree $\rho^e F_p(\mathbf n,\mathbf z)$. Distribute
$\rho^e$ through the explicit pairs: a ground token becomes a fixed
ground tree, $T_{n_j+c}$ becomes $T_{n_j+c+e}$, and $\rho^a(z_i)$
becomes $\rho^{a+e}(z_i)$. Thus its value is again a mixed template.

Permit any finite list of signed negative records
$(a,p,b,q,\ne)$ with $p,q$ structural positions, at any fixed epochs.
The translated negative is the **whole** comparison of these two
subtemplates. Both native endpoint guards hold by the structural proof
just given; they are justified, not replaced by the negation of equality.
The position can include the original root or an ancestor spanning many
payloads, so the comparisons are not restricted to sibling leaves or
one residual variable.

**Definition 4.4 (rank-only refinements).** A rank region is a structural
position whose displayed subtemplate contains no residual occurrence.
It includes the atomic cells and fixed ground exterior pieces. Permit
additional literals at fixed epochs and arbitrary fixed suffixes below
such regions, and additional positive links between two such endpoints.
Their values and reach depend only on $\mathbf n$. Apply [CAR, Lemma
4.1][CAR] to these residual-free templates to obtain a Presburger formula
$K(\mathbf n)$ for **all** these records. In a positive link its formula
contains both endpoint guards and its equality. In a literal it includes
the precise reply, with absence allowed only when that is the retained
literal reply. Let $K$ be true for the empty refinement list.

This permits arbitrary fixed ground restrictions and actual rank tests
within the family, without permitting a new restriction on a residual
subtree. An optional external rank policy is a further mathematical
restriction; it is not an extra acquired rank port.

**Lemma 4.5 (exact positive correspondence).** Temporarily impose the
old concrete exterior and all within-role old equalities, the mandatory
records of Definition 4.2, and all refinements of Definition 4.4. Leave
the different-role old inequalities and the additional negative records
for Theorem 4.6. The resulting set of sources is in effective bijection
with

$$
\{(\mathbf n,\mathbf z)\in\mathbb N^k\times\mathcal T^m:
K(\mathbf n)\},
\tag{URR.18}
$$

through $\Theta$. In particular its residual coordinates are genuinely
unrestricted, for each admissible rank vector.

Proof. Start with a source satisfying those positive data. The old
exterior and within-role equalities give exactly $C[(u_H)_H]$, with
$u_H=u|_{p_H}$ unique. At $A_j$, the branch literal writes
$u_{A_j}=\langle x_j,y_j\rangle$. The original path $p_{A_j}L$
survives the update, because all its original ancestors are pairs.
Its epoch-one subtree is $\rho(x_j)$. The two guarded endpoints of
(URR.14) therefore assert

$$
\rho(x_j)=\langle x_j,y_j\rangle.
\tag{URR.19}
$$

The complete finite feedback classification is reused from [ARH,
Application 26.1][ARH]: there is one and only one $n_j\ge0$ with
$(x_j,y_j)=(T_{n_j+1},T_{n_j})$. Its premises are exactly (URR.19)
on finite native trees. Thus $u_{A_j}=F_{A_j}$, and the original right
subtree at its representative is $T_{n_j}$.

Set $z_i=u|_{p_{Z_i}}$, with no restriction on this finite native tree.
At a payload pair node the retained branch literal permits ordered
decomposition. At a ground token the full finite literal description
fixes exactly that ground tree: every listed leaf stops the tree there.
At a residual token the positive link gives precisely $\rho^a(z_i)$;
at an atomic token its link gives precisely $\rho^c(T_{n_j})$.
Original paths to the generator subtrees persist under $\rho$, so these
are the actual recorded-epoch endpoint values. Induction up the finite
payload syntax gives $u_{V_t}=E_t(\mathbf n,\mathbf z)$.
The rank-region navigation and both guards in the remaining positive
links translate exactly to $K(\mathbf n)$. This proves the source-to-
coordinate direction, including every fixed literal and positive link.

Conversely take any $\mathbf n$ satisfying $K$ and any finite tuple
$\mathbf z\in\mathcal T^m$. Fill $C$ by (URR.17). Its exterior and
all repeated roles have the prescribed values. The atomic cells satisfy
(URR.19) by $T_{n+2}=\langle T_{n+1},T_n\rangle$ and
$\rho T_{n+1}=T_{n+2}$. They are branches, including $n=0$.
Their left and right positions are reached. Every explicit payload pair
and ground node has its retained literal, and both endpoints of every
token link are reached with the values in (URR.15) or (URR.16).
All rank refinements hold with their guards by the exact interpretation
of $K$. Thus the constructed source satisfies every asserted positive
condition, without any extra assumption on $\mathbf z$.

Finally the ranks are recovered uniquely from the $A_j$ right subtrees
by atomic-index injectivity; each residual is recovered from its
$Z_i$ representative. Hence equal reconstructed sources have equal
coordinates. Payloads and repeated role copies are already determined.
This proves both directions and uniqueness, including zero coordinates.
All constructions are finite on a supplied source or supplied tuple.
The inverse is a mathematical operation on a given tree, not an
observer operation. $\square$

**Theorem 4.6 (the entire acquired fiber).** Form a finite list
$\mathcal L_C$ consisting of:

1. $F_H\ne F_{H'}$ for every two distinct old roles $H,H'$;
2. every translated whole negative record of Definition 4.3, retaining
   repetitions and its actual endpoint coordinates.

Let $D_C$ be their conjunction and define the full original-source fiber

$$
U=\{u:R_A(u)=R,\ H_0(u),\ H_{\rm rel}(u)\},
\tag{URR.20}
$$

where $H_0,H_{\rm rel}$ are exactly all the prescribed records. Then
$\Theta$ is a bijection

$$
\{(\mathbf n,\mathbf z):K(\mathbf n)\land
D_C(\mathbf n,\mathbf z)\}\ \longrightarrow\ U.
\tag{URR.21}
$$

Proof. A source in $U$ satisfies the positive conditions of Lemma 4.5,
so has its unique coordinates with $K$. Its complete old partition says
that different roles have unequal whole subtrees. These are exactly
item 1, including all off-task classes. Every additional negative has
two reached endpoints and the exact mixed values established in
Definition 4.3, so item 2 holds. This gives one inclusion.

Conversely, a tuple satisfying the left side of (URR.21) constructs a
source satisfying all positive and literal data by Lemma 4.5. Its old
cut positions are all reached and its concrete exterior is exactly $C$.
Occurrences of the same role are equal; item 1 prevents every unwanted
cross-role equality. Thus its whole old partition is exactly $\pi$.
Item 2, together with both
structurally proved endpoint guards, gives each negative signed record.
Rank-refinement guards were already imposed by $K$. Hence every record
holds on this single original source and its old row is exactly $R$.
Uniqueness is the uniqueness in Lemma 4.5. $\square$

The temporary positive set in Lemma 4.5 is only a proof device. Equation
(URR.21) restores every old inequality and every signed record and is the
domain used for all subsequent statements. It is not a statement that
arbitrary positive histories admit such a presentation.

## 5. One common background on the entire feasible rank set

**Theorem 5.1 (uniform completion of every described acquired family).**
For every finite description of §4, apply Definition 2.2 to its whole
list $\mathcal L_C$. It computes one finite tuple $\mathbf z_C^\star$
and, by Corollary 3.2, a Presburger formula $\Psi_C$ such that the
exact rank support of the entire fiber $U$ is

$$
S_C=\{\mathbf n:K(\mathbf n)\land\Psi_C(\mathbf n)\}.
\tag{URR.22}
$$

For every $\mathbf n\in S_C$ the source
$s_C(\mathbf n)=\Theta(\mathbf n,\mathbf z_C^\star)$ belongs to $U$.
The rank map $\pi_C:U\to S_C$ supplied by the unique coordinates
satisfies $\pi_C\circ s_C=\operatorname{id}_{S_C}$. The residual tuple
is independent of $\mathbf n$, $K$, and any optional rank policy once
the finite negative templates have been fixed.
For nonempty $U$, under Assumption 6.1's complete accessible-state cut,
this is the entire successful output fiber of the paid producer of
[ARH, Proposition 2.1][ARH], at any authentic final epoch $N$ at least
every recorded epoch. The common section therefore applies to that
acquired fiber, with the producer's full sourcewise correspondence and
its separately charged acquisition costs.

Proof. Theorem 4.6 supplies precisely the full Cartesian residual
hypothesis of Corollary 3.2. Thus the existence of a source of rank
$\mathbf n$ is equivalent to
$K(\mathbf n)\land D_C(\mathbf n,\mathbf z_C^\star)$, whose exact
arithmetic formula is (URR.22). The same equivalence proves membership
of every displayed $s_C(\mathbf n)$. Coordinate uniqueness proves the
section identity. The construction consults only $\mathcal L_C$;
rank-only refinements can change $K$ without changing that tuple.
The section is defined on the whole support, even if infinite or empty.

For any policy $P$, Corollary 3.3 applies to $D_C$ on $P\cap\{K\}$.
Equivalently, if the requirement is to realize *each* rank of $P$ as a
source satisfying every record, then

$$
\begin{aligned}
&\forall\mathbf n\in P\ \exists\mathbf z\quad
K(\mathbf n)\land D_C(\mathbf n,\mathbf z)\\
\Longleftrightarrow\;&\exists\mathbf z\ \forall\mathbf n\in P\quad
K(\mathbf n)\land D_C(\mathbf n,\mathbf z)\\
\Longleftrightarrow\;&\forall\mathbf n\in P\quad
K(\mathbf n)\land D_C(\mathbf n,\mathbf z_C^\star).
\end{aligned}
\tag{URR.23}
$$

If $P$ contains a rank violating $K$, all three statements are false;
if $P$ is empty all three are true. Thus changing the policy does not
require choosing a new residual background.

For the acquired-input assertion, apply [ARH, Proposition 2.1][ARH]
with public old cut $A$, every literal of Definitions 4.2 and 4.4,
every endpoint occurrence of Definitions 4.2–4.4, retaining repetitions,
and final $N$ at least all their epochs. These are finite public lists
independent of the unknown source. The supplier traverses the actual
finite original source to obtain the whole old row, performs forward
updates on the same register, and acquires every requested literal and
whole comparison endpoint by paid original-root reads with its actual
prefix. Both endpoint guards are required: an absent endpoint gives the
supplier's distinct invalid outcome, never a successful negative.

Every $u\in U$ gives the stipulated row, literals and signs by
(URR.20), reaches actual epoch $N$, and yields the same retained state
under the complete cut. Conversely every original source yielding that
retained state has exactly the old row and every guarded predicate in
(URR.20), hence belongs to $U$. The cut includes authentic $N$ and the
common ready state and excludes no still accessible source-bearing
field. This proves both directions of the retained-state correspondence
for the application, with nonempty $U$ as required for service entry.

The supplier terminates on each finite source; its fixed public list of
requested coordinates does not impose a uniform bound on traversal
costs over $U$. Pre-cut finite descriptions are paid memory, not physical
register clones; comparisons, updates, authentication and retention have
their separate costs. Forgetting a traversal or retaining a short sign
refunds none of those costs. The common tuple is not used to obtain or
replace any actual reply. $\square$

**Proposition 5.2 (a scalable infinite subfamily).** For arbitrary integers
$k,r\ge1$, take $m=r$ and payload roles $V_{j,i}$ for every
$1\le j\le k$, $1\le i\le r$, with

$$
E_{j,i}=\langle T_{n_j},z_i\rangle.
\tag{URR.24}
$$

Choose any context containing two copies of every role and any additional
fixed finite ground exterior. Give precisely the role partition, and
install all the feedback cells and payload links of §4. Take no rank
refinements or extra negatives. The full set of old inequalities still
compares every pair of different atomic, residual and payload classes.

Its feasible-rank support is exactly

$$
\{\mathbf n\in\mathbb N^k:n_j\ne n_h\text{ whenever }j\ne h\}.
\tag{URR.25}
$$

At each feasible rank the residual and source sizes are unbounded within
this same fiber, with each residual shared by all its $k$ payloads and
every role repeated in the old row.

Proof. Necessity follows from the distinct atomic-role classes and
injectivity of $T_n$. For sufficiency choose any $H\ge1$ and set
$z_i=\rho^{i-1}C_H$. These residuals have mass $H$ and are pairwise
distinct by the clock. The atomic roles have mass zero and the payloads
have mass $H+1$. Thus no equality crosses these three groups. Two payloads
are equal exactly when their left atomic children and right residual
children are respectively equal; the distinct ranks and distinct
residuals force the same indices $(j,i)$. Every old inequality therefore
holds. Theorem 4.6 gives an actual original source in the full fiber.

The indices in (URR.25) are unbounded; for $k=1$ every natural rank is
allowed. At each feasible rank, $H$ can increase without bound, producing
unbounded residual and source sizes inside this very same fiber. Each
$z_i$ is shared by all $k$ payloads involving it, and every role is
repeated in the old row. The numbers of generators, payloads, old classes
and links are arbitrary finite input data. Thus these are an infinite
family of finite descriptions. Section 4 also permits arbitrary mixed decorations, ground payloads and additional
whole-template negatives beyond (URR.24). $\square$

## 6. Paid acquisition and the actual action boundary

**Assumption 6.1 (authentic acquired input).** For a nonempty fiber $U$
of (URR.20), impose exactly [ARH, Assumption 1.3][ARH]. The specified
row and all records have been acquired by paid operations. The actual
single original-root register is $\rho^N u$, for an authenticated
$N$ at least every recorded epoch. The complete accessible state is a
fixed function of the retained input and common parameters and recovers
that input. Its original-source fiber is exactly $U$.

All still accessible source-bearing caches, addresses, traversal lengths,
counts, control positions, timing fields, handles, permissions, outputs
and archives belong to that complete state. No unlisted field retains a
distinction among sources in $U$. This is an access-cut assumption, not
a claim that mathematics erases physical information. A merely plausible
list of signs without its actual acquisition does not meet the assumption.

**Definition 6.2 (service class and costs).** A permitted service
remains a common deterministic effective controller, correct and
terminating on every actual $u\in U$. For a prescribed finite prefix-free
original target cut $Q$, correctness still means returning the entire
$R_Q(u)$: reached original holes in their specified order, the complete
concrete exterior, and the full whole-subtree equality partition. The
empty cut retains the complete source; the root cut gives the one-hole
row. No service for this target is furnished by the section theorem.
Its source operations are
original-root $\mathsf{Read}(p)$ for any finite word
$p\in\{L,R\}^*$, including absent addresses; forward same-register
$\mathsf{ApplyRho}$; and absorbing $\mathsf{Halt}$. Replies may control
later actions, and the halt time may vary with the source. There is no
reset, clone, reroot, identity, rank, chart, unknown-subtree equality or
free inverse port. Updates convey no extra source-dependent information.

For a service $A$ on one source write

$$
\begin{aligned}
c_A(u)&=(q_A(u),a_A(u),\ell_A(u)),&
\ell_A(u)&=\sum_{\text{actual reads at }p}|p|,\\
b(A)&=(\sup_Uq_A,\sup_Ua_A,\sup_U\ell_A),&
W_\lambda(A)&=\sup_{u\in U}\lambda\cdot c_A(u),
\qquad\lambda\in\mathbb Q_{\ge0}^3.
\end{aligned}
\tag{URR.26}
$$

Every actual read counts, including repeats and absence; $a_A$ counts
actual post-entry updates. Root reads have length zero but cost one call.
The weighted sum is taken on the same run before the supremum.
Coordinate maxima can come from different sources; the two objectives
cannot be identified. Zero weights remain allowed, and do not remove
source-total correctness or the obligation to halt. Installation, local
work, address generation, storage, acquisition, authentication, retention,
output, physical time and energy are separately supplied costs.

The section selects a possible source at each rank; it does not
identify the unknown original source, supply a source port or produce
an observer reply or causal message. Restricting an optimization or recovery question from
$U$ to $s_C(S_C)$ would change its domain and is not justified here.
The construction bounds the mass of its chosen witnesses only. It does
not bound the sizes of all sources, even at one fixed feasible rank, as
Proposition 5.2 shows. Nor does fixed residual mass bound the size of
$s_C(\mathbf n)$ as the atomic ranks increase.

For this same full $U$, fixed finite histories and a fixed finite target
cut, [NPL, Theorems 4.1 and 5.3][NPL] already decide finite versus
infinite native output images and the complete row image. Their finite
answers enumerate every output with an original realizing source;
their infinite answers give original sources with pairwise distinct
outputs. Under Assumption 6.1 and the actual-action contract above,
[NPL, Theorem 6.2][NPL] also decides bounded recovery of the reached
set and concrete exterior and supplies its paid static consumer.
The partition remains part of the full row target. Finite row image
alone does not supply its bounded observation.

When the entire original source fiber is finite and nonempty,
[NPL, Theorems 7.1 and 8.1–8.2][NPL] enumerate that entire fiber and
give a finite family dominating every legal adaptive comparator on each
same source. Their exact Pareto basis and attained rational nonnegative
same-run weighted minima include zero weights. Finiteness is decided
from the original retained input; it is not an added source-size promise.
Neither a finite list of rows nor the common section $s_C(S_C)$ satisfies
the entire-finite-fiber hypothesis merely by being a list of witnesses.

For infinite fibers with finite row image, uniform observation of the
remaining partition and optimization over arbitrary physical words are
the separate obligations of [NPL, Open problems 10.1–10.2][NPL]. The
common section supplies no determining original-prefix depth or actual
service for those obligations. The source bijection (URR.21) applies to
the finite descriptions of §4; it is not a positive normalizer for
arbitrary native histories. Empty instances remain empty mathematical
fibers; all service assertions retain the nonempty-fiber premise.

## 7. Boundaries of the uniform construction

**Proposition 7.1 (native avoidance and the Cartesian hypothesis).**
For the one-pair list formed from the two sides of

$$
\rho^2(z)=\langle\rho(z),z\rangle
\tag{URR.27}
$$

Definition 2.2 supplies a witness to its disequality although the
corresponding equation has infinitely many finite native solutions.
For the list $(z,\beta)$, adding either $z=\alpha$ or the requirement
that the original left child of $z$ be absent gives a feasible constrained
problem whose solutions exclude the tuple from Definition 2.2.
Consequently the full Cartesian residual domain in Theorem 3.1 and the
independent positive correspondence in Lemma 4.5 cannot be omitted.

Proof. For (URR.27), the input weights give $M=1$, $G=2$, and the single
residual is $z^\star=C_2$. Its mass is two by Lemma 2.3. The supplied
mass identities [CAR, Definition 2.1 and Theorem 2.2 proof][CAR] give
masses two and five for the two sides, so they differ at this tuple.
In contrast, the supplied atomic recurrence and injectivity [ABC,
Theorems 2.2–2.3][ABC] give equality at every $z=T_j$, with all these
finite trees distinct. More generally positive mass $\gamma(z)$ gives
masses $\gamma(z)$ and $1+2\gamma(z)$, so equality is impossible there; in particular $C_1$ refutes the equation.
The native solution $\rho(\beta)=\langle\beta,\alpha\rangle$ also
satisfies the interpreted feedback equation used in Lemma 4.5.
These credited native identities provide the transfer boundary for the
construction: syntactic one-variable finite-exception arguments and a
free occurs-check on interpreted $\rho$ do not justify its separation.

For $(z,\beta)$, the weights give $M=0$, $G=1$ and $z^\star=C_1$.
The assignment $z=\alpha$ satisfies $z\ne\beta$ and each of the two
stated extra restrictions. But $C_1=\langle\alpha,\alpha\rangle$ is
neither $\alpha$ nor a tree with an absent original left child.
Thus the common tuple for the unrestricted negative need not satisfy
an added positive residual equation or a reach restriction. An exact
positive correspondence must eliminate such a restriction with proof
or retain it in its domain; it cannot classify it as rank-only merely
by choosing coordinates. $\square$

## 8. References and mathematical correspondences

The following citations specify the mathematical interfaces used in
the definitions and proofs above.

| Source | Reused content and boundary |
| --- | --- |
| [ARH, Assumption 1.3, Proposition 2.1, Lemma 19.2 and Application 26.1][ARH] | Complete acquired fiber, both endpoint guards, paid producer, native injectivity/clock, and the exact finite feedback classification. Constructor elimination and the graph results of §§19–32 do not assert unrestricted Cartesian residuals for every positive history. |
| [ABC, Theorems 2.2–2.3 and 3.2][ABC] | Native/normal-code bijection, rank translation, image bounds and guarded navigation. No ambient free-code replacement for native pairing is made. |
| [CAR, Definition 2.1, Theorem 2.2 proof and Lemma 4.1][CAR] | Constructor mass, its positive-child formula, and arithmetic equality/navigation on fixed finite atomic templates. Its cycle-covered whole-source coordinates require atomic coverage; arbitrary residuals here are not declared atomic. |
| [CRF, Proposition 1.3 and §§2–6, Open problem 9.1][CRF] | Exact constructor-elimination charts and their physical-word/resource interface. Those hypotheses are not automatically conferred on the family here by an existence section. |
| [GRS, Proposition 2.1 and §§4–5][GRS] | Entire acquired graph correspondence and its action/resources under its own hypotheses. The same original source controls both copies. Selecting representatives can change prices, as its Proposition 7.1 explains. |
| [SRF, Definition 1.1, Lemma 1.3 and §§2–3][SRF] | Original-root routing, synchronous family resources, and separate coordinate and same-run objectives. A residual witness is not a common physical action. |
| [TPO, Corollaries 4.2–4.4][TPO] | Nondefinability in its specified ambient term-power language. A formula-dependent finite substitution does not define the all-shape native normal domain or its total canonicalization graph. |
| [NSF, Lemmas 3.2, 4.1–4.2, Theorem 4.3 and Corollary 4.4][NSF] | Existential native feasibility, equal-mass nonleaf shape markers, block replacement, scalar preservation and formula-dependent witnesses. Scalar preservation already supplies the atomic-rank projection extension in the proof of Corollary 3.2. Witness templates are not the entire source domain. |
| [NPL, Theorems 4.1, 5.3, 6.2, 7.1 and 8.1–8.2][NPL] | Exact finite/infinite native images, whole-row image classification, exterior bounded recovery, and exact entire-finite-fiber resources under the common-state and actual-action hypotheses of §6. These are the supplier applications in Definition 6.2; neither an output list nor a section replaces the original domain. |
| [NativeGroundSeparation][NGS], including private statements | `count_length`, `evaluated_length`, `compound_mass_ne`, `bounded_eval_injective`, `code_mass`, `code_injective` and public `simultaneous_ground_separation` establish the finite Boolean free-magma separation mechanism with fixed finite term-length bounds. They do not contain unbounded atomic-rank parameters or coupled native $\rho$ decorations. The proof of Theorem 3.1 uses the equal-mass method with constructor mass and the native clock. |
| [FIB whitebox volume][FIB] | Its observer, information and resource distinctions separate a mathematical completion from actual source information, as in Definition 6.2. |

The primary citations below specify the transfer conditions in the
proof of Theorem 3.1 and Proposition 7.1 and the endpoint convention
in Definition 4.3.

| Primary source | Mathematical passage and correspondence |
| --- | --- |
| H. Comon and P. Lescanne, [*Equational Problems and Disunification*][CL], §3.2 Lemma 1, Appendix B.3, and §6.2; PDF pp. 15, 35–36 and 30 | finite conjunctions of nontrivial syntactic disequations have ground solutions over the stated infinite sort carriers. Appendix B.3 uses the finite, in its induction at-most-one, one-variable solution property. Section 6.2 explicitly says the preceding free-term results do not hold for general equational theories and discusses special extensions. Proposition 7.1 is the concrete native obstruction to importing that finite-exception proof. |
| A. Reuß, [*Normalization of Horn Clauses with Disequality Constraints*][REUSS], §2.1 p. 16, §3.2.4 Theorem 18 and Corollary 17 pp. 59–60, §3.3 pp. 65–67 | hom-disequalities compare images after a given tree homomorphism. Theorem 18 constructs a finite list of ground terms eliminating an existential variable for its stated labeled-path disequalities and automata predicate, uniformly in the remaining substitution. This is a relevant existing finite-witness result. Section 3.3 handles homomorphic-image comparisons in its specified Horn/automata classes. No singleton rank-independent native completion is inferred without an exact encoding and its hypotheses. |
| G. Godoy, O. Giménez, L. Ramos and C. Àlvarez, [*The HOM problem is decidable*][HOM], §§2.1–2.2, Definition 2.4, PDF pp. 3–4 | ranked-tree homomorphisms use specified constructor images and substitution. At the end of §2.1 a path disequality is true if either endpoint is missing, as well as when both reached subtrees differ. Native signed histories instead require both endpoints reached for either sign. The automata results cannot silently replace this guard contract. |

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[CAR]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[CRF]: RECURSIVE_RELATIONAL_OBSERVATION_CONSTRUCTOR_RESOURCE_FRONTIER.md
[GRS]: RECURSIVE_RELATIONAL_OBSERVATION_GRAPH_RESOURCE_SEPARATION.md
[SRF]: RECURSIVE_RELATIONAL_OBSERVATION_SYNCHRONOUS_RESOURCE_FRONTIER.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[FIB]: FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[NSF]: https://github.com/the-omega-institute/trureturing/blob/9289f512403121af5115e3af0d808f85f11d481b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: https://github.com/the-omega-institute/trureturing/blob/b343383cdf485cdff33784b18c37ba5b6954f1f1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[NGS]: https://github.com/the-omega-institute/trureturing/blob/ac6649d4d23e9d97ab24c2cc0922937e31acc87c/D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[REUSS]: https://mediatum.ub.tum.de/doc/1116533/document.pdf
[HOM]: https://www.cs.upc.edu/~ggodoy/papers/homproblem2.pdf

## 追加锚（本行以下为增补区）

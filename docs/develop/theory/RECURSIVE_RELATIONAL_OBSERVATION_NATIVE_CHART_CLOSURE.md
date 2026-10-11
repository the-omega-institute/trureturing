# Exact native prefix closure of complete signed charts

> This generic-v1 volume contains ordinary definitions and proofs. Its
> mathematical suppliers are cited at their stated domains. It is reference
> input, with no assertion of Lean verification. Integrated sections are
> retained; subsequent additions and corrections follow the append anchor.

## 1. Native sources, complete charts and the unchanged target

**Definition 1.1 (the finite native algebra).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle u,v\rangle&=\langle\rho u,\rho v\rangle,\\
T_n&=\rho^n\alpha\qquad(n\in\mathbb N).
\end{aligned}
\tag{NCC.1}
$$

Every source is nonempty, finite and ordered, with no common size, depth,
shape or rank bound. Pairing is the actual ordered binary constructor;
$\rho$ is the displayed interpreted operation. A reply $r_u(p)$ at an
original word $p\in\{L,R\}^{*}$ is $\alpha$, $\beta$,
$\mathsf{branch}$ or $\mathsf{absent}$. Write $u\sim_h v$ for equality
of every reply at $|p|\le h$. Depth is inclusive.

For a finite prefix-free original cut $Q$, the full row $R_Q(u)$ records
all reached positions in their prescribed order, the entire concrete
exterior with precisely those subtrees replaced by numbered holes, and
all whole-subtree equality classes. The empty cut retains the whole
source as exterior; an absent cut position contributes no hole.

**Assumption 1.2 (the entire original fiber).** Retain the complete input
of [PDC, Assumption 1.2][PDC] and [ARH, Assumption 1.3][ARH]:

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{NCC.2}
$$

Here $R$ is the entire old row, $H_0$ is the entire finite literal list,
and $H_{\rm rel}$ is the entire finite signed mixed-epoch list. A record
$(a,p,b,q,\bowtie)$ requires

$$
p\in\operatorname{Pos}(\rho^a u),\quad
q\in\operatorname{Pos}(\rho^b u),\quad
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q,
\qquad\bowtie\in\{=,\ne\}.
\tag{NCC.3}
$$

Both endpoint guards apply to either sign. All records concern the same
source. Repeated names and classes, different-class inequalities,
off-task negatives, every literal and the old concrete exterior remain
in (NCC.2). Mathematical consistency questions allow an empty $D$;
service questions retain $D\ne\varnothing$.

**Assumption 1.3 (complete native chart interface).** A chart has a
finite mixed native source template $\Theta$ and domain

$$
\begin{aligned}
\mathcal C&=\{(\mathbf n,\mathbf z)\in
\mathbb N^k\times\mathcal T^m:K(\mathbf n)\land
\Gamma(\mathbf n,\mathbf z)\},\\
\Gamma&=\bigwedge_{\ell=1}^{s} A_\ell\ne B_\ell,\\
A&::=g\mid T_{n_j+c}\mid\rho^a(z_i)\mid\langle A,A\rangle,
\qquad g\in\mathcal T,\quad a,c\in\mathbb N.
\end{aligned}
\tag{NCC.4}
$$

All exponents and offsets are fixed finite constants; repeated coordinate
names have shared values. $K$ is an effective scalar Presburger formula.
Every member of $\Gamma$ is a whole native disequality. The residual
carrier is exactly the full Cartesian $\mathcal T^m$, with no positive,
image, navigation, language or normality predicate outside $\Gamma$.
Zero dimensions and empty conjunctions have their literal empty-product
meanings.

[PDC, Theorem 5.2 and §§6–8][PDC] is the separately supplied ordinary
paper producer of this interface for arbitrary (NCC.2). It gives
injective source maps covering every original source, without any
cutoff. It discharges all positives, literals and both guards exactly,
and retains all negatives, including its nonprimitive-sort negatives
$\rho^2z\ne\langle\rho z,z\rangle$. Its templates also retain every
field of $R_Q$.

When the full row image is finite, apply that producer to each entire
predicate $u\in D\land R_Q(u)=r$ for every attained row $r$. The resulting
finite list $(\mathcal C_i,\Theta_i,r_i)$ includes all branches and
satisfies

$$
\Theta_i[\mathcal C_i]\subseteq\{u\in D:R_Q(u)=r_i\},\qquad
D=\bigcup_i\Theta_i[\mathcal C_i].
\tag{NCC.5}
$$

The exact finite image and attainment are supplied by [NPL, Theorem
5.3][NPL]. A uniform residual completion section is not a replacement
for any $\mathcal C_i$.

**Definition 1.4 (the original stopping question).** The unchanged
question is to decide

$$
\exists H\in\mathbb N\quad
\forall u,v\in D\quad
u\sim_H v\ \Longrightarrow\ R_Q(u)=R_Q(v).
\tag{NCC.6}
$$

In the finite-image case, [PDC, Corollary 8.3, equation (23)][PDC]
identifies its negation with a fixed distinct-label chart pair satisfying

$$
r_i\ne r_j,\qquad
\forall h\in\mathbb N\quad
\exists a\in\mathcal C_i,\ b\in\mathcal C_j\quad
\Theta_i(a)\sim_h\Theta_j(b).
\tag{NCC.7}
$$

The pair and both full finite labels are fixed before $h$ varies. The
results below calculate closure at supplied coordinate points and give a
two-direction semantic correspondence for (NCC.7). They do not decide the
unrestricted existential over all such points in (NCC.6).

## 2. Supplied coordinates and the exact topology

**Definition 2.1 (native completion and atomic coordinates).** Let
$\overline{\mathcal T}$ be all finite or infinite ordered full binary
$\alpha/\beta$ trees. Give it the four-reply prefix topology, whose basic
neighborhood of $Z$ at inclusive depth $h$ is

$$
[Z]_h=\{W\in\overline{\mathcal T}:W\sim_h Z\}.
\tag{NCC.8}
$$

Let $\Omega$ be the infinite tree with a branch at every address. For a
scalar coordinate use

$$
\overline{\mathcal A}=\{T_n:n\in\mathbb N\}\cup\{\Omega\}.
\tag{NCC.9}
$$

The symbol $\infty$ is a label for the last point, not an integer at
which $K$ is evaluated. Thus the completed coordinate space is
$X=\overline{\mathcal A}^{k}\times
\overline{\mathcal T}^{m}$. Embed a finite tuple by
$\operatorname{coord}(\mathbf n,\mathbf z)
=(T_{n_1},\ldots,T_{n_k},z_1,\ldots,z_m)$.

These are ordinary constructor-tree spaces. They are compact and
metrizable: their replies form a closed, locally arity-consistent subset
of the product of four-element sets over the countable addresses.
The root is present, a branch has precisely two present children, and a
leaf or absent node has only absent descendants. These restrictions
are closed and characterize exactly the indicated trees.

The atomic facts of [ABC][ABC] and [NLC, Lemma 3.1][NLC] give
$\mu(T_n)=\lfloor n/2\rfloor$, where $\mu$ is minimum leaf depth, and
injectivity of $n\mapsto T_n$. Consequently

$$
T_n\sim_h\Omega\quad\Longleftrightarrow\quad n\ge2h+2.
\tag{NCC.10}
$$

A bounded rank sequence has a constant subsequence. A sequence of ranks
tending to infinity converges to $\Omega$. These observations also show
that (NCC.9) is closed and compact. A finite tree $f$ is isolated by its
prefix through its maximum leaf depth: every branch and every terminating
leaf is then fixed, so no proper extension or different tree agrees.
This isolation applies also to each finite atomic coordinate.

**Definition 2.2 (exact finite and infinite tags).** Fix a supplied
$\xi=(\overline{\mathbf n},\mathbf Z)\in X$. Let

$$
\begin{aligned}
J&=\{j:\overline n_j=\infty\},&
\overline n_j&=q_j\in\mathbb N\quad(j\notin J),\\
F&=\{i:Z_i\in\mathcal T\},& f_i&=Z_i\quad(i\in F),\\
I&=\{1,\ldots,m\}\setminus F.
\end{aligned}
\tag{NCC.11}
$$

Thus every $Z_i$ with $i\in I$ is genuinely infinite. All finite values
$f_i,q_j$ are supplied exactly. These tags are mathematical hypotheses;
an arbitrary program is not assumed to decide its output's infinitude.
Effective finite witness production additionally requires effective
prefixes of every $Z_i$ for $i\in I$.

Define the finite-residual support and its joint cofinality condition by

$$
\begin{aligned}
S_f(\mathbf n)&\ \Longleftrightarrow\
K(\mathbf n)\land
\exists\mathbf w\in\mathcal T^{I}\quad
\Gamma(\mathbf n,(f_i)_{i\in F},\mathbf w),\\
\operatorname{Cof}(\xi)&\ \Longleftrightarrow\
\forall b\in\mathbb N\ \exists\mathbf n\in\mathbb N^k\quad
S_f(\mathbf n)\land
\bigwedge_{j\notin J} n_j=q_j\land
\bigwedge_{j\in J} n_j\ge b.
\end{aligned}
\tag{NCC.12}
$$

Partial substitution retains every shared occurrence and every listed
negative. By [URR, Corollary 3.2][URR], $S_f$ has an effective exact
Presburger formula: substituting each $f_i$ and evaluating its fixed
iterates leaves precisely the same mixed-template grammar in the
remaining variables. Hence $\operatorname{Cof}(\xi)$ is one Presburger
sentence. If $J$ is empty it is feasibility at the fixed entire rank
vector. If $I$ is empty its existential is over the empty tuple.

## 3. Native prefix substitution creates no new universal equality

**Definition 3.1 (independent nonground contexts).** For each residual
name $z_i$ in a finite set, supply a finite constructor context $C_i$ over
$\alpha,\beta$ with a nonempty finite set $V_i$ of holes. A hole is a
variable leaf. Names at different hole positions are distinct, and the
sets $V_i$ are pairwise disjoint. Repeated occurrences of $z_i$ use the
same $C_i$ with the same holes. Every hole is filled by an arbitrary tree
in $\mathcal T$; the filling carrier is the full
$\mathcal T^{\bigcup_i V_i}$.

**Theorem 3.2 (interpreted prefix-substitution conservativity).** Fix
any finite rank vector and any already substituted finite residual
coordinates. For any two remaining native templates $A,B$, and contexts
as in Definition 3.1,

$$
\begin{aligned}
&\forall\mathbf v\in\mathcal T^{\bigcup_i V_i}\quad
 A((C_i[\mathbf v])_i)=B((C_i[\mathbf v])_i)\\
&\hspace{25mm}\Longleftrightarrow\quad
\forall\mathbf z\in\mathcal T^{\{i\}}\quad A(\mathbf z)=B(\mathbf z).
\end{aligned}
\tag{NCC.13}
$$

The quantifiers share all repeated variable occurrences. Decorations
$\rho^a z_i$ are actual powers of one variable, never independent
variables or free unary constructor terms.

Proof. Use the finite native invariants in [URR, Definition 2.1][URR].
The normal code of [ABC, Theorems 2.2–2.3][ABC] gives constructor mass
$\gamma$, counting its nonprimitive $F$ nodes, with

$$
\begin{aligned}
\gamma(\rho^a u)&=\gamma(u),&\gamma(T_n)&=0,\\
\gamma(\langle u,v\rangle)&\ge\max(\gamma(u),\gamma(v)),\\
\gamma(\langle u,v\rangle)&=1+\gamma(u)+\gamma(v)
&&\text{if either child has positive mass}.
\end{aligned}
\tag{NCC.14}
$$

The native clock of [ARH, Lemma 19.2][ARH] satisfies

$$
\kappa(\alpha)=0,\quad\kappa(\beta)=1,\quad
\kappa(\langle u,v\rangle)=2+\kappa(v),\quad
\kappa(\rho^a u)=\kappa(u)+a.
\tag{NCC.15}
$$

These statements are about finite native values. In particular they
allow native atomic collapse; no free-code constructor assumption is
being applied to native pairing.

Every nonground $C_i$ has arbitrarily large mass among its fillings.
Indeed $c_0=\alpha$, $c_{t+1}=\langle c_t,\alpha\rangle$ has mass $t$.
Fill one private hole of $C_i$ by $c_t$, keeping every other hole fixed.
Moving from that hole to the context root never decreases mass, by
(NCC.14). Thus $\gamma(C_i[\mathbf v])\ge t$. This variation leaves
all other contexts fixed, because their hole sets are disjoint. It also
provides fillings with strictly positive mass.

Distribute every fixed power through explicit pairs, combine successive
powers on a variable, and evaluate every ground occurrence using the
actual leaf laws (NCC.1). Expand fixed ground trees into their finite
$\alpha/\beta$ syntax. Both remaining expressions now have only leaf,
decorated-variable, and explicit-pair roots. We prove that equality on
all context fillings implies equality on all residual assignments, by
induction on the sum of their expanded syntax sizes.

If both sides are residual-free, their values are fixed. Equality on
context fillings is their actual ground equality and therefore holds on
the full residual product. Otherwise the root cases are as follows.

1. Two explicit pair roots decompose by injectivity of the actual native
   ordered constructor. Each corresponding child equality holds on every
   same context filling. Each comparison has smaller total syntax size;
   induction gives both equalities on the full product, and reassembly
   gives the conclusion.
2. Two decorated-variable roots with the same name have equal values
   only when their exponents agree, by (NCC.15). In that case their
   equality holds on every residual assignment. With different names,
   keep the second context fixed and vary a private hole of the first.
   Its mass becomes unbounded while the second's remains fixed, so
   universal equality is impossible.
3. A decorated-variable root $\rho^a z_i$ cannot be universally equal
   to a ground leaf or any residual-free side: its mass is unbounded
   on fillings of $C_i$, and the ground side has fixed finite mass.
4. Compare $\rho^a z_i$ with an explicit pair expression $E$. If $E$
   contains no occurrence of $z_i$, fix every other context and vary
   one private hole of $C_i$. Again its unbounded mass contradicts
   equality with the fixed $E$. If $E$ contains $\rho^b z_i$ at any
   descendant, choose a filling with $\gamma(z_i)>0$. Along the
   explicit constructor path from that occurrence to the root, every
   parent has a positive-mass child. Each such parent adds at least
   one to its mass. Because the root is a pair, the path has at least
   one parent, so $\gamma(E)>\gamma(z_i)=\gamma(\rho^a z_i)$.
   This excludes equality, even with repeated occurrences and other
   variables on that same side.
5. A ground leaf and an explicit pair have different native roots;
   two ground leaves compare by their labels. Reversing the two sides
   in any preceding case gives the identical conclusion.

These cases exhaust the expanded roots. They establish the forward
implication without restricting any residual name to a marker or
imposing independence on its decorations. The reverse implication is
specialization to the context fillings, which are finite native values.
$\square$

**Theorem 3.3 (joint completion within prescribed contexts).** Under
Definition 3.1, for any finite rank vector and substituted finite
residuals, a finite conjunction $\Gamma$ of whole native negatives is
feasible on its full remaining residual product if and only if it is
feasible on the product of those context cylinders.

Proof. Feasibility on the full product makes every forbidden equality
nonuniversal there. Theorem 3.2 makes each equality nonuniversal after
context substitution. Substitution preserves the URR mixed-template
grammar: fixed powers distribute through explicit pairs and act on
fixed leaves or on decorated frontier variables. Apply [URR, Theorem
3.1 and Corollary 3.2][URR] once to the entire substituted list. Its
single finite frontier tuple avoids every listed equality together,
with all repetitions and shared holes intact. Fill each $C_i$ with
that same tuple. Conversely any successful filling is itself an
assignment in the original full residual product.

The completing tuple may depend on the contexts and their depth. It
is not the original chart's fixed section and is not a choice of one
witness for each negative. Empty lists and zero remaining residuals
reduce to their literal truth values. $\square$

## 4. The exact supplied-coordinate closure criterion

**Theorem 4.1 (closure with joint cofinal ranks).** For every complete
chart (NCC.4) and every correctly tagged supplied coordinate point $\xi$
of Definition 2.2,

$$
\xi\in\overline{\operatorname{coord}[\mathcal C]}
\quad\Longleftrightarrow\quad\operatorname{Cof}(\xi).
\tag{NCC.16}
$$

Thus the shapes of the infinite residual coordinates do not enter the
decision after the exact finite coordinates have been retained. For
supplied effective infinite prefixes, a true answer constructs one
finite admitted chart tuple agreeing with $\xi$ through every requested
inclusive coordinate depth. A false answer supplies a finite coordinate
neighborhood disjoint from the chart.

Proof. For necessity, fix $b$. Choose an inclusive depth $d$ at least
the heights of all finite residual values $f_i$, all finite atomic
values $T_{q_j}$, and $b$. A finite admitted tuple whose coordinates
agree with $\xi$ through $d$ exists by closure. Isolation forces
$z_i=f_i$ for every $i\in F$ and $n_j=q_j$ for every $j\notin J$.
For $j\in J$, (NCC.10) forces $n_j\ge2d+2\ge b$.
The other residual values witness $S_f(\mathbf n)$ at this same entire
rank vector. This proves every instance of (NCC.12). No disequality
has been asserted to remain true at the limiting point.

For sufficiency, fix inclusive depth $h$. Choose a witness to
(NCC.12) with $b=2h+2$. All finite scalar coordinates are exactly
$q_j$; all other atomic trees agree with $\Omega$ through $h$ by
(NCC.10). Keep every finite residual exactly $f_i$.
For each infinite $Z_i$, record its concrete replies through $h$ and
put a distinct hole at each reached address of length $h+1$. This
produces a finite constructor context $C_{i,h}$ with its concrete
terminating leaves retained. An infinite finitely branching tree has
nodes at every depth, so its frontier at depth $h+1$ is nonempty.
Give different residual coordinates disjoint hole sets, and reuse one
coordinate's entire context at every occurrence of its name.

Every finite filling of $C_{i,h}$ agrees with $Z_i$ through $h$,
including absence below early leaves. Conversely every finite tree
with this prefix is such a filling, by taking its actual frontier
subtrees. This is the ordinary constructor decomposition also used
in [NSF, Lemma 5.1][NSF] and [NativeDepthPatterns, depthEquiv][DEPTH].
The depth parameter there is $h+1$, since observations here are
inclusive through $h$.

The chosen $\mathbf n$ belongs to $S_f$, so the complete negative
list is feasible on the remaining unrestricted residuals at that
rank vector. Theorem 3.3 gives one finite filling of all the contexts
satisfying that whole list jointly. Together with the exactly frozen
finite residuals and the chosen scalars, this is a tuple in
$\mathcal C$ whose coordinates agree with $\xi$ through $h$.
Every prefix neighborhood is therefore met.

For effectiveness at supplied $h$, use the exact Presburger formula
for $S_f$ to extract the finite rank witness, compute the finitely
many supplied residual prefixes, and apply URR's finite completion
to their entire substituted list. These are finite mathematical
constructions. They assert no executed solver or runtime observation.

If $\operatorname{Cof}$ is false, its Presburger negation has a
witness $b$ such that no rank vector satisfies the displayed joint
conditions. Choose $d$ as in the necessity argument. Any finite
admitted tuple in $[\xi]_d$ would provide just such a vector, so this
neighborhood is disjoint from the chart. With $J=\varnothing$, failure
is fixed-rank infeasibility; the finite isolation depths still suffice.
This proves the stated exclusion as well as the equivalence. $\square$

Joint cofinality retains the whole $K\land\Gamma$ support. Separate
unboundedness of each rank, or separate feasibility of each negative,
cannot replace it. [NLC, Proposition 4.3][NLC] already supplies the
separate-versus-simultaneous growth boundary. There is no bound here on
finite values in other prospective coordinate points.

## 5. Exact original prescribed-pair contact

**Definition 5.1 (continuous source templates).** On the completed
coordinate space interpret each $T_{n_j+c}$ as
$\rho^c(t_j)$, where $t_j$ is the atomic coordinate; in particular
$\rho^c\Omega=\Omega$. Pairing and the actual leaf replacements extend
$\rho$ uniquely to $\overline{\mathcal T}$, as in [NLC, Theorem
11.3][NLC]. Let $\overline\Theta$ be the resulting source expression.
For each finite address its evaluation needs only input replies at
words of length at most that address's length. Explicit constructors
consume address letters, and an interpreted power follows the remaining
word through input constructors before entering a finite leaf image.
Equal early leaves have identical finite images, and equal branches
reduce to corresponding children. Hence
all four replies, including born and absent positions, satisfy

$$
\xi\sim_h\eta\quad\Longrightarrow\quad
\overline\Theta(\xi)\sim_h\overline\Theta(\eta).
\tag{NCC.17}
$$

This is native locality, not normal-code depth. It proves continuity
on the completion, and specializes to [PDC, Theorem 6.2][PDC] on finite
admitted tuples. No value $K(\infty)$ is introduced.

**Theorem 5.2 (two-direction prescribed-pair correspondence).** Fix
any two charts from (NCC.5), with their same prescribed distinct full
finite labels $r_i\ne r_j$. Their original contact assertion (NCC.7)
is equivalent to

$$
\exists\xi\in X_i,\ \eta\in X_j\quad
\operatorname{Cof}_i(\xi)\land\operatorname{Cof}_j(\eta)\land
\overline\Theta_i(\xi)=\overline\Theta_j(\eta).
\tag{NCC.18}
$$

All finite residuals in these conditions are frozen exactly. The
original source directions preserve every condition in (NCC.2) and
every field of both labels. No equality between independent finite
approximants is required when their limiting coordinates coincide.

Proof. Suppose (NCC.7). For each $h$ choose its actual finite admitted
parameter pair. The finite product $X_i\times X_j$ is compact and
metrizable by Definition 2.1. A subsequence with depths tending to
infinity converges to some $(\xi,\eta)$. Each component is in the
closure of its finite chart coordinates, so Theorem 4.1 gives both
cofinality conditions. Continuity gives the two limiting source
images. For any finite depth, sufficiently late members of the
subsequence have agreeing original replies through that depth, and
convergence makes those replies the respective limit replies. Thus
the two source limits agree at every address, proving equality.

Conversely suppose (NCC.18), and fix requested original inclusive
$h$. Theorem 4.1 supplies admitted finite tuples $a_h$ and $b_h$
approximating their own coordinate points through $h$, independently.
Equation (NCC.17) and the common completed source give
$\Theta_i(a_h)\sim_h\Theta_j(b_h)$. Exact finite reconstruction in
(NCC.5) gives membership of both originals in the complete $D$ and
the full rows exactly $r_i,r_j$. This proves (NCC.7).

In the finite full-row-image case, every original opposite-row pair
is represented by the complete chart cover, including pairs that
came from one unlabelled chart before the full-row predicates were
imposed. PDC's finite-list quantifier argument fixes one labelled
chart pair before taking all depths. Neither direction discards any
old record or replaces a stratum by its section.

For clarity, each individual chart also satisfies

$$
\overline{\Theta_i[\mathcal C_i]}
=\overline\Theta_i\bigl[
\overline{\operatorname{coord}[\mathcal C_i]}\bigr].
\tag{NCC.19}
$$

The right side is compact and hence closed, contains the finite image,
and every one of its points is approximated by that image using
continuity. This proves equality. A common point for distinct labels
cannot be a finite source: its isolating original prefix would force
finite approximants from both labels to be that same source.

Compactness in the first direction supplies semantic points only.
It supplies no effective description of them and no finite equality
certificate. $\square$

## 6. Sound consumption of supplied finite recursive data

**Corollary 6.1 (supplied guarded descriptions with proved equality).**
Suppose finite data describe the two points in (NCC.18) by equations
$X_v=E_v(\mathbf X)$ in actual native expressions, with every state
occurrence below at least one pair after fixed powers are distributed.
Coordinate outputs are native expressions in these states, together
with exact finite atomic values or $\Omega$. Supply a finite ordinary
equational derivation of the equality of the two completed source
outputs, using these equations, (NCC.1), and equality congruence.
If the two exact cofinality sentences hold, these data are a sound
finite certificate of original finite contact for the same chart
pair. They construct its original finite counterpair at each requested
depth. This is a sufficient certificate criterion, with no completeness
claim for a description or equality language.

Proof. The standard prefix metric has distance $2^{-d}$ when $d$ is
the first distinguishing depth. Pairing is $1/2$-contracting in the
maximum product metric and actual $\rho$ is nonexpanding by native
locality. The displayed guarded tuple map is therefore contracting
on a complete finite product of $\overline{\mathcal T}$. Its unique
solution and effective prefixes follow from the ordinary contraction
argument: iteration from a finite all-$\alpha$ tuple stabilizes
replies through $h$ after $h+1$ iterations. This is the metric method
in the corrected [Milius–Moss, §7.3, Theorem 7.15 and Remark 7.16][MM];
the native bound has been checked directly rather than postulating
that bare $\rho$ is contracting or invoking an unproved Elgot-algebra
structure. Their Definition 7.1 and Theorem 7.5 have additional
interpreted-solution hypotheses, which are not silently imported.

Finite and infinite tags for these particular finite nullary equations
are also justified directly. Draw an edge to each state occurring in
$E_v$. A state reaching no directed cycle expands along a finite
acyclic graph to an exact finite tree. A state reaching a cycle is
infinite. If it were finite, every occurring descendant would be
finite: $\rho$ preserves every infinite branch, and pairing never
deletes a child. Around a cycle, finite leaf counts would then strictly
decrease along every edge, since each occurrence is below a pair,
$\ell(\rho t)\ge\ell(t)$, and the other child is nonempty. This is
impossible. A coordinate expression containing an infinite state is
infinite by the same nondeletion facts; otherwise its value is finite
and computable. Thus the required tags and finite residual values
are obtained for these supplied data.

Each step of the supplied finite equality derivation is sound in the
unique solution, because the equations and actual native laws hold
there. The two Presburger conditions now admit finite coordinate
witnesses by Theorem 4.1; their original-source correspondence is
Theorem 5.2. Raw finite recursive unfoldings need not satisfy the signs.
They provide the prefixes, after which joint completion supplies the
finite signed realizations. $\square$

The corollary decides the approximation condition for those supplied
points and verifies a supplied finite equality derivation. It does
not decide equality of every two generated trees, prove that every
true equality has such a derivation, or prove that every contact has
these finite descriptions. Rejection of these data is not exclusion
of every other point satisfying (NCC.18).

## 7. A consumed signed realization consequence

**Theorem 7.1 (feasible negative refinements preserve the supplied
nonregular prescribed-pair contact).** Reuse exactly [NLC, Definition
11.1 and Theorems 11.2–11.4][NLC], including the entire original input,
all three strata, and their full labels. Its notation is

$$
G(y)=\langle\alpha,\rho y\rangle,\qquad
U(x,y)=\langle x,\langle y,G(y)\rangle\rangle,\qquad
D=\{U(x,y):x,y\in\mathcal T\}.
\tag{NCC.20}
$$

Add any finite list of acquired negative records whose two endpoints
are uniformly reached on this entire displayed $D$, and whose whole
values there are fixed native expressions in $x,y$. Let their entire
joint negative conjunction be $\Delta(x,y)$. Retain every old record.
If both full one-variable conjunctions

$$
\Delta(y,y),\qquad\Delta(G(y),y)
\tag{NCC.21}
$$

are feasible on $\mathcal T$, then the same prescribed rows $r_0,r_1$
still have finite original contact at every inclusive depth, at the
same common point $L=\langle K,\langle K,K\rangle\rangle$ supplied by
NLC, where $K=G(K)$. This is a finite signed realization consequence;
NLC owns that tree, its nonregularity and its recursive descriptions.

Proof. The entire refined fiber is exactly

$$
D^\Delta=\{U(x,y):x,y\in\mathcal T,\ \Delta(x,y)\}.
\tag{NCC.22}
$$

NLC supplies both directions for the original $D$. Uniform guards and
the stated endpoint identities make the new records exactly $\Delta$
on those same sources, proving both directions of (NCC.22).
NLC also supplies $y\ne G(y)$ for every finite $y$, by
$\ell(G(y))=1+\ell(y)+\#\beta(y)>\ell(y)$. Thus the entire refined
$r_0$ stratum is $\{U(y,y):\Delta(y,y)\}$, the entire refined $r_1$
stratum is $\{U(G(y),y):\Delta(G(y),y)\}$, and the entire third stratum
retains $x\ne y$, $x\ne G(y)$ and $\Delta(x,y)$. The common reached set
and numbered exterior at $Q=(L,RL,RR)$ remain unchanged.

Each selected one-variable domain is a complete negative chart with
no scalar coordinates. Include its whole row negative $y\ne G(y)$;
this changes no finite membership. Feasibility in (NCC.21) is exactly
its fixed-rank cofinality condition. Its proposed residual limit is
the infinite $K$, so Theorem 4.1 gives independent finite $y_h^0,y_h^1$
matching $K$ through $h$ and satisfying each entire conjunction.
The exact source maps are $\Theta_0(y)=U(y,y)$ and
$\Theta_1(y)=U(G(y),y)$. Their completed outputs coincide at $K$ by
NLC's supplied identity. Theorem 5.2, or directly native locality,
therefore gives finite originals in the same two full strata agreeing
through $h$ with $L$.

No equality $y_h^0=y_h^1$ is imposed. Different negative lists can
require different finite replacements even though their limit is the
same. The finite row negative $y\ne G(y)$ becomes equality at $K$;
its finite validity comes from reconstruction and joint completion.
Additional literals or nonuniform endpoint guards are not covered
by this shortcut; their complete predicates must first be discharged
by the exact PDC producer. $\square$

**Corollary 7.2 (an actual nonredundant acquired negative refinement).**
In the entire NLC input (NLC.32), add the two signed records

$$
(0,RL,0,RRL,\ne),\qquad(0,RL,1,RRL,\ne).
\tag{NCC.23}
$$

Keep its original positive mixed-epoch record and every literal, with
an authentic common handoff $N\ge1$. The entire refined fiber is
$\{U(x,y):x,y\in\mathcal T,\ y\ne\alpha,\ y\ne\beta\}$ and retains
the same $r_0/r_1$ contact at every depth.

Proof. On every $U(x,y)$ the original subtrees at $RL,RRL$ are
$y,\alpha$, and the epoch-one subtree at $RRL$ is $\beta$. All three
endpoints are reached. Hence the two records are exactly the stated
joint restrictions on $y$. They remove finite sources from the original
fiber, including those with $y=\alpha$ or $y=\beta$. Both substitutions
in (NCC.21) are feasible, witnessed by $y=\langle\alpha,\alpha\rangle$.
Apply Theorem 7.1. The full third stratum is retained as well: for this
same $y$, $x=\alpha$ differs from both $y$ and $G(y)$ and attains it.
The two prescribed rows keep every finite cross-class inequality,
including the one that disappears at the common limit. $\square$

## 8. Source-matched boundaries and the remaining obligation

**Theorem 8.1 (productive source approximation can miss both prescribed
finite labels).** There is a nonempty original acquired signed fiber
with finite full-row image, two attained prescribed distinct labels,
and a finite productive common-positive description with actual finite
approximants in the entire fiber, but with no prescribed-pair contact
through inclusive depth three.

Proof. Take the old cut $P=\{\varepsilon\}$ with its complete one-hole
row. Retain exactly

$$
\begin{aligned}
H_0={}&\{(0,\varepsilon,\mathsf{branch}),(0,L,\mathsf{branch}),
(0,LL,\alpha),(0,LR,\mathsf{branch})\},\\
H_{\rm rel}={}&\{(0,R,0,LL,\ne)\}.
\end{aligned}
\tag{NCC.24}
$$

Writing $V(y,z,t)=\langle\langle\alpha,\langle y,z\rangle\rangle,t\rangle$,
the entire source fiber is

$$
D_* =\{V(y,z,t):y,z,t\in\mathcal T,\ t\ne\alpha\}.
\tag{NCC.25}
$$

The literals force this unique constructor decomposition; the two
signed endpoints are precisely the reached subtrees $t,\alpha$.
Conversely every displayed source has the full old root row and all
these records. Original subtrees at $LRL,LRR,R$ recover $y,z,t$.
Authentic acquisition is subject to the common complete-state contract
of Assumption 1.2, rather than an extra observer operation.

Use $Q=(LL,LRL,LRR,R)$. Every source reaches all four positions and
has the full numbered exterior
$\langle\langle\square_1,\langle\square_2,\square_3\rangle\rangle,
\square_4\rangle$, with hole values $(\alpha,y,z,t)$. Its row image
is finite, since there are finitely many partitions of four holes.
Prescribe $r_0$ with partition $\{\{1,2\},\{3\},\{4\}\}$ and
$r_1$ with partition $\{\{1,3\},\{2\},\{4\}\}$. Their entire strata
have injective complete negative charts

$$
\begin{aligned}
\Theta_0(z,t)&=V(\alpha,z,t),&
\Gamma_0&=(z\ne\alpha)\land(t\ne\alpha)\land(t\ne z),\\
\Theta_1(y,t)&=V(y,\alpha,t),&
\Gamma_1&=(y\ne\alpha)\land(t\ne\alpha)\land(t\ne y).
\end{aligned}
\tag{NCC.26}
$$

Both carriers are the full $\mathcal T^2$ and $K$ is true. All
cross-class inequalities are included. With $c=\langle\alpha,\alpha\rangle$,
$V(\alpha,\beta,c)$ attains $r_0$ and $V(\beta,\alpha,c)$ attains $r_1$.
These two sources agree through depth two.

The point $M=V(\alpha,\alpha,\Omega)$ has the finite productive
description $O=\langle O,O\rangle$, substituted for $\Omega$. It
satisfies the acquired literal skeleton and the guarded acquired
negative $\Omega\ne\alpha$, as well as the positive equations of
both prescribed partitions. Put $t_0=\beta$,
$t_{n+1}=\langle t_n,t_n\rangle$. Its leaves all have depth $n$, so
$V(\alpha,\alpha,t_n)$ is an actual finite source in $D_*$ approaching
$M$. Its full finite label is instead
$\{\{1,2,3\},\{4\}\}$.

Every $r_0$ source replies $\alpha$ at original $LRL$. Every $r_1$
source has $y\ne\alpha$ there and replies either $\beta$ or branch.
Thus depth three excludes the prescribed pair globally; the attaining
pair above shows that this depth is sharp. In (NCC.26), the putative
coordinate points are respectively $(\alpha,\Omega)$ for $(z,t)$
and $(\alpha,\Omega)$ for $(y,t)$. Freezing the finite first coordinate
makes each complete negative conjunction false. Their cofinality
conditions therefore fail, despite productivity and source-valid
approximation of $M$ in the entire fiber.

This refutes acceptance using only limiting positive equations and
source-valid approximants. It does not exclude contact between other
row pairs in $D_*$, nor does it refute stronger finite descriptions.
$\square$

**Theorem 8.2 (private holes and finite freezing are essential).**
Neither identifying frontier holes of independent coordinates nor
allowing a supplied finite residual to vary preserves Theorem 4.1.
A leftover positive residual condition is likewise outside its scope.

Proof. With two unrestricted residuals and the whole negative
$z_1\ne z_2$, the point $(\Omega,\Omega)$ is in coordinate closure:
use the perfect depth-$(h+1)$ trees with all leaves respectively
$\alpha$ and $\beta$. They are distinct and both agree with $\Omega$
through $h$. If their two root contexts are assigned the same hole
variables at corresponding frontiers, every such common filling has
$z_1=z_2$ and violates the negative. Equal limiting coordinates did
not justify that finite identification.

For the chart $\{z:z\ne\alpha\}$, the supplied finite point $\alpha$
is not in closure: its depth-zero neighborhood is the singleton
$\{\alpha\}$. Feasibility on a freely varying residual would wrongly
accept it. Exact substitution of its finite value makes $S_f$ false,
as Theorem 4.1 requires. Conversely, the infinite point $\Omega$ is
in that chart's closure although a fixed finite completion tuple cannot
agree with it beyond that tuple's leaf depth.

Finally, the domain $\{z:z=\alpha\}$ has feasible empty negatives but
has no $\Omega$ closure point. The omitted positive equation prevents
application of Theorem 3.3. Exact PDC elimination would remove this
free residual and reconstruct the fixed tree, rather than leave its
positive condition unlisted. $\square$

**Open problem 8.3 (unrestricted equality and stopping remain).** For
arbitrary (NCC.2), the original deciding-prefix goal (NCC.6) remains
unresolved here. In the finite full-row-image case, Theorem 5.2 replaces
each prescribed-pair contact by (NCC.18) with exact finite-realization
conditions. Deciding that existential still requires a complete
effective method for equal completed chart outputs, or a complete
finite description and equality-proof language for every such contact.
The finite coordinate values and ranks in prospective points are not
bounded by the supplied-point decision. Compactness gives no effective
certificate synthesizer. Fixed-depth decisions, successive depth
searches, successful supplied-point tests and sound supplied recursive
certificates each retain their separate scope.

All constructions here are offline ordinary mathematics. They add no
observer equality port, inverse update, reset, source or chart selector,
hidden control memory or free paid-operation receipt. A resulting finite
original pair obstructs (NCC.6) at its requested depth; any further
actual-service consequence retains the authentic acquisition, common
complete state and paid operation hypotheses of ARH. No infinite tree
is an original source or register.

## 9. Exact suppliers and literature correspondence

**References 9.1 (ownership and mathematical status).** The new
repo-derived content is Theorems 3.2–4.1 and their completed-chart
consumer in Theorem 5.2, the supplied-data signed realization in §6,
the negative-refinement consequence in §7, and the source boundaries
in §8. These are ordinary deductions from the listed suppliers.
Elementary prefix avoidance is already owned by [RNL, §§3 and 5][RNL]
for one uniform outer power on each side. Its finite-forbidden argument
expressly excludes internally mixed powers. Theorem 3.2 instead proves
universal-identity reflection under nonground prefix substitution for
mixed powers, and Theorem 4.1 combines it with entire-chart scalar
support. No literature priority claim is made.

| Supplier | Exact mathematical use and retained boundary |
| --- | --- |
| [PDC, Theorem 5.2, Theorem 6.2 and §§7–8][PDC] | Complete arbitrary-signed all-source charts, actual original-prefix locality, all within/cross-chart pairs, and fixed full-label formulation; the completion section is not the domain. This is a pinned ordinary paper supplier. |
| [URR, Definition 2.1, Theorem 3.1, Corollary 3.2 and Proposition 7.1][URR] | Native mass and clock, one simultaneous completion and exact scalar Presburger support; no residual-positive or guard restriction may remain unlisted. |
| [ABC, Theorems 2.2–2.3][ABC] and [ARH, Lemma 19.2][ARH] | Native normal coding, atomic injectivity, mass preservation, clock and original-prefix locality; no free unary interpretation of $\rho$. |
| [NSF, Lemma 5.1 and Theorems 5.2–6.1][NSF] | Both guards, complete-row compilation and supplied-depth finite queries; these already own finite feasibility, not the unrestricted outer stopping claim. |
| [NPL, Theorem 5.3][NPL] | Exact finite full-row image and attainment, with full exterior and partition. |
| [NLC, Lemma 3.1 and §§11–12][NLC] | Atomic depth, continuous native extension, the exact shifted fiber, its prescribed nonregular point and already-owned parameter recursion; §7 adds feasible negative refinements rather than another comb proof. |
| [NativeDepthPatterns, depthEquiv and original_prefix_locality][DEPTH] | Exact finite constructor/frontier decomposition and native locality, including private fill_decompose/decompose_fill; no completed-chart closure theorem is imported from those declarations. |
| [NativeGroundSeparation][NGS] | Its private compound_mass_ne and bounded_eval_injective clarify finite equal-mass separation; the mixed-power invariants and common completion used here are the URR paper supplier. |
| [RNL, Lemma 3.1, Corollary 3.2 and Proposition 5.2][RNL] | Elementary deep finite replacement with uniform outer powers; that restricted decision is not reauthored or extended into arbitrary-signed stopping here. |

**References 9.2 (primary literature and transfer limits).** The
following background is literature-attested; it is used inside the
new native deductions at the explicitly matched hypotheses.

| Primary source | Correspondence and boundary |
| --- | --- |
| [Comon–Lescanne, *Equational Problems and Disunification*, §2.1, §3.2 Proposition 2/Lemma 1, Appendix B.3 and §6.2][CL] | Their finite ranked constructor constants and binary function correspond to $\alpha,\beta$ and ordered pairing; their rational-tree and simultaneous syntactic disequation results distinguish finite and rational algebras. Appendix B.3 uses the finite one-variable exception property, and §6.2 withholds a general equational-theory transfer. Native $\rho^2z=\langle\rho z,z\rangle$ has all $T_n$ as finite solutions, so their finite-exception argument is not the proof of Theorem 3.2. |
| [Milius–Moss, corrected version 0904.2385v2, Definition 6.1, Theorem 6.5, Definition 7.1, Theorems 7.5 and 7.15, Remark 7.16][MM] | Guarded schemes have uninterpreted solutions under their functor hypotheses; interpreted solutions require an Elgot algebra, with uniqueness under complete iterativity and the corrected compatibility condition. Their metric discussion supplies the standard guarded contraction method. Here pairing contracts and actual $\rho$ is only nonexpanding. This supports supplied recursion semantics, not signed finite approximability, finite-label preservation or description completeness. |
| [Marshall–Meadows–Narendran, *On Unification Modulo One-Sided Distributivity*, §5 and Lemma 5.6][OD] | Their typed single homomorphism distributes over a binary operation. Their cycle rejection relies on a subterm-collapse-free theory without the native leaf laws. The native finite solution $\beta$ of $\rho(x)=\langle x,\alpha\rangle$ excludes a direct transfer of that cycle test. |
| [Godoy–Giménez–Ramos–Álvarez, *The HOM problem is decidable*, §§2.1–2.2][HOM] | Native $\rho$ is exactly a ranked-tree homomorphism with images $\alpha\mapsto\beta$, $\beta\mapsto\langle\beta,\alpha\rangle$, and pairing mapped to pairing of its argument images. Their problem concerns regularity of the image of a supplied regular finite-tree language; their path disequality also accepts missing endpoints. Original signed records require both reached guards, and no such regular-language or all-depth-contact encoding is supplied here. |
| [Reuß, *Normalization of Horn Clauses with Disequality Constraints*, §3.2.4, Theorem 18 and Corollary 17, pp. 59–60][REUSS] | A finite automata-clause system with the specified disequalities admits a finite list eliminating one existential variable uniformly in the others. No correspondence from arbitrary interpreted native chart contact to that clause class is proved here; a finite witness list for a fixed query does not by itself meet every changing prefix. |

These precise background results do not settle Open problem 8.3.
The native chart-closure proof, its whole signed reconstruction, and
its two-direction consumer are supplied in this volume. No kernel,
solver, physical, general complexity, undecidability or programme
completion statement accompanies them.

[PDC]: https://github.com/the-omega-institute/trureturing/blob/5f6e4c682e3e92206e00b81be891b30e35a25f1b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_POSITIVE_DOMAIN_CORRESPONDENCE.md
[NLC]: https://github.com/the-omega-institute/trureturing/blob/a5680221ab72e9a913651087bc74d21de1109933/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[RNL]: https://github.com/the-omega-institute/trureturing/blob/cfb2de434586535803959c1671a08e207f78b655/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NEGATIVE_HISTORY_LIMITEDNESS.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[NGS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[MM]: https://arxiv.org/abs/0904.2385v2
[OD]: https://arxiv.org/abs/1503.06687v2
[HOM]: https://www.cs.upc.edu/~ggodoy/papers/homproblem2.pdf
[REUSS]: https://mediatum.ub.tum.de/doc/1116533/document.pdf

## 追加锚（本行以下为增补区）

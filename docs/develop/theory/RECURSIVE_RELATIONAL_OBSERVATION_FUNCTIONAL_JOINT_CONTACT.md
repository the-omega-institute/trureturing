# Functional joint contact for complete acquired native rows

> This generic-v1 volume is mathematical reference input. It gives ordinary
> proofs, without a claim of Lean-kernel verification. Integrated definitions
> and proofs are retained; additions and corrections follow the append anchor.

## 1. The entire source and the joint question

**Definition 1.1 (native sources and original prefixes).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle s,t\rangle&=\langle\rho s,\rho t\rangle,\\
T_j&=\rho^j\alpha\qquad(j\in\mathbb N).
\end{aligned}
\tag{FJC.1}
$$

Every source is nonempty, finite, free and ordered as a binary tree.
Repeated occurrences are retained. There is no common bound on size,
depth or atomic rank. The operation $\rho$ is interpreted by (FJC.1).
An original address is a finite word in $\{L,R\}$, with root
$\varepsilon$. The four-valued reply $r_u(p)$ is $\alpha$, $\beta$,
$\mathsf{branch}$ or $\mathsf{absent}$. Strict descendants of a leaf
are absent. Put

$$
u\equiv_h v\quad\Longleftrightarrow\quad
\forall |p|\le h\quad r_u(p)=r_v(p).
\tag{FJC.2}
$$

Depth is inclusive. For a finite prefix-free original cut $A$, the full
row $R_A(u)$ comprises the reached set $A\cap\operatorname{Pos}(u)$,
in address order, its entire concrete exterior with precisely those
subtrees replaced by numbered holes, and the complete partition of those
holes by equality of their entire ordered subtrees. An absent cut
address contributes no hole. Empty cuts and the root cut are allowed.

**Definition 1.2 (complete acquired predicate).** Fix the input
$I=(P,R,H_0,H_{\rm rel},Q,N)$ of [ARH, Definitions 1.1–1.2][ARH].
Both cuts are finite and prefix-free. The attained old row $R$ includes
its full exterior, reached set and partition. A literal $(a,p,c)$ means
$r_{\rho^a u}(p)=c$. A signed record $(a,p,b,q,\bowtie)$ means

$$
p\in\operatorname{Pos}(\rho^a u),\qquad
q\in\operatorname{Pos}(\rho^b u),\qquad
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q,
\quad\bowtie\in\{=,\ne\}.
\tag{FJC.3}
$$

The lists retain repetitions. An absent endpoint invalidates either
sign. All records within one realization concern its same original
source. Define the entire fiber and its full-row strata by

$$
\begin{aligned}
D&=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\},\\
D_r&=\{u\in D:R_Q(u)=r\}.
\end{aligned}
\tag{FJC.4}
$$

Thus all different old classes remain unequal, every repeated class
remains shared, and off-task constraints remain imposed. The new target
is the entire original $Q$-row.

**Assumption 1.3 (common actual producer and service).** Retain exactly
[ARH, Assumption 1.3 and Proposition 2.1][ARH]. One public source-total
paid acquisition procedure obtains the old row, literals and signed
whole-subtree comparisons on the same register, then reaches the
certified epoch $N$, at least every record epoch. Conditional on the
stipulated complete access cut, its entire accessible retained state has
exactly fiber $D$. Every $u\in D$ produces that same state, and every
source producing that state belongs to $D$.

All accessible source-dependent caches, lengths, addresses, traversal
counts, control, permissions, timing and handles are included in that
premise. The cut is an access assumption, not a physical-erasure theorem.
The original source and root persist. Subsequent operations are paid
four-valued $\mathsf{Read}(p)$ and legal serial forward
$\mathsf{ApplyRho}$. No source-selection, equality, original-version,
reset, reroot, clone or clock port is supplied. Local computation uses
common data and acquired replies. Acquisition, literal words, updates,
local work, memory, retention, preparation and installation have separate
charges. A sourcewise finite acquisition need not have a uniform bound.

**Definition 1.4 (joint finite prefix).** Let $B$ be any supplied finite
set of distinct attained full row labels, $|B|\ge2$. Set

$$
J_B(h)\quad\Longleftrightarrow\quad
\exists (u_r)_{r\in B}\in\prod_{r\in B}D_r\quad
\forall r,s\in B\quad u_r\equiv_h u_s.
\tag{FJC.5}
$$

Each witness is an actual finite native source satisfying the entire
input. The witnesses can change with $h$. They are alternative originals
for the common producer contract, not one source carrying incompatible
labels. Pairwise witnesses chosen separately need not form this tuple.
Rows outside $B$ remain in $D$.

## 2. The input class and its lawful certificates

**Definition 2.1 (rank-free negative charts).** A rank-free expression
has finite syntax

$$
A::=g\mid\rho^a z_i\mid\langle A,A\rangle,
\qquad g\in\mathcal T,quad a\in\mathbb N.
\tag{FJC.6}
$$

All constants and exponents are supplied finite data. A repeated name
uses the same value. For each supplied $r\in B$, give finitely many
charts $(\Theta_{r,c},\Delta_{r,c})$, with
$\mathbf z\in\mathcal T^{m_{r,c}}$, such that

$$
D_r=\bigcup_c
 \{\Theta_{r,c}(\mathbf z):\Delta_{r,c}(\mathbf z)\},
\qquad
\Delta_{r,c}=\bigwedge_\ell A_{r,c,\ell}\ne A'_{r,c,\ell}.
\tag{FJC.7}
$$

Each comparison is a whole-tree negative. The carrier before imposing
$\Delta$ is the full Cartesian product; zero coordinates and empty
conjunctions are allowed. There are no variable-rank coordinates,
residual positive equations, navigation filters, image restrictions or
normality predicates left in a chart.

Equation (FJC.7) requires both source directions. Every chart point
satisfies the original exterior, reached sets, both complete partitions,
every literal, every sign and both endpoint guards, and exactly row $r$.
Every $u\in D_r$ is reconstructed as that same source by at least one
chart. It is insufficient to cover merely selected partition bits or to
supply arbitrary finite feasibility witnesses.

**Definition 2.2 (checkable source certificate).** Exactness in
Definition 2.1 is accompanied by a finite derivation with distinguished
free source $u$, from the predicate $u\in D_r$ to

$$
\bigvee_c\exists\mathbf z\quad
u=\Theta_{r,c}(\mathbf z)\ \land\ \Delta_{r,c}(\mathbf z).
\tag{FJC.8}
$$

The following are lawful certificate steps, with their stated domains.
Finite Boolean rearrangements, renaming and existential distribution use
ordinary first-order logic with syntactically checked freshness.
A fresh definition $x=A$ can be introduced; a variable defined by an
expression not containing it can be eliminated by substitution, with
its reconstruction retained. Native powers distribute through pairs,
compose by addition, and act on supplied grounds by (FJC.1). Native
pair cancellation is valid; cancellation of equal fixed powers uses
finite-native injectivity from [ARH, Lemma 19.2][ARH].

Fixed navigation, guards and rows may first be expanded into the exact
finite original-prefix cases of [NSF, Lemma 5.1][NSF]. The case inverse
uses the actual reached frontier subtrees. Masks retain every uncut
subtree, and row comparisons retain every partition bit. A
quantifier-free conjunct may be removed under the remaining
quantifier-free conditions only when the counterquery is empty by
[NSF, Theorems 4.3 and 5.2][NSF]. This is a terminating native finite
query, including complements of guards after reach is evaluated.

Each rule preserves the predicate for each fixed $u$; definitions and
prefix cases preserve the same source with explicit witnesses.
The finite sequence and its side conditions are effectively checkable.
No rule licenses forgetting a guard or substituting a bound on source
size. The direct correspondences proved in §6 give such certificates:
constructor decomposition, positive substitution, and removal of
universally redundant negative conjuncts are their steps.

[NIC, Theorems 3.2–3.3 and 4.3][NIC] provides general exact mixed
covers with natural-rank coordinates. Such a cover is usable here only
when its elimination into (FJC.8) is actually justified. Its existence
does not justify dropping those coordinates.

**Definition 2.3 (completed common-output presentation).** Let
$\widehat{\mathcal T}$ be the space of finite or infinite ordered full
binary trees with $\alpha/\beta$ leaves. It has the same four replies.
The tree $\Omega$ has a branch at every address. Extend $\rho$ by its
actual leaf replacements and pair law, so $\rho\Omega=\Omega$.

For every choice $\mathbf c=(c_r)_{r\in B}$ of one chart per row,
use independent coordinate names for different charts and form

$$
\mathscr E_{\mathbf c}(\mathbf z):\quad
\Theta_{r,c_r}(\mathbf z_r)
 =\Theta_{s,c_s}(\mathbf z_s)\quad(r,s\in B).
\tag{FJC.9}
$$

Negatives are not imposed on completion points. Supply a finite lawful
completed-equation derivation to either a clash, or a finite system

$$
\mathscr G:\quad X_i=E_i(\mathbf X)\qquad(i\in A),
\tag{FJC.10}
$$

with at most one definition for each state. States outside $A$ are free.
The right sides have grammar (FJC.6), with states replacing coordinates.
Every original coordinate is a specified state of $\mathscr G$;
identifications are permitted. A coordinate projection $\pi$ and the
retained definitions establish exactly

$$
\{\mathbf z\in\widehat{\mathcal T}^{\sum m_{r,c_r}}:
                  \mathscr E_{\mathbf c}(\mathbf z)\}
 =\pi\{\mathbf X\in\widehat{\mathcal T}^{s}:\mathscr G(\mathbf X)\}.
\tag{FJC.11}
$$

A clash certificate proves the left side empty. The projection preserves
the designated original coordinates; its reverse extension need not be
unique. Auxiliary states have no physical meaning.

**Definition 2.4 (lawful completed reductions and class).** The allowed
steps for (FJC.11) are Boolean and equation rearrangement, finite ground
evaluation, native distribution and composition of fixed powers,
ordered-pair cancellation, fresh definitions and nonrecursive variable
substitution with retained extension/projection maps. Leaf-label and
leaf/pair clashes are valid. All are identities or equivalences on
$\widehat{\mathcal T}$. No finite occurs-check is allowed, and a failure
to reduce is never called a clash. Additional reduction rules require a
proved completed-domain equivalence and effectively checkable side
conditions; they are not assumed by the class.

A functional rank-free input is the entire native input, a finite $B$,
and certificates of Definitions 2.1–2.4 for every chart tuple. These
certificates describe finite source strata and equation presentations,
not a supplied completed solution. Theorems below apply to every such
input and every finite supplied $B$ satisfying these premises. Membership
of arbitrary uncatalogued native input in this class is not asserted.

## 3. Solving the functional equations and finding forced finite values

**Theorem 3.1 (canonical solution and finite-coordinate rigidity).**
Every finite system (FJC.10) has a computably presented canonical
solution $\mathbf K$ in $\widehat{\mathcal T}$. One can compute

$$
F=\{i:K_i\in\mathcal T\}
\tag{FJC.12}
$$

and the exact finite values $K_i$ for $i\in F$. Every completed solution
of $\mathscr G$ has those same values on $F$. Every other canonical
coordinate is infinite and has effectively computable prefixes.
Free states, finite grounds, root-shift chains, zero-shift cycles,
positive-shift cycles and pair-guarded cycles are all included.

**Proof.** First establish the completion interfaces used in the
construction. The reply functions form a closed subset of the product
of four-element sets over countably many addresses: the root is present;
a branch has two present children; leaves and absent nodes have absent
descendants. The complement of each condition is witnessed at finitely
many addresses. This closed space is compact. It is complete for the
prefix metric $d(S,T)=2^{-\delta(S,T)}$ for distinct trees, where
$\delta$ is their first differing depth, and $d(S,S)=0$.
Every prefix can be filled finitely, and a finite tree is isolated by
its prefix through maximum leaf depth.

For a request in $\rho^a S$, follow its original address in $S$.
Original pairs persist. If a first original leaf is encountered, the
remaining reply is computed in its finite $\rho^a$-expansion. If no
leaf is encountered, the reached reply is branch. This includes born
positions and absent descendants. It proves prefix nonexpansion and
continuity of $\rho^a$ on the completion, extending the finite argument
of [ARH, Lemma 19.2][ARH] and
[NativeDepthPatterns.original_prefix_locality][DEPTH]. Pairing adds
one level of prefix agreement. Finite expressions are continuous and
nonexpanding in the maximum product prefix metric.

Normalize each right side by distributing fixed powers through explicit
pairs and evaluating finite grounds. Its root is now ground, an
explicit pair, or $\rho^aX_j$. Call the last form a root link and attach
weight $a\ge0$. The finite directed root-link graph has outdegree at
most one. A path reaches a free state, a ground or pair definition, or
a root-link cycle. Following a path accumulates its fixed weights;
all paths and cycles are found by finite graph traversal.

On a root-link cycle with total weight zero, every weight is zero.
All cycle states are equal, and their common value is unrestricted.
Replace the cycle by one free state and retain the equality maps.
On a cycle with total weight $a>0$, a state satisfies $Z=\rho^a Z$.
If $Z$ had any leaf, its minimum leaf depth $\mu(Z)$ would be finite.
Each leaf under $\rho^2$ becomes a tree with minimum leaf depth at
least one: $\rho^2\alpha=\langle\beta,\alpha\rangle$ and
$\rho^2\beta=\langle\langle\beta,\alpha\rangle,\beta\rangle$.
Hence $\mu(\rho^{2ak}Z)\ge\mu(Z)+ak$ for every $k$.
Iterating $Z=\rho^a Z$ contradicts this inequality. Thus $Z$ has no
leaf. The only full binary tree without leaves is $\Omega$.
Conversely $\rho^a\Omega=\Omega$, so the cycle and all root-link
predecessors entering it have exactly that solution. This is an
interpreted-$\rho$ argument, not unification with a free unary symbol.

Substitute every root-link path ending at a ground, pair or free state,
with its accumulated exponent. Distribute its exponent at a pair.
Keep the pair-defined states as the remaining unknowns. Their defining
equations now have every state occurrence below an explicit pair.
A reference to a removed root-link state substitutes its retained
finite expression; a reference to a positive cycle substitutes
$\Omega$. There are finitely many substitutions. Dependencies through
pairs are not unfolded indefinitely. Reconstruction of every removed
state is a ground, $\Omega$, or a fixed expression in the remaining
states and free parameters. These operations preserve both solution
directions: a solution restricts to the normalized equations, and their
solution reconstructs every original equation along its root-link path.

Assign arbitrary completed values to the free parameters. For the
remaining pair-defined states let $T$ be simultaneous evaluation of
their right sides. If two assignments agree through depth $h-1$, their
images agree through $h$; for $h=0$, the explicit pair roots agree
without an assumption. Consequently iteration from any initial values
stabilizes the prefix through $h$ after $h+1$ iterations. More precisely,
any two $n$-fold iterates agree through $n-1$, and successive iterates
have that same agreement. Completeness of the metric gives a limit.
Continuity makes it a fixed point. Iterating the same estimate on two
fixed points proves equality at every depth, hence uniqueness for those
free values. This is the direct native version of guarded metric
recursion; the general background is [Milius–Moss, §7.3][MM]. Bare
$\rho$ was used only as a nonexpanding map.

Set every free parameter to $\Omega$. This defines $\mathbf K$ and a
finite description by grounds, $\Omega$, and pair-guarded equations,
followed by the reconstruction expressions. Its prefixes are effective:
compute the necessary finite number of simultaneous iterations and
finite expression prefixes, querying $\Omega$ as all-branch.

It remains to classify finite coordinates without inspecting an
infinite output. Draw an occurrence edge from each remaining defined
state to each state or free parameter in its right side. Mark free
parameters and explicit $\Omega$ dependencies as infinite terminals.
A defined state whose reachable graph is acyclic and contains no such
terminal evaluates to a finite tree, by evaluation in reverse
topological order. Its value depends only on supplied grounds, so is
the same in every solution.

Every other state reaches an infinite terminal or a directed cycle.
Pairing and fixed $\rho$ powers do not delete an infinite branch, so
an infinite terminal makes all its predecessors infinite in
$\mathbf K$. A pair-guarded dependency cycle cannot have finite values
on all its states: for finite native leaf count $\ell$, induction on
(FJC.1) gives $\ell(\rho^a t)\ge\ell(t)$, and an occurrence below
at least one pair has a nonempty sibling. Each cycle edge would give
$\ell(X_i)>\ell(X_j)$. Following the cycle is impossible. If one cycle
state were finite, its dependent subexpressions would all be finite,
so the whole cycle would be finite, the same contradiction. Thus all
cycle states and their predecessors are infinite.

A reconstruction expression is finite exactly when all its occurring
canonical states are finite and it has no $\Omega$ occurrence; its
value is then computed finitely and is forced in every solution.
An occurring infinite state remains infinite under powers and pairing.
This classifies all original coordinates and proves (FJC.12).
A canonical infinite coordinate that depends on a free state can be
finite in another solution. The theorem claims rigidity only on $F$;
it does not confuse canonical infinitude with forced infinitude.
$\square$

## 4. The signed finite-realization bridge

**Definition 4.1 (canonical chart test).** For a nonclash chart tuple,
construct $\mathbf K$ by Theorem 3.1. For each chart coordinate $z_i$
whose designated canonical state is finite, substitute its exact value
$f_i$. Leave every other coordinate as an unrestricted finite native
variable. Test the entire remaining conjunction $\Delta_{r,c_r}$.
This is terminating by [URR, Theorem 3.1 and Corollary 3.2][URR], with
no rank coordinates, or by [NSF, Theorem 4.3][NSF]. A tuple passes if
all its chart tests are feasible. A clash tuple fails.

**Theorem 4.2 (complete canonical test for one chart tuple).** Fix
charts $c_r$, one for every $r\in B$. They have actual finite
representatives with a common original prefix at arbitrarily large
depths if and only if their canonical chart tuple passes. In the passing
case, effective finite representatives are produced for every requested
$h$, satisfying all chart negatives together within each source and
exactly the original full row labels. They need not satisfy the
completed cross-source equations as finite equalities.

**Proof.** We give the prefix-preserving negative argument explicitly.
Its prefix-substitution part overlaps [NCC, Theorems 3.2–3.3][NCC];
here it is derived from the accepted finite mass and clock suppliers
rather than assumed through that manuscript.

The normal atomic code in [ABC, Theorems 2.2–2.3][ABC] assigns a mass
$\gamma(t)$ counting its nonprimitive constructor nodes. As recorded
in [URR, Definition 2.1][URR], on finite native values

$$
\begin{aligned}
\gamma(\rho^a t)&=\gamma(t),\\
\gamma(\langle s,t\rangle)&\ge\max(\gamma(s),\gamma(t)),\\
\gamma(\langle s,t\rangle)&=1+\gamma(s)+\gamma(t)
       &&\text{if either child has positive mass}.
\end{aligned}
\tag{FJC.13}
$$

The exceptional atomic pairing can have mass zero; we do not treat its
normal code as an unconditionally free constructor. The native clock
from [ARH, Lemma 19.2][ARH] is

$$
\kappa(\alpha)=0,\quad\kappa(\beta)=1,\quad
\kappa(\langle s,t\rangle)=2+\kappa(t),\quad
\kappa(\rho^a t)=\kappa(t)+a.
\tag{FJC.14}
$$

For each remaining coordinate $z_i$, take any finite constructor context
$C_i$ with a nonempty frontier. Use distinct private names at its hole
occurrences, disjoint from other coordinates; repeated occurrences of
$z_i$ reuse the whole same context and its names. Its finite fillings
have arbitrarily large mass: the comb $c_0=\alpha$,
$c_{n+1}=\langle c_n,\alpha\rangle$ has mass $n$, by (FJC.13).
Filling one private hole by $c_n$ makes the context mass at least $n$
and leaves other contexts fixed.

We claim that universal equality of two expressions on these context
fillings implies universal equality on the unrestricted remaining
coordinate product. Normalize fixed powers, evaluate grounds and
expand their finite leaf/pair syntax. Induct on the sum of expression
sizes. Two pair roots cancel to their corresponding smaller children.
Two decorated occurrences of the same variable can be universally
equal only with equal exponents, by (FJC.14); then they agree on every
assignment. For different variables, vary a private hole of one while
fixing the other: one mass is unbounded and the other fixed.
A decorated variable likewise cannot universally equal a residual-free
expression. Against a pair containing no occurrence of that variable,
the same independent mass variation excludes equality. Against a pair
containing that variable, choose its context filling with positive mass.
Along the explicit pair path above that occurrence, (FJC.13) increases
mass strictly, whereas a fixed power at the variable root preserves
mass. The pair value therefore has greater mass than the decorated
variable. Finally two ground sides compare directly, and a ground
leaf differs from a pair root. Reversing the sides changes none of these
arguments. These cases exhaust the normalized syntax and prove the
claim. The reverse implication is specialization to finite fillings.
The argument also covers zero remaining variables.

If a finite conjunction of whole negatives is feasible on the full
remaining product, each forbidden equality is nonuniversal there.
The claim makes each substituted equality nonuniversal on the private
frontier variables. Substitution still has grammar (FJC.6).
[URR, Theorem 3.1 and Corollary 3.2][URR] gives one computable finite
frontier tuple avoiding all those equalities simultaneously. This is
one joint filling, not one witness per negative. Thus any prescribed
nonground contexts preserve feasibility of the whole conjunction.

For precision, the URR construction takes the largest side weight $M$
(ground mass, with one added at each explicit pair), the largest
variable decoration $d$, a common mass $G=M+1$, and assigns successive
variables $\rho^{(i-1)(d+1)}c_G$. Residual-free values have mass at most
$M$; residual-containing pair values have mass at least $G+1$; a variable
value has mass $G$. The clock separates its finite decorations and the
separated exponent intervals distinguish different variables. Pair
cancellation then reflects every listed equality to universal equality.
This gives an explicit terminating filling algorithm after substitution.
For an empty negative list any finite fillings suffice. For no remaining
variables the exact finite ground tests suffice.

Now suppose the canonical tuple passes. Fix $h$. Keep its finite chart
coordinates exactly $f_i$. For every other coordinate compute the
prefix of its canonical infinite tree through $h$, preserving every
early leaf and its absent descendants. At every reached position of
depth $h+1$ replace the remaining subtree by a distinct hole.
An infinite full tree has an infinite branch, so this frontier is
nonempty. Every finite filling agrees through $h$ with that coordinate.
Coordinates in different charts have private fillings even if their
canonical state values coincide. Sharing inside a chart remains exact.

Apply the preceding negative construction to each chart with its entire
substituted $\Delta$. The resulting finite tuples satisfy every negative
of their own chart simultaneously. Since all their coordinates agree
through $h$ with the canonical ones, nonexpansion of native expressions
makes each finite source $\Theta_{r,c_r}(\mathbf z_{r,h})$ agree through
$h$ with its canonical completed output. Equation (FJC.11) makes these
completed outputs a single common tree. Thus all the finite sources
share a common inclusive original prefix. Equation (FJC.7) proves every
original literal, sign, guard and exact full row on each source. No sign
or finite partition has been passed to the limit, and no cross-source
finite equality was required.

Conversely suppose actual finite chart representatives exist at
unbounded depths $h_n\to\infty$. Choose their chart coordinates.
Compactness of the finite product of $\widehat{\mathcal T}$ supplies
a convergent subsequence with coordinate limit $\boldsymbol\xi$.
Continuity of all source expressions, and the common prefixes at
$h_n$, make the limiting source outputs equal: at any fixed depth the
coordinates and outputs eventually have their limit replies, and the
finite sources agree at that depth. By (FJC.11), the coordinate limit
extends to a solution of $\mathscr G$. A clash certificate would rule
this out.

Every coordinate finite in the canonical solution has the same exact
finite value in this extension, by Theorem 3.1. Such a finite tree is
isolated by its maximum-leaf-depth prefix. Convergence therefore makes
that coordinate in the finite witness sequence eventually equal to its
canonical value. There are only finitely many such coordinates; at a
late common index they all have those values simultaneously. That
finite witness satisfies every chart negative, so supplies feasibility
of each entire substituted conjunction in Definition 4.1. The canonical
tuple passes. This argument does not assert that the remaining
coordinates of $\boldsymbol\xi$ equal their canonical values. The
negative completion argument permits replacing them by the canonical
infinite choices. $\square$

## 5. A terminating decision and the actual row consumer

**Theorem 5.1 (functional-input decision and synthesis).** For every
functional rank-free input of Definition 2.4 there is a guaranteed
terminating choice between:

- YES, with effective finite sources $u_{r,h}\in D_r$ for every requested
  $h\ge0$, all sharing one original prefix through $h$;
- NO, with a finite $H$ for which $\neg J_B(H)$.

The procedure requires no supplied completion point, prescribed-depth
promise or observation of a plateau.

**Proof.** There are finitely many chart tuples. Check their supplied
completed-equation certificates and perform Definition 4.1 on every
nonclash tuple. Theorem 3.1 and the finite native feasibility supplier
make these finite tests terminate. If any tuple passes, the explicit
construction in Theorem 4.2 is the YES synthesis algorithm.

If $J_B(h)$ held for every $h$, exact chart completeness would supply
one chart for each finite source witness. Among finitely many chart
tuples, at least one would occur at unbounded depths. The converse of
Theorem 4.2 makes that tuple pass. Therefore failure of every tuple
proves $\neg\forall h\ J_B(h)$.

Extract a concrete depth by testing $h=0,1,2,\ldots$. Each test is
terminating: use independent whole-source variables $(u_r)_{r\in B}$,
impose the entire predicate (FJC.4), exact row $r$ for each, and equality
of their four replies at every word of length at most $h$.
[NSF, Lemma 5.1 and Theorem 5.2][NSF] allows any finite number of source
variables and this finite Boolean native query. Its witnesses are the
actual finite source tuple; no pairwise surrogate is used.
The proven $\neg\forall h\ J_B(h)$ guarantees that this search stops
at a false test, whose $H$ is sound. Merely failing to find a reduction
or a productive certificate would not justify this search guarantee;
here the class hypotheses and Theorem 4.2 do. $\square$

**Corollary 5.2 (whole-row recovery under the actual register bridge).**
Under Assumption 1.3, a YES for any $B$ of at least two distinct full
rows excludes a uniform finite-new-read legal static or serial forward
service recovering the entire $R_Q$ on $D$. A NO excludes only that
joint $B$ at its depth.

If additionally the entire attained image $\mathcal R=R_Q(D)$ is a
supplied finite exact list, and all its distinct pairs have functional
rank-free certificates, the full-row service existence question is
terminating: any YES pair excludes a uniform finite-read service; if
all pairs return NO, the maximum of their exclusion depths determines
the whole row. A singleton image needs no new reads. No finite-image
promise is needed for Theorem 5.1 itself.

**Proof.** Reuse [ARH, Definition 2.2 and (ARH.2.3)][ARH], with the
complete-state and same-register premises unchanged. A uniformly bounded
effective deterministic serial controller has a finite four-reply tree
of read outcomes. The supplier compresses each reply-free computation
and forward-update segment. Its finite set of submitted words has a
maximum original dependency depth, including born and absent positions.
Native locality then makes that original prefix determining. A YES
supplies two finite differently labelled sources agreeing through any
such depth, contradicting recovery. Static controllers are included.
This transfers an existence bridge, not an equality of optimal prices.

For $|B|>2$, exclusion at $H$ merely says no one $H$-prefix occurs in
every stratum of $B$. It can occur in several other rows or several rows
inside $B$. Even exclusion of one pair leaves other pairs untouched.
For an entire finite image, however, take the maximum $H$ of all pair
exclusions. If two sources at that depth had different full rows, their
pair would violate its own exclusion. This proves full-row determination.

The lawful consumer uses actual static epoch-$N$ reads to recover the
original replies through $H$, via [SLH, Theorem 2.2][SLH] and
[DelayedOriginalReadout.original_decoder_correct and
original_decoder_service][DECODER]. This gives upper bounds

$$
q\le2(2^{H+1}-1),\qquad a=0,\qquad
\text{total literal length}\le
 2(2^{H+1}-1)(H+\lceil N/2\rceil).
\tag{FJC.15}
$$

The bound includes original absence. Condition the whole input on the
recovered prefix and use NSF to produce one finite compatible source;
the actual source makes that query nonempty. Determination makes its
whole row the actual correct answer, without identifying the witness
with the actual source. Equivalently precompute a finite table of
nonempty conditioned-prefix fibers and their common rows.

Independently of a uniform bound, paid traversal of the current finite
tree $\rho^N u$ gives its whole finite description. The effective partial
inverse of [ARH, Lemma 19.2][ARH], applied $N$ times to that description,
recovers the finite original $u$ and hence its whole $R_Q(u)$. This is
local computation on paid evidence, not inverse execution on the register.
It proves sourcewise finite recovery even on a YES instance; it gives no
uniform read cap. The traversal costs $|\operatorname{Pos}(\rho^N u)|$
new calls and the sum of their actual address lengths, with storage and
inverse computation charged separately.

Preparation of the class certificates, their decisions, that table,
address generation, comparisons, memory, installation, acquisition and
entry remain paid separately from (FJC.15). A concrete compatible-source
search has sourcewise finite local cost; no optimum or uniform local-cost
bound is proved. ARH Proposition 2.1 provides paid pre-cut acquisition
with raw cost

$$
|\operatorname{Pos}(u)|+|H_0|
 +\sum_{(e,p)\in E}|\operatorname{Pos}((\rho^e u)|_p)|,
\tag{FJC.16}
$$

where endpoint occurrences $E$ retain repetitions and their traversals
include their root reads. Updates, finite word lengths, comparisons,
retained descriptions, certification and the cut add their own costs.
Every term is finite on each finite source. Nothing here grants a
runtime completion, coordinate, source selector or equality operation.
$\square$

## 6. A native acquired consumer with coupled outputs

**Proposition 6.1 (entire six-hole source correspondence).** Define

$$
\begin{aligned}
F(z,w)&=\langle\rho z,\rho w\rangle,\\
G(y)&=\langle\alpha,\rho y\rangle,&
H(y)&=\langle\beta,\rho^2 y\rangle,\\
U(y,z,w)&=\left\langle
 \langle y,\langle z,w\rangle\rangle,
 \langle F(z,w),\langle G(y),H(y)\rangle\rangle
 \right\rangle.
\end{aligned}
\tag{FJC.17}
$$

Take $P=\{\varepsilon\}$ with its full reached one-hole row,
$Q=(LL,LRL,LRR,RL,RRL,RRR)$, and authentic $N\ge2$.
Retain exactly these literals at epoch zero: branch at
$\varepsilon,L,LR,R,RR,RL,RRL,RRR$; $\alpha$ at $RRLL$;
$\beta$ at $RRRL$. Retain the positives

$$
\begin{aligned}
&(1,LRL,0,RLL,=),\quad (1,LRR,0,RLR,=),\\
&(1,LL,0,RRLR,=),\quad (2,LL,0,RRRR,=),
\end{aligned}
\tag{FJC.18}
$$

and the negative $(0,LRL,0,LRR,\ne)$. The entire fiber is exactly

$$
D_0=\{U(y,z,w):y,z,w\in\mathcal T,\ z\ne w\}.
\tag{FJC.19}
$$

It is a successful output of one common actual producer as in
Assumption 1.3. All six original $Q$-holes are reached. Its full exterior
is

$$
\left\langle
 \langle\square_1,\langle\square_2,\square_3\rangle\rangle,
 \langle\square_4,\langle\square_5,\square_6\rangle\rangle
\right\rangle.
\tag{FJC.20}
$$

**Proof.** The branch literals uniquely decompose an admitted original
source into the six-hole skeleton, with arbitrary values $y,z,w$ in
its first three holes, a pair $\langle a,b\rangle$ in the fourth,
$\langle\alpha,c\rangle$ in the fifth and
$\langle\beta,d\rangle$ in the sixth. All endpoints of (FJC.18) are
reached: their epoch-zero parents are stipulated branches, and those
original branches persist under $\rho$. Transport of an originally
reached subtree makes their whole comparisons respectively
$a=\rho z$, $b=\rho w$, $c=\rho y$, $d=\rho^2y$.
The retained negative is exactly $z\ne w$. This reconstructs that
same original source as (FJC.17). Conversely every source in (FJC.19)
has every stated literal, reached endpoint, positive comparison and
negative. The root old row is automatic, including its singleton
partition. These are both source directions, and (FJC.20) retains the
whole exterior rather than selected comparisons.

For actual acquisition use the public coordinate schedule of
[ARH, Proposition 2.1][ARH]: compute the old row at epoch zero, acquire
the finite descriptions of requested epoch-zero endpoints, update the
same register to epochs one and two, acquire their specified endpoint
descriptions, and compare the retained finite descriptions. Continue to
$N$ and apply the stipulated complete cut. On every finite source this
procedure is paid and source-total, with invalid outcomes if endpoints
fail. Every displayed $U$ gives the stipulated successful outcome;
conversely that outcome entails exactly (FJC.19). This is conditional
on the same complete-state access premise, not a new producer axiom.
$\square$

**Proposition 6.2 (exact full strata and synthesized contact).** With
the common exterior (FJC.20), let $r_0,r_1$ have complete partitions

$$
\pi_0=\{\{1,4\},\{2\},\{3\},\{5\},\{6\}\},
\qquad
\pi_1=\{\{1\},\{2,5\},\{3,6\},\{4\}\}.
\tag{FJC.21}
$$

Their exact strata in the entire fiber (FJC.19) are

$$
\begin{aligned}
D_{r_0}&=\{U(F(z,w),z,w):z,w\in\mathcal T, z\ne w\},\\
D_{r_1}&=\{U(y,G(y),H(y)):y\in\mathcal T\}.
\end{aligned}
\tag{FJC.22}
$$

Both rows are attained. Their common-output equations have a functional
native presentation. Theorem 5.1 returns YES and synthesizes actual
finite sources in both strata with a common prefix at every requested
depth. Other full rows of $D_0$ are preserved.

**Proof.** Finite leaf count gives
$\ell(\rho^a t)\ge\ell(t)$ and
$\ell(\langle s,t\rangle)=\ell(s)+\ell(t)$.
Thus $F(z,w)$ has strictly more leaves than either $z$ or $w$,
and $G(y),H(y)$ each have strictly more than $y$. Also $G(y)\ne H(y)$
because their left children are $\alpha$ and $\beta$.

In the first displayed stratum, the hole values are
$y=F(z,w),z,w,F(z,w),G(y),H(y)$. The first and fourth are equal.
The second and third are unequal by the entire history. Both differ
from $y$ by the leaf count of $F$. Both last values have strictly more
leaves than $y$ and hence than $z,w$. They differ from one another by
their left children. These are all cross-class inequalities of $\pi_0$.
Conversely row $r_0$ imposes $y=F(z,w)$, and its source already has
$z\ne w$, so (FJC.22) recovers the same source.

For the second stratum, set $z=G(y),w=H(y)$.
These differ, satisfying the retained negative. They have more leaves
than $y$; $F(z,w)$ has more than either, and consequently more than $y$.
Thus exactly the indicated copies are equal and every different class
of $\pi_1$ is unequal. Conversely its second/fifth and third/sixth
class equalities force exactly $z=G(y),w=H(y)$, recovering the same
source. No additional literal or reach restriction remains.
The examples $(z,w)=(\alpha,\beta)$ in the first chart and $y=\alpha$
in the second prove attainment. Constructor decomposition, positive
substitution and the proven redundant-conjunct removals furnish the
checkable chart reductions of Definition 2.2.

Write the first-chart coordinates as $Z,W$ and the second-chart
coordinate as $Y$. Equality of the full completed sources cancels their
identical outside constructor skeleton. Equality of their first three
holes is exactly

$$
Y=F(Z,W),\qquad Z=G(Y),\qquad W=H(Y).
\tag{FJC.23}
$$

These imply equality of the other three holes by substitution into
$F,G,H$. Conversely equality of whole sources implies the first three
hole equations by ordered-pair cancellation. Hence (FJC.23), with no
auxiliaries, proves both completed directions of (FJC.11).
It is a functional system with every dependency below a pair and all
three states reaching a directed cycle. Theorem 3.1 makes all its
canonical coordinates infinite; there are no finite coordinates to
freeze. The first-chart conjunction $Z\ne W$ is feasible, and the
second conjunction is empty, so the canonical tuple passes. Theorem
4.2 constructs the finite signed realizers; it does not assert that
finite sources satisfy (FJC.23) exactly.

The source $U(\alpha,\alpha,\beta)$ also belongs to $D_0$.
Its hole values satisfy $1=2=\alpha$, $3=\beta$,
$4=6=\langle\beta,\langle\beta,\alpha\rangle\rangle$ and
$5=\langle\alpha,\beta\rangle$. Its full partition is therefore
$\{\{1,2\},\{3\},\{4,6\},\{5\}\}$, distinct from both selected
rows. This third row remains in the entire input: testing
$B=\{r_0,r_1\}$ does not replace $D_0$ by their two strata.
$\square$

**Proposition 6.3 (lawful additional negative records).** Retain any
finite additional list of negative records whose endpoints have proved
uniform reach on the whole family $D_0$ and whose entire actual-epoch
values have proved rank-free expressions in $y,z,w$. Let their whole
translated conjunction be $\Delta(y,z,w)$. The new entire fiber is

$$
D^- =\{U(y,z,w):z\ne w,\ \Delta(y,z,w)\}.
\tag{FJC.24}
$$

Its two selected strata have the same source expressions as (FJC.22),
with entire chart conjunctions

$$
z\ne w\ \land\ \Delta(F(z,w),z,w),\qquad
\Delta(y,G(y),H(y)),
\tag{FJC.25}
$$

respectively. They are attained precisely when their conjunctions are
feasible. If both are feasible, the selected pair still has all-depth
joint contact, with effective finite realizers satisfying every added
negative. If either fails, that row is not an attained label of $D^-$.

**Proof.** A structural endpoint stops within the explicit source
skeleton, ground expansion or at a parameter token; it does not navigate
an unspecified parameter. Its original reach is forced by that skeleton,
and its epoch-$e$ subtree is the actual $\rho^e$-transform of the
corresponding expression. Distributing the fixed power gives (FJC.6).
More general endpoints require the stated separate reach and expression
proofs. Under these premises each signed record is precisely its whole
negative expression, so (FJC.24) has both original-source directions.
Intersecting the exact strata (FJC.22) with the entire new conjunction
gives (FJC.25) in both directions. The common-output equations remain
(FJC.23); its canonical coordinates are infinite. Thus its canonical
tests are exactly feasibility of (FJC.25), decided by URR or NSF.
Theorem 4.2 provides one joint negative filling for each source at every
requested depth. Positives, new literals, nonuniform reach, or navigation
inside an unrestricted residual do not follow from this proposition;
they require new exact chart certificates. The paid common producer
acquires the additional whole descriptions and signs before the same
complete cut, as in Proposition 6.1. $\square$

## 7. A concrete boundary and the unchanged larger problem

**Theorem 7.1 (an acquired atomic tail has no finite rank-free cover).**
The actual acquired fiber in [ARH, Proposition 7.1][ARH], namely

$$
\begin{gathered}
P=\{L,R\},\quad
R=(\langle\square_1,\square_2\rangle,\{\{1\},\{2\}\}),\quad
H_0=\varnothing,\\
H_{\rm rel}=\{(0,\varepsilon,1,L,=)\},\quad N\ge1,\qquad
D_\star=\{T_j:j\ge2\},
\end{gathered}
\tag{FJC.26}
$$

has no representation as a finite union of rank-free negative-only
chart images (FJC.7). Even its infinite stratum at
$Q=\{LL,LR,RL,RR\}$ with reached four-hole exterior and partition
$\{\{1\},\{2,3\},\{4\}\}$, consisting of $j\ge4$, has no such
finite cover.

**Proof.** ARH Proposition 7.1 proves exactly the whole source fiber
and actual acquisition: the root-to-descendant positive forces an
atomic iterate, and the old reached two-hole row retains its distinct
children, excluding the smaller indices. Its entire four-hole rows are
$\langle\beta,\alpha\rangle$ with no reached cut for $j=2$;
$\langle\langle\square_1,\square_2\rangle,\beta\rangle$ with two
singleton classes for $j=3$; and
$\langle\langle\square_1,\square_2\rangle,
\langle\square_3,\square_4\rangle\rangle$ with the partition in the
statement for $j\ge4$. These suppliers retain all old guards and
inequalities and the same paid complete-state premise.

Every atomic $T_j$ has mass $\gamma(T_j)=0$ by ABC. Consider an
inhabited rank-free chart with output $\Theta$ and feasible whole
negative conjunction $\Delta$. If its output contains a residual
variable, the URR separation construction used in Theorem 4.2 can choose
its common residual mass $G$ arbitrarily large, subject to $G>M$.
All its equality-reflection arguments still hold: ground masses stay
below $G$, residual pair masses exceed $G$, and separated clock
intervals distinguish the decorations. Consequently this finite tuple
still satisfies every feasible negative. Every residual appearing in
the output has positive mass $G$, and fixed powers and pairing never
decrease that mass. The output therefore has positive mass, contrary
to containment in the atomic tail.

An inhabited chart whose output contains no residual variable produces
one fixed finite source, even if its unused coordinates occur in
$\Delta$. An empty chart produces none. Hence finitely many charts
contained in the tail produce only finitely many sources, while the
indices $j\ge2$ and $j\ge4$ each give infinitely many distinct $T_j$.
The contradiction proves both claims. Variable atomic ranks are a real
boundary of this input class. It does not prove undecidability or rule
out another representation. $\square$

**Open problem 7.2 (unrestricted stopping).** For arbitrary complete
acquired native $I$ and arbitrary finite distinct attained full rows
$B$, decide $\forall h\ J_B(h)$ with actual finite-source synthesis
or a finite exclusion depth. General mixed covers can require
unbounded atomic-rank coordinates, whose joint cofinal finite support
must be preserved, and common-output equations can have multiple
nonfunctional constraints or image/inverse restrictions. No complete
effective reduction of those cases to (FJC.10) is proved here. A failed
reduction has no NO meaning for such an input. Fixed-depth feasibility,
finite images and equality of supplied recursive descriptions do not
supply that missing reduction or an outer stopping rule.

The functional decision asserts existence of one synthesized contact
certificate for each positive instance in its stated class. It does
not represent every semantic common completion point. A completion
point outside a chosen description language does not refute an
existential certificate basis when the same instance has another
representable contact. No claim of all-input synthesis, physical
spacetime recovery, undecidability, global research completion or
resource optimality follows.

## 8. Exact suppliers, attribution and transfer limits

**Definition 8.1 (mathematical source correspondence).** The accepted
mathematical suppliers below are read at revision
`3508d303746985c18ca446a13c92b5c22f9df10d`. Their ordinary prose is used
at its explicit hypotheses; this volume asserts no new kernel evidence.
ARH Definitions 1.1–1.2, Assumption 1.3, Proposition 2.1 and (ARH.2.3)
provide the complete acquired predicate, both producer directions and
the paid static/serial/prefix existence bridge. ARH Lemma 19.2 provides
finite injectivity, locality and the clock, not a free-unary occurs-check.
NSF Theorem 4.3 and Lemma 5.1–Theorem 5.2 provide terminating finite
native feasibility, witnesses and finite multi-source observation
queries. NSF Theorem 6.1 is a supplied-depth decision, not an all-depth
cutoff. NIC Theorems 3.2–3.3 and 4.3 provide exact signed mixed images
and full strata with actual-source preservation; their scalar ranks
cannot be removed without proof. URR Theorem 3.1–Corollary 3.2 provides
one simultaneous finite separating tuple on the whole Cartesian
residual carrier. ABC Theorems 2.2–2.3 provide the normal atomic code
underlying its mass. SPC Theorem 2.2 verifies a sufficient productive
certificate and constructs witnesses, without claiming completeness.
[NPL, Theorem 5.3][NPL] supplies a terminating finite complete-row-image
decision and exact list when finite; it provides no canonical functional
presentation or all-depth joint stopping theorem.

The exact public and private declaration correspondence is as follows.
All names are in `D5.S3.Arith.FibonacciAtomic.Observer`, followed by
the indicated module namespace.

| Declaration source | Reused interface and limit |
| --- | --- |
| [NativeDepthPatterns][DEPTH] `original_prefix_locality`, `original_present_transport`, `depthEquiv`; private `fill_decompose`, `decompose_fill` | Fixed native epoch replies depend only on original prefixes; exact actual-frontier decomposition. The `History` abbreviation is literal history, not arbitrary signed relations. |
| [NativeCutFibers][CUT] `rowFiberEquiv`, `legal_values_row`; private `recover_fill`, `fill_injective`, `classValue_distinct` | Exact old row with concrete exterior and all different-class inequalities. No new coupled-history solver. |
| [NativeHistoryCells][CELLS] `historyCellEquiv`, `cell_feasibility_exact`; private `syntax_iff_ground`, `sourceCell_right`, `cellSource_injective` | Literal-history cells and same-source inverse maps, with all old off-task inequalities. These are not promoted to arbitrary signed-history declarations. |
| [NativeSymbolicRecutting][RECUT] `symbolic_recut_exact`; private `termAt_fill`, `exterior_commute` | Complete reached list, exterior, actual subtrees and partition, under the stated deep-frontier bounds. |
| [NativeGroundSeparation][NGS] `simultaneous_ground_separation`; private `count_length`, `evaluated_length`, `compound_mass_ne`, `bounded_eval_injective`, `code_mass`, `code_injective` | The finite free-magma equal-mass separation method. URR supplies the interpreted-$\rho$ mass-and-clock extension actually needed here. |
| [DelayedOriginalReadout][DECODER] `original_decoder_correct`, `original_decoder_service`; private `present_label_decode`, `original_query_bounds` | Current-register decoding of original presence and labels with at most two reads and the stated word bound. An offline tree witness is not an actual observation. |

These declarations supply source interfaces and mathematical antecedents.
No compilation or kernel claim about the new functional decision is
inferred from their names or from reading their proof terms.

**Definition 8.2 (overlap and primary literature).** NCC at
`0487ddfee131db56e40b654fad5a69689948e3c7`, Theorems 3.2–3.3 and 4.1,
already treats prefix-substitution conservativity, negative density and
supplied-coordinate closure. NGE at
`c0f820f0b4800326b5c9d06b23f11ce925b404fb`, Assumption 1.2 and its
guarded-description equality development, treats equality of supplied
nullary descriptions. These are attributed overlapping manuscripts;
neither is an accepted axiom or an assumed producer correspondence.
No premise is taken from PDC at
`5f6e4c682e3e92206e00b81be891b30e35a25f1b`.

[Comon–Lescanne, *Equational Problems and Disunification*, Journal of
Symbolic Computation 7 (1989), 371–425][CL], §2.1 Theorem 1, attributes the unique rational
solution of finite functional systems with distinct left variables and
non-variable right sides in a free signature to Huet. Its §3.2 Lemma 1
and Appendix B.3 concern nontrivial syntactic disequations with infinite
sort carriers. Section 6.2 explicitly excludes general nontrivial
equational theories from the preceding completeness results. Those
free-signature results are literature-attested background. They do not
supply the interpreted native root-shift argument, the negative density
bridge, or the source/row fidelity here; finite native equations can
have infinite atomic solution families.

[Milius–Moss, *The Category Theoretic Solution of Recursive Program
Schemes*, arXiv:0904.2385v2][MM], §7.3 and Theorem 7.15, treats guarded recursive
program schemes for contracting functors on nonempty complete metric
algebras, with the required iterative/Elgot structure. This is
literature-attested guarded-recursion background. Our pair-guarded map
is verified directly by one-level prefix gain; bare $\rho$ is
nonexpanding and has not been assumed to be a contracting free
operation. No general recursive-scheme synthesis or description
completeness theorem is imported.

The repository-derived increment is the complete functional-input
canonical test, its forced-finite-coordinate converse, effective signed
finite-source synthesis, and its exact acquired consumer. The accepted
negative separation and the overlapping prefix-conservativity argument
are intermediate ingredients, not a newly claimed general theorem.
The source comparison is limited to the named mathematical suppliers,
the listed public/private declarations and these primary texts. It is
not an exhaustive literature or third-party-library search and supports
no external-priority claim.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[NCC]: https://github.com/the-omega-institute/trureturing/blob/0487ddfee131db56e40b654fad5a69689948e3c7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CHART_CLOSURE.md
[NGE]: https://github.com/the-omega-institute/trureturing/blob/c0f820f0b4800326b5c9d06b23f11ce925b404fb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GUARDED_EQUALITY.md
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[CUT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[CELLS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[RECUT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[NGS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[DECODER]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[MM]: https://arxiv.org/abs/0904.2385v2

## 追加锚（本行以下为增补区）

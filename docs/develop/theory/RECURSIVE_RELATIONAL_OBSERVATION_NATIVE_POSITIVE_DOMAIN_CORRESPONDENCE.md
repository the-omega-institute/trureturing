# All-source positive-domain correspondence for native residual completion

> This is a generic-v1 theory volume. Its definitions and ordinary proofs
> are reference input, not a second mathematical truth source. Existing
> sections remain unchanged after integration; additions and corrections
> belong after the terminal append anchor.

## 1. The original domain and the local result

**Definition 1.1 (finite native sources).** Use the algebra of [ABC][ABC]
and [NSF][NSF]:

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&
\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle x,y\rangle&=\langle\rho x,\rho y\rangle,\\
T_n&=\rho^n\alpha\qquad(n\in\mathbb N).
\end{aligned}
\tag{PDC.1}
$$

All trees are nonempty, finite and ordered. A native expression uses
variables, the two leaves, pairing and fixed natural powers of this
interpreted $\rho$. There is no common bound on the size, depth, atomic
rank or normal shape of a source. In particular $\rho$ is not a free
unary constructor.

For an original-root word $p$, the reply $r_u(p)$ is one of
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$. Write $u\sim_h v$ when
these replies agree at every $|p|\le h$. Depth is inclusive throughout.
For a finite prefix-free cut $Q$, the full row $R_Q(u)$ consists of its
reached cut positions in their fixed order, the entire concrete exterior
with those positions replaced by numbered holes, and the complete
equality partition of their whole subtrees. An absent cut creates no
hole. The empty cut retains the whole source as exterior.

**Assumption 1.2 (entire acquired signed fiber).** Fix the complete input
of [ARH, Assumption 1.3][ARH], equivalently [NSF, Assumption 1.2][NSF].
An old cut $P$, its full row $R$, a finite literal list $H_0$, and a
finite signed mixed-epoch list $H_{\rm rel}$ define

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{PDC.2}
$$

A signed record $(a,p,b,q,\bowtie)$ means

$$
p\in\operatorname{Pos}(\rho^a u)\ \land\
q\in\operatorname{Pos}(\rho^b u)\ \land\
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q,
\qquad \bowtie\in\{=,\ne\}.
\tag{PDC.3}
$$

Both guards are required for either sign. Every literal, repeated name,
repeated old class, different-class inequality, off-task inequality and
concrete old exterior belongs to this same predicate on the same $u$.
No consistency promise is needed for the mathematical construction;
service applications retain $D\ne\varnothing$.

For those applications the retained records have actually been acquired,
the original-root register is at the authentic epoch $\rho^N u$, and
the complete accessible state is common on exactly $D$. The available
source operations remain actual original-root reads, forward updates of
that same register and absorbing halt. Mathematical coordinates,
representatives, inverses and branch labels below supply no observation,
source selection, reset, rerooting or equality port.

**Result 1.3 (scope and precise increment).** The result below constructs
a finite cover of all of $D$ by injective native maps

$$
\begin{aligned}
\Theta_i:\mathcal C_i&\longrightarrow D,\\
\mathcal C_i
&=\{(\mathbf n,\mathbf z)\in\mathbb N^{k_i}\times\mathcal T^{m_i}:
             K_i(\mathbf n)\land\Gamma_i(\mathbf n,\mathbf z)\}.
\end{aligned}
\tag{PDC.4}
$$

Here $K_i$ is an explicit scalar Presburger condition. Each $\Gamma_i$
is a finite conjunction of whole native disequalities of exactly the
mixed-template grammar in [URR, Definition 1.2][URR]. Its residual
quantifier is literally over $\mathcal T^{m_i}$. Every residual sort
restriction occurs inside this displayed negative list; there is no
additional positive, image, normality or reach predicate on the carrier.

The arbitrary-positive native image cover and its Cartesian URR consumer
are already supplied by [NIC, Theorems 3.2–3.3 and 4.3, Proposition
3.5][NIC]. Those images may overlap and need not have unique arguments;
their construction deliberately permits nonnormal assembled codes.
The additional correspondence here retains canonical named values to
obtain injective charts and recover their coordinates from bounded
original prefixes. Elimination, feasibility and the common-completion
section alone are not claimed as new results. Ordinary free-constructor solution
spaces, native coding, feasibility, scalar projection, common completion
and supplied-depth decisions are reused. In particular [NLC, Lemma
2.2][NLC] already supplies exact all-source branch factoring and a
separate marker-witness guarantee. Its second guarantee expressly does
not parameterize its first. The proof here does not replace any actual
source by a marker witness.

All statements are ordinary mathematics. There is no new Lean
verification, solver implementation, physical execution, complexity
bound or literature-wide novelty claim. The original unrestricted
determining-prefix decision remains the explicit problem in §8.

## 2. Exact input suppliers and the free-constructor interface

**Convention 2.1 (normal-code supply).** Reuse [ABC, Theorems 2.2–2.3][ABC].
The maps $B:\mathcal T\to\mathcal N$ and $E:\mathcal N\to\mathcal T$ are
inverse bijections. Normal codes have primitive leaves $[r]$,
$r\in\mathbb N$, and constructor $F$, with every occurrence of
$F([r+1],[r])$ forbidden. Thus

$$
\begin{aligned}
B(T_r)&=[r],&
E(F(X,Y))&=\langle E(X),E(Y)\rangle,\\
J(X,Y)&=
\begin{cases}
[r+2],&X=[r+1],\ Y=[r],\\
F(X,Y),&\text{otherwise},
\end{cases}\\
B(\rho^a u)&=\tau_a B(u).
\end{aligned}
\tag{PDC.5}
$$

Translation $\tau_a$ adds $a$ to every rank. For $a\ge0$ it preserves
normality. Its image is exactly the normal codes with all ranks at
least $a$, and subtraction is its unique inverse on that image.
Atomic indices are injective. These are supplier results.

For intermediate algebra only, let $\mathcal K_{\mathbb Z}$ be the
free finite $F$-trees with integer-labelled leaves. On this auxiliary
set $\tau_d$ is defined for every $d\in\mathbb Z$, commutes with $F$,
and is bijective. A negative integer label has no native expansion.
No negative power of $\rho$ is introduced. Sections 4–5 impose exactly
the conditions that return every named value to $\mathcal N$.

**Construction 2.2 (original constructor cells).** Use either one of the
complete covers of [ARH, Definitions 19.3 and Proposition 19.4][ARH],
with [NSF, Lemma 5.1][NSF] for any additional fixed full-row predicate.
It gives finitely many original constructor patterns $W_\eta(X_\eta)$
and conjunctions, or finitely distributed Boolean branches,
$\Phi_\eta(X_\eta)$. Every frontier variable has a fixed reached
representative original address $a_{\eta,x}$. The source is recovered
by filling $W_\eta$; its inverse takes these actual subtrees.

Navigation uses the actual finite iterate of an early original leaf.
An endpoint born during such an iterate is evaluated there; an endpoint
absent at its recorded epoch rejects either sign. Literal repetitions
and all old class inequalities stay in the same cell. The reached
target set $I_\eta$, its complete native mask $M_\eta$, and all whole
target-hole expressions $H_{\eta,q}$ are retained simultaneously.
The mask replaces only reached target holes by $\alpha$, and retains
every uncut residual term. Its reached positions recover the numbered
exterior, by [ABC, Theorem 4.2][ABC].

These are exact source and recutting suppliers, not new navigation or
feasibility theorems. The cell cover can resolve a finite list of
requests without bounding the unresolved frontier trees. Its
constructor distinctions must not be confused with the later
algebraic branches.

**Construction 2.3 (use of the existing ground solution equivalences).**
Within a conjunction, let $C$ be its positive equations that contain
only Boolean leaves, variables and pairing. Let $\Delta$ contain its
free-constructor disequalities, and let $G$ be the conjunction of all
remaining interpreted constraints. Keep the finite variable set
$X=X_\eta$ in full, including variables absent from $C$.

The exact source interface is [NativeGroundSolutionSpace][NGSS].
Use its Presentation enumerating all of $X$, encodeEquations, and a
successful output $S$ of the actual empty-state free-term unifier.
Its notation gives

$$
\begin{aligned}
Y&=\{x\in X:x\notin D(p,S)\},\\
\operatorname{Ext}(w)(x)
  &=\operatorname{evaluate}(w,\sigma(x)),\\
\{w:Y\to\mathcal T:\ &
  \operatorname{Diseq}(\Delta)(\operatorname{Ext}w)
       \land G(\operatorname{Ext}w)\}\\
&\simeq
\{v:X\to\mathcal T:
  \operatorname{Sol}(C)(v)\land
  \operatorname{Diseq}(\Delta)(v)\land G(v)\}.
\end{aligned}
\tag{PDC.6}
$$

This is precisely constrainedEquiv; solutionEquiv is its unrestricted
equation interface. Their inverse is restriction to the unbound
original variables. The declarations restriction_Ext, Ext_restriction,
Ext_sol and action_identity supply the identities, including unused
and repeated original variables. The predicate $G$ is pulled back
through the same Ext, not through an independently chosen witness.

The underlying Source is FreeMagma Bool and Term $X$ is
FreeMagma $(\mathrm{Bool}\mathbin{\oplus}X)$, with
$\alpha=\mathtt{of\ true}$, $\beta=\mathtt{of\ false}$ and pairing
$\mathtt{mul}$. The native encoding and its support conditions come
from [NativeUnificationCore][NUC]. [NativeTermUnification][NTU] supplies
the terminating free-term procedure; [NativeSubstitution][NSUB]
supplies its well-formed substitution idempotence and native constructor
preservation; [UnificationCompleteness][UC] supplies unify_sound,
unify_mgu and unify_complete. NativeGroundSolutionSpace's
native_complete justifies discarding a failed free subsystem.

No part of that syntax contains interpreted $\rho$. Thus (PDC.6)
retains $G(\operatorname{Ext}w)$ and does not yet meet URR's hypothesis.
Substitute the supplied finite terms $\sigma(x)$ into every remaining
constraint, source expression, mask and hole expression. An unbound
$y\in Y$ is still the source subtree at $a_{\eta,y}$, because Ext fixes
it. The empty free subsystem is allowed. No free unification theorem
or ground-decoding theorem is reproved here.

## 3. Interpreted positive equations as a finite weighted system

**Definition 3.1 (all names and exhaustive collapse cases).** In each
remaining Boolean conjunction, retain all variables in $Y$ and give
each native subexpression a name. Include subexpressions of the source,
mask, hole expressions and both sides of every positive or negative
atom. A name denotes its actual deterministic expression in $Y$;
repeated uses share its value. Constants can be expanded into their
finite Boolean/pair syntax.

Use [NSF, Definition 2.2 and Lemma 2.3][NSF]. A name definition is
$X_v=[0]$, $X_v=[1]$, $X_v=\tau_aX_w$, or
$X_v=J(X_l,X_r)$. For each $J$ choose exactly one of:

$$
\begin{array}{ll}
\text{collapse:}&
 X_l=\tau_1X_r,\quad X_v=\tau_2X_r,\quad X_r\text{ primitive};\\
\text{ordinary:}& X_v=F(X_l,X_r).
\end{array}
\tag{PDC.7}
$$

All names will be required normal. In particular normality of the
ordinary output excludes its forbidden primitive cherry. The collapse
case introduces no independent scalar witness: its rank is already
the rank of the existing name $X_r$. Positive equalities are offset-zero
edges. Original negatives remain whole named-code disequalities,
with repetitions retained. No negative is replaced by a conjunction
of childwise negatives or discarded because two symbolic shapes differ.

**Definition 3.2 (weighted closure).** Regard an edge
$X_v=\tau_dX_w$ as an integer offset constraint. Compute connected
components with integer potentials, maintaining

$$
X_v=\tau_{p_v}S_C\quad(v\in C).
\tag{PDC.8}
$$

Choose an existing name $r_C$ as representative, with $p_{r_C}=0$;
thus $S_C=X_{r_C}$. Merge components when adding a new edge, or check
its offset against the existing difference. Reject a nonzero-offset
cycle.

Primitive flags propagate across a component. A ground condition
$X_v=[a]$ makes $S_C=[a-p_v]$; multiple ground conditions must agree.
Whenever two retained definitions

$$
X_v=F(X_l,X_r),\qquad X_w=F(X_{l'},X_{r'})
$$

have parent names in one component, put $d=p_v-p_w$ and add

$$
X_l=\tau_dX_{l'},\qquad X_r=\tau_dX_{r'}.
\tag{PDC.9}
$$

Continue until every connected pair of parent definitions has been
inspected. Reject a component carrying both a primitive flag and an
$F$ definition. Finally form the directed graph from each defined
component to the components of both its children, and reject a directed
cycle.

**Lemma 3.3 (finite closure and preservation of every solution).**
This closure terminates. Every rejection just described excludes all
solutions of that branch in $\mathcal K_{\mathbb Z}$. Every edge added
preserves its entire solution set. In a nonrejected final system,
one chosen $F$ definition per defined component implies all its
other $F$ definitions.

Proof. Translation preserves the finite shape and adds its offset to
the minimum of the nonempty finite set of leaf labels. Thus
$X=\tau_dX$ forces $d=0$. Ground and primitive/$F$ conflicts have the
stated immediate necessary consequences. Free ordered $F$ injectivity,
together with its commutation with $\tau_d$, proves (PDC.9) from the
two parent definitions. Conversely (PDC.9) and either parent definition,
with their already imposed parent offset, recover the other.

Let $v$ be the number of names and $f$ the number of retained $F$
definitions. There are at most $\max(0,v-1)$ strict component merges.
Two already connected names have a fixed relative offset; any later
incompatible requirement rejects instead of changing it. Mark each
unordered pair of $F$ definitions when its connected parents are
inspected. At most $\binom f2$ such inspections add two edges apiece.
The initial edge list is finite. Scanning the finite uninspected list
after a merge, and stopping when no connected uninspected pair remains,
therefore terminates. These counts prove termination of a finite
symbolic construction, not a complexity bound.

For the last rejection, let $s(X)$ count $F$ nodes of an integer code.
It is invariant under translation, whereas
$s(F(A,B))=1+s(A)+s(B)$ is strictly larger than either child's count.
Along every component-to-child edge the count strictly decreases.
A directed cycle is impossible in a finite-code solution.

At termination two parent definitions in a component have been compared.
Their corresponding children are in the same respective components
with the exact offset (PDC.9). Hence their defining expressions for
$S_C$ coincide under (PDC.8). One definition therefore suffices without
dropping the force of any other. $\square$

This finite-tree check is performed after the exhaustive native collapse
choices. It is not a free-constructor occurs check on an unprocessed
equation involving $\rho$.

**Lemma 3.4 (complete acyclic expansion).** For each nonrejected system,
one obtains finite expressions for every $X_v$ in independent sink
values. A sink is a fixed integer primitive, a free integer primitive,
or an arbitrary member of $\mathcal K_{\mathbb Z}$. These expressions
parameterize exactly all its positive solutions before natural-rank
and normality requirements.

Proof. For a chosen definition $X_v=F(X_l,X_r)$ in component $C$, with
child components $L,R$, (PDC.8) gives

$$
S_C=
 F\bigl(\tau_{p_l-p_v}S_L,\tau_{p_r-p_v}S_R\bigr).
\tag{PDC.10}
$$

Expand in a topological order of the finite acyclic graph. At a sink,
a ground flag fixes its primitive value; a remaining primitive flag
allows an arbitrary integer rank; otherwise allow any integer code.
Distribute all translations through displayed $F$ nodes and compose
them at sink occurrences. Formula (PDC.8) then gives an expression
for every name, not only for a designated output.

Every positive solution supplies its own values at the representative
names of the sinks, and induction in that order recovers all its named
values. Conversely any assignment of the stated sink types defines all
components by (PDC.10), satisfies every original offset and ground
condition, and satisfies all $F$ definitions by Lemma 3.3. The expansion
therefore has both directions and a unique inverse on its full named
assignment space.

Different unflagged sinks may acquire equal shapes or equal values.
There is no marker separation requirement. Any original constraint
against such coincidence remains its whole negative in §5. $\square$

## 4. Discharging all images and all normality conditions

**Definition 4.1 (bounds from every named expression).** For each free
sink $C$, collect the integer offsets $d$ at all occurrences of $S_C$
in the expansions of every name in Lemma 3.4. This includes its own
representative occurrence, of offset zero. Define

$$
L_C=\max\bigl(\{0\}\cup\{-d:d\text{ occurs for }C\}\bigr).
\tag{PDC.11}
$$

Check every occurrence of every fixed primitive after its translations;
reject a negative fixed rank. For a free primitive sink write
$S_C=[L_C+n_C]$. For a free unrestricted sink write
$S_C=\tau_{L_C}V_C$. These are changes of mathematical coordinates on
an image, not inverse native actions.

**Lemma 4.2 (exact image bounds on the full domain).** Subject to the
fixed-rank check, every named expansion has natural leaf ranks exactly
when each free primitive rank is at least $L_C$ and each unrestricted
sink has minimum leaf rank at least $L_C$. On normal sinks the changes
in Definition 4.1 are bijections from, respectively, $\mathbb N$ and
$\mathcal N$. After substitution, every displayed variable offset is
nonnegative.

Proof. An occurrence $\tau_dS_C$ has natural labels exactly when
$\min\operatorname{rank}(S_C)+d\ge0$. In the primitive case this minimum
is its single rank. Every leaf of every expansion is either such a
translated sink leaf or a checked fixed primitive. The conjunction over
all occurrences is therefore exactly (PDC.11), in both directions.
The representative occurrence ensures that the sink itself is among
the conditions.

For an actual normal sink satisfying the bound, [ABC, Theorem 2.3][ABC]
supplies its unique normal preimage under $\tau_{L_C}$. Conversely
translation of any normal preimage gives exactly that image. For a
primitive this is the usual unique decomposition of a natural rank as
$L_C+n_C$. Each occurrence now has offset $L_C+d\ge0$. Normality of
the explicit constructors remains to be imposed; it has not been
inferred merely from the rank bound. $\square$

**Construction 4.3 (root sorts and the scalar condition).** Split every
remaining unrestricted normal $V_C$ into its exhaustive disjoint cases:
a primitive $[n_C]$, or an $F$-rooted normal code. A primitive case
adds one scalar coordinate. Retain one residual coordinate for each
$F$-rooted case. There are finitely many such choices.

After this split, each subtree of a named expansion has a known root
sort. It is a primitive constant $[a]$, a primitive $[n_j+c]$, a
translated nonprimitive residual, or an explicit $F$ node. In every
named expansion inspect every explicit $F$ node. If both children
have primitive roots, with respective ranks $a(\mathbf n)$ and
$b(\mathbf n)$, impose

$$
a(\mathbf n)\ne b(\mathbf n)+1.
\tag{PDC.12}
$$

If at least one child is nonprimitive, its root cannot be a forbidden
primitive cherry. Let $K(\mathbf n)$ be the conjunction of all checks
(PDC.12); a false constant check makes $K$ false. All constants and
offsets are natural after Lemma 4.2. Hence $K$ is a finite
quantifier-free Presburger condition, independent of the residuals.

**Lemma 4.4 (normality with no unlisted residual predicate).** Represent
an $F$-rooted residual by $V_C=B(z_C)$, with $z_C\in\mathcal T$, and
put the single whole native negative

$$
\rho^2z_C\ne\langle\rho z_C,z_C\rangle
\tag{PDC.13}
$$

in the residual list. Then all named expressions are normal exactly
when $K$ holds, on the stated root-sort branch. The root-sort condition
on every residual is exactly (PDC.13); no further restriction on
$z_C$ is required.

Proof. [ARH, (4.4)][ARH], the first conjunct of
[SourceTransportCentralizer, source_transport_centralizer][CENTRALIZER],
states on all finite native trees that
$\rho^2z=\langle\rho z,z\rangle$ if and only if $z=T_n$ for some
$n\in\mathbb N$. By ABC, this is exactly the condition that $B(z)$ is
primitive. Its negation is therefore precisely the other root sort.

For any finite $z$, $B(z)$ is normal. A nonnegative translation
preserves its interior normality and its root sort. Primitive tokens
are normal. Induction up an expanded named expression now leaves
exactly the explicit nodes with two primitive children; their necessary
and sufficient root conditions are (PDC.12). Nodes with a nonprimitive
child are normal once their children are normal. Applying this
argument to every name proves sufficiency and necessity. It handles
all insertion boundaries as well as all interiors.

There is no recursive normality predicate left on a free ambient code:
the residual variable is a native finite tree, and $B$ is used only
in the proof. The translated final expressions in §5 use native
pairing and $\rho$, so they are defined even on residual assignments
that fail (PDC.13). $\square$

## 5. The all-source correspondence and the full original row

**Definition 5.1 (the final native formulas).** Expand the named code
templates by $E$ after §4. Their native grammar is

$$
A::=g\mid T_{n_j+c}\mid\rho^a(z_l)\mid\langle A,A\rangle,
\qquad a,c\in\mathbb N,\quad g\in\mathcal T.
\tag{PDC.14}
$$

A fixed primitive expands to a fixed $T_a$. Include in $\Gamma$:

1. the whole translated disequality for every retained negative,
   including all old class inequalities and all off-task inequalities;
2. (PDC.13) for every nonprimitive residual.

Keep repetitions. Positive definitions have been solved by §§3–4,
and the free part by (PDC.6). Literals and both guards were settled by
the exact original cell. The domain is exactly

$$
\mathcal C=\{(\mathbf n,\mathbf z)\in
 \mathbb N^k\times\mathcal T^m:K(\mathbf n)\land
       \Gamma(\mathbf n,\mathbf z)\}.
\tag{PDC.15}
$$

In particular $\Gamma$ has no residual-positive conjunct. It is a list
of disequalities in (PDC.14), evaluated as native expressions on the
entire Cartesian product. This last interpretation also applies
outside $\mathcal C$; normal-code identities are asserted only on
the admitted domain.

**Theorem 5.2 (injective refinement of the all-source cover).** For every input
(PDC.2) and finite prefix-free original $Q$, the construction terminates
and produces finitely many domains (PDC.15), native templates $\Theta_i$,
fixed reached sets $I_i$, complete masks $M_i$ and hole templates
$H_{i,q}$ such that:

1. $\Theta_i$ is injective on $\mathcal C_i$ and its image is contained
   in $D$.
2. $D=\bigcup_i\Theta_i(\mathcal C_i)$; every original source, without
   any bound, is represented.
3. For every admitted $a\in\mathcal C_i$,
   $I_Q(\Theta_i(a))=I_i$, its mask is $M_i(a)$, and its whole subtree
   at reached $q$ is $H_{i,q}(a)$. Thus these expressions determine
   precisely the entire original $R_Q(\Theta_i(a))$.
4. Every free coordinate is recoverable from an existing named native
   expression in original frontier subtrees, followed only by the
   proved image inverse and, for a scalar, atomic-index inversion.

Empty domains and zero-dimensional products are included. Images of
different Boolean branches need not be disjoint.

Proof. For completeness, take any $u\in D$. Construction 2.2 takes its
actual cell and its unique frontier subtrees, with the entire retained
predicate true. The existing restriction in (PDC.6) recovers $w$ and
its Ext reconstructs the same original frontier assignment. Evaluate
every remaining named expression on this $w$, and apply $B$.

Choose the actual $J$ case at every occurrence. These normal named
codes satisfy all positive branch equations. Lemma 3.3 therefore
cannot reject this assignment. Lemma 3.4 factors these very codes
through their actual sink representative values, without replacing
a shape or leaf-rank function. They satisfy every fixed-rank and
all-name lower bound. Lemma 4.2 recovers the unique rebased normal
sink values. Choose their actual primitive or nonprimitive roots.
The scalar conditions hold because every actual named code is normal;
the residual sort negatives hold by Lemma 4.4. Every original whole
negative remains true on these same codes and hence on their native
expansions. The resulting tuple belongs to $\mathcal C_i$ and its
source expression expands to exactly $u$.

Conversely let $a\in\mathcal C_i$. Lemmas 4.2 and 4.4 make every
expanded named code natural and normal. Lemma 3.4 reconstructs every
positive offset, ground and $F$ definition. In a collapse branch,
the primitive flag and the two edges in (PDC.7) give exactly the
native collapse; in an ordinary branch, the reconstructed normal
output excludes collapse. Induction through the original expression
definitions therefore identifies each reconstructed name with the
actual code of its native expression. All original positives hold.
All retained negatives hold by $\Gamma$, evaluated on whole values.
The free subsystem and its same-assignment pullbacks hold by (PDC.6).

Filling the original cell now satisfies every literal, every signed
record with both guards, all old equalities and all different-class
inequalities. Its concrete exterior and absent old cut positions are
the ones in that cell. This proves membership in the complete $D$,
rather than in a positive relaxation or witness subfamily.

For injectivity, two equal reconstructed sources have equal original
frontiers at all representative addresses, hence equal $w$ by
restriction. Each sink representative is an existing name of a
deterministic native expression in $w$, so its values agree. Its code
is $\tau_{L_C}$ of the corresponding normal residual, or
$[L_C+n_C]$ for a scalar. ABC's image injectivity and atomic-index
injectivity recover equality of every coordinate. No independent
auxiliary witness survives this argument.

The source, mask and all reached-hole expressions underwent precisely
the same substitutions. Construction 2.2's recutting identities
therefore give item 3. In particular the mask still contains any uncut
residual exterior, and every partition comparison uses the original
whole hole values. Repeated classes do not become independent
coordinates. Empty, root and absent cuts retain their stated meanings.

All case lists are finite, free unification uses its existing
termination supplier, weighted closure terminates by Lemma 3.3, and
all remaining expansions and finite checks terminate. An unsatisfiable
$K\land\Gamma$ may be retained as an empty domain; no new feasibility
theorem is needed. NSF can decide such emptiness if desired. The
construction never enumerates original source sizes or ranks.
$\square$

## 6. Original finite prefixes in both directions

**Definition 6.1 (coordinate observations and constants).** For a chart
write

$$
\operatorname{coord}(\mathbf n,\mathbf z)
 =(T_{n_1},\ldots,T_{n_k},z_1,\ldots,z_m).
\tag{PDC.16}
$$

Coordinate agreement $\sim_h$ means coordinatewise native four-reply
agreement of these trees. It is not equality of integer ranks at a
finite observation depth. Let $d_i$ be the maximum length of the fixed
representative original addresses of its unbound frontier variables,
with an empty maximum zero. Let $L_i$ be the maximum rebasing constant
of its free sinks, again zero for an empty list, and put

$$
c_i=d_i+\left\lceil L_i/2\right\rceil.
\tag{PDC.17}
$$

**Theorem 6.2 (same-chart prefix correspondence).** For all
$a,b\in\mathcal C_i$ and every $h\ge0$,

$$
\begin{aligned}
\operatorname{coord}(a)\sim_h\operatorname{coord}(b)
   &\Longrightarrow \Theta_i(a)\sim_h\Theta_i(b),\\
\Theta_i(a)\sim_{h+c_i}\Theta_i(b)
   &\Longrightarrow \operatorname{coord}(a)\sim_h
                         \operatorname{coord}(b).
\end{aligned}
\tag{PDC.18}
$$

Proof. In (PDC.14), $T_{n_j+c}$ is $\rho^c(T_{n_j})$.
Consequently $\Theta_i$ is a fixed native expression in the trees
(PDC.16). [ARH, Lemma 19.2][ARH] says that pairing and fixed interpreted
powers preserve original-prefix agreement. Its strict-depth notation
is applied at $h+1$ here. This proves the first implication, including
absent replies and early leaves.

For the second, take any free sink. Its representative was a named
native expression $A_C(w)$ before weighted coordinate changes.
On the admitted domain it equals $\rho^{L_C}(z_C)$, or
$\rho^{L_C}(T_{n_C})$ in the primitive case. The original source prefix
through $h+c_i$ gives the prefix of every unbound original frontier
through $h+\lceil L_i/2\rceil$, since its representative address has
length at most $d_i$. Native expression locality gives that same
prefix of $A_C(w)$.

The image promise just stated is established by Theorem 5.2.
[SLH, Theorem 2.2][SLH] recovers every reply of its preimage at a word
$p$ from image replies at lengths at most
$|p|+\lceil L_C/2\rceil$. Thus all replies of this coordinate through
$h$ agree. Do this for every free sink. The empty-coordinate case is
vacuous. This proves the second implication using the original
four-reply meaning, not a normal-code depth metric. $\square$

The constants in (PDC.17) are proof bounds for one chart. A mathematical
inverse evaluates a supplied source, and is not an actual post-cut
operation. No bounded reply test for membership in an algebraic chart,
no cross-chart coordinate identification, and no scalar rank readout
follows from (PDC.18).

## 7. Application of the existing uniform completion theorem

**Corollary 7.1 (the consumer at its actual hypotheses).** For each
chart of Theorem 5.2, [URR, Theorem 3.1 and Corollaries 3.2–3.3][URR]
supply one finite tuple $\mathbf z_i^\star$ and an effective Presburger
formula $\Psi_i$ such that, for every $\mathbf n\in\mathbb N^{k_i}$,

$$
\begin{aligned}
\exists\mathbf z\in\mathcal T^{m_i}\quad
  K_i(\mathbf n)\land\Gamma_i(\mathbf n,\mathbf z)
&\Longleftrightarrow
  K_i(\mathbf n)\land\Gamma_i(\mathbf n,\mathbf z_i^\star)\\
&\Longleftrightarrow K_i(\mathbf n)\land\Psi_i(\mathbf n).
\end{aligned}
\tag{PDC.19}
$$

The tuple is independent of the ranks and of any later rank policy.
On the entire feasible rank set

$$
S_i=\{\mathbf n:K_i(\mathbf n)\land\Psi_i(\mathbf n)\},
\tag{PDC.20}
$$

the map $\mathbf n\mapsto(\mathbf n,\mathbf z_i^\star)$ is a section
of the rank projection of the full domain $\mathcal C_i$.
Its source image $\Theta_i(\mathbf n,\mathbf z_i^\star)$ belongs to
the complete original $D$ at every such rank.

Proof. Use URR's dimensions $k=k_i,m=m_i$ and its finite list consisting
of all pairs in $\Gamma_i$, including every sort negative (PDC.13).
Every side has exactly (PDC.14), with only fixed nonnegative offsets
and exponents. Repeated variables and repeated list members retain
their shared interpretation. URR evaluates this native list over all
$\mathcal T^{m_i}$; the producer has left no residual restriction
outside the list. Its common-completion equivalence applies at every
rank. Conjoining the independent scalar $K_i$ gives (PDC.19), with
URR's exact Presburger support. Theorem 5.2 supplies the original
source membership. Projection of the displayed section is the
identity on all of $S_i$.

For any policy $P\subseteq\{\mathbf n:K_i(\mathbf n)\}$, URR's
same-tuple quantifier exchange applies to $\Gamma_i$ on $P$.
An arbitrary policy is not claimed effectively Presburger. Empty
policies, no residuals, no ranks and empty negative lists have URR's
literal empty-product interpretations. $\square$

The section is not the full domain: no equality
$\mathcal C_i=\{(\mathbf n,\mathbf z_i^\star):\mathbf n\in S_i\}$
is claimed. It does not preserve all target rows or prefix contacts,
identify the actual source, or choose its chart. Every member of
$\mathcal C_i$ remains in the source correspondence. The injective
producer supplies this application on its canonical coordinate domains.
NIC Proposition 3.5 already supplies the analogous section for its
noninjective images; common completion, scalar projection and feasibility
remain credited to NIC, URR and NSF.

## 8. Every original opposite-row pair and the unresolved decision

**Definition 8.1 (complete pair relations).** Before any row
classification, retain for every pair of charts their entire product
$\mathcal C_i\times\mathcal C_j$ and the relations

$$
\begin{aligned}
P_{ij,h}(a,b)&\ \Longleftrightarrow\
                   \Theta_i(a)\sim_h\Theta_j(b),\\
B_{ij,h}(a,b)&\ \Longleftrightarrow\
 P_{ij,h}(a,b)\ \land\
 R_Q(\Theta_i(a))\ne R_Q(\Theta_j(b)).
\end{aligned}
\tag{PDC.21}
$$

Full row inequality uses all fields from Theorem 5.2. It includes
within-chart as well as cross-chart pairs and is never tested merely
on the sections of §7.

**Proposition 8.2 (exact pair preservation).** Every parameter pair in
$B_{ij,h}$ gives finite original sources in $D$ with equal prefixes
through $h$ and different complete rows. Conversely every such original
source pair is the image of at least one of these parameter pairs.

Proof. Soundness and the recutting identities are Theorem 5.2.
For the reverse direction apply its coverage to each of the two
original sources independently. Their actual rows and prefixes are
unchanged by reconstruction, so their parameter pair satisfies
(PDC.21). No coordinate comparison between two different charts is
needed. $\square$

**Corollary 8.3 (finite-label formulation without a stopping claim).**
Reuse [NPL, Theorem 5.3][NPL] for the exact full-row image. If it is
infinite, no finite prefix determines the row, since a fixed finite
prefix has only finitely many four-reply patterns. In the finite-image
case, for each attained row $r$ impose the complete predicate
$u\in D\land R_Q(u)=r$ and apply Theorem 5.2. Write the resulting finite
list as $(\mathcal C_i,\Theta_i,r_i)$, including all its branches.
Then

$$
\exists h\ \operatorname{PrefDet}(D,Q,h)
\ \Longleftrightarrow\
\exists h\ \forall i,j\ (r_i\ne r_j
       \ \Longrightarrow\ P_{ij,h}=\varnothing).
\tag{PDC.22}
$$

Its negation is equivalent to

$$
\exists i,j\quad r_i\ne r_j\quad\land\quad
 \forall h\ \exists a\in\mathcal C_i,\ b\in\mathcal C_j\
                     P_{ij,h}(a,b).
\tag{PDC.23}
$$

Proof. NSF's exact full-row compiler imposes each stratum with both
source directions. The strata cover exactly $D$, so Proposition 8.2
gives (PDC.22). For (PDC.23), note that $P_{ij,h+1}\subseteq P_{ij,h}$.
If every opposite-row pair had some exclusion depth, the maximum of
the finitely many depths would exclude all such pairs. Conversely a
fixed pair nonempty at every depth defeats every determining prefix.
An empty opposite-row index set makes (PDC.22) true and (PDC.23) false,
as required. $\square$

The finite quantifier argument does not construct a terminating
classifier or an effective finite description of witnesses for all
depths. Each fixed-depth query already belongs to [NSF, Theorem 6.1][NSF].
A resulting finite determining $H$ already has its paid actual static
consumer at $N$; replace $H$ by $\max(1,H)$ when a positive depth is
required. [NFO, §§3–7][NFO] supplies its separate prescribed-budget and
conditional resource interfaces. Enumerating depths or budgets gives
no general negative stop.

**Convention 8.4 (reuse of the latest depth and contact supply).**
[NLC, Theorem 4.1][NLC] already decides simultaneous minimum native
leaf-depth growth of any fixed finite native QF system and nonempty
designated output tuple. It returns EMPTY, a universal barrier, or
finite original witnesses at every requested depth. Apply it to the
original compiled predicate and actual designated expressions when
that is the required question; no new proof or replacement by a fixed
URR tuple is needed.

For a supplied finite constructor context $C$ and two supplied distinct
attained full rows $r,s$, [NLC, Lemma 5.4 and Theorem 6.1][NLC] apply
to the exact two-source predicate

$$
C[\mathbf x]\in D,\ R_Q(C[\mathbf x])=r,\qquad
C[\mathbf y]\in D,\ R_Q(C[\mathbf y])=s.
\tag{PDC.24}
$$

Their simultaneous-depth decision gives exact contact at
$C[\Omega,\ldots,\Omega]$, with original finite pairs at every depth,
or exclusion of a stratum at a finite depth. Every resulting original
pair has parameters in the complete relations (PDC.21) by
Proposition 8.2. This consumes the existing contact result without
claiming its contexts exhaust (PDC.23).

[NLC, Theorem 8.4][NLC] supplies an anchored-comb common limit outside
this context language for its specified row pair. Its Proposition 8.5
also supplies another pair in the same fiber that does have a context
certificate. Accordingly that example proves neither whole-fiber
evasion nor completeness of regular limits. Distinct finite row labels
can coalesce in the infinite limit; they must stay attached to their
finite approximants. No limit partition supplies the labels in
(PDC.21).

**Open problem 8.5 (unchanged unrestricted original target).** Decide
$\exists h\,\operatorname{PrefDet}(D,Q,h)$ on every nonempty original
signed fiber (PDC.2), with a terminating negative decision or an exact
effective finite-source countercertificate productive at every requested
depth. In the finite-image case the remaining obligation is boundedness
of all the exact relations (PDC.21), equivalently (PDC.22).

No source-size, shape, rank, sample or depth cutoff may replace those
domains. A proposed automaton or limit method still owes both
finite-source directions, all joint signed constraints and guards,
whole-row disagreement and the original-prefix correspondence.
Theorem 5.2 discharges the representation and residual-domain
obligations needed for §7; it does not discharge this further
unbounded separation obligation. No unrestricted selector, negative
stop, undecidability result or completed research programme follows.

## 9. Boundary examples on original finite sources

**Example 9.1 (feedback and the image check).** The interpreted
equation $\rho x=\langle x,\alpha\rangle$ has $x=\beta$, as already
emphasized by NSF §2 and URR §7. In (PDC.7), the right side's collapse
branch has right rank $0$, left rank $1$ and output rank $2$. It
therefore retains that source. The ordinary $F$ branch cannot retain
a cycle through a proper $F$ child, but that rejection does not reject
the separate collapse branch.

For an edge $X=\tau_1Y$, choosing $X$ as representative gives
$Y=\tau_{-1}X$. Its actual domain requires every rank of $X$ to be
at least one. A putative value $X=[0]$ cannot be repaired by treating
$\tau_{-1}$ as an everywhere-defined native operation. Definition 4.1
reads the occurrence in $Y$, even if $Y$ is absent from a designated
output, and imposes precisely this lower bound.

**Example 9.2 (a boundary cherry is not a new normal code).** The
ambient expression $F([1],[0])$ expands to
$\langle\beta,\alpha\rangle=T_2$, whose canonical code is $[2]$.
It is therefore not an admissible ordinary-branch value.
Condition (PDC.12) excludes it there, while the collapse branch
represents the same actual tree.

This matters on an entire acquired fiber, not only in syntax. Take
the old cut $\{L,R\}$ with two different classes and exterior
$\langle\square_1,\square_2\rangle$, and retain the literal
$(0,L,\beta)$. Its full fiber is exactly
$\{\langle\beta,z\rangle:z\ne\beta\}$. The member $z=\alpha$ must be
retained, but through its actual collapse case. A blanket restriction
to nonprimitive residuals would omit it. Sections 3–4 instead keep
the primitive branch and enforce normality wherever an ordinary
constructor is asserted.

**Example 9.3 (constant algebraic labels do not provide a selector).**
The following is an application of the existing atomic stability and
NSF §9 deep-prefix suppliers, not a new general negative criterion.
Set

$$
A(z)=\rho^2z,\quad B(z)=\langle\rho z,z\rangle,\quad
W(z)=\langle A(z),B(z)\rangle,\quad
U(z)=\langle W(z),z\rangle.
\tag{PDC.25}
$$

Use old cut $P=\{L,R\}$, two distinct old classes and exterior
$\langle\square_1,\square_2\rangle$. Retain literals
$(0,L,\mathsf{branch})$, $(0,LR,\mathsf{branch})$, and signed records

$$
\begin{gathered}
(0,LL,2,R,=),\quad(0,LRL,1,R,=),\\
(0,LRR,0,R,=),\quad(1,R,0,R,\ne).
\end{gathered}
\tag{PDC.26}
$$

The full acquired fiber is exactly $\{U(z):z\in\mathcal T\}$.
Indeed the old row and literals decompose any source as
$\langle\langle a,\langle c,d\rangle\rangle,z\rangle$.
The three positive records give $a=\rho^2z,c=\rho z,d=z$.
Conversely every $U(z)$ has all those reached endpoints and equalities.
The old classes differ because $W(z)$ properly contains a copy of $z$.
The last record holds by the supplied native clock
$\kappa(\rho z)=\kappa(z)+1$. These checks prove both source directions
and both guards of every sign; an authentic acquisition can hand off
at $N=2$ under Assumption 1.2.

For $Q=\{LL,LR,R\}$ the full exterior is
$\langle\langle\square_1,\square_2\rangle,\square_3\rangle$.
The hole values are $A(z),B(z),z$. The first differs from $z$ by the
clock, and the second differs from $z$ by proper containment.
The first two are equal exactly when $z$ is atomic. Thus the entire
row image consists of the two partitions
$\{\{1,2\},\{3\}\}$ and $\{\{1\},\{2\},\{3\}\}$, with the same reached
set and complete exterior.

Let $C_1=\langle\alpha,\alpha\rangle$ and, for each $h$, put
$t=2h+2$. The two finite members

$$
U(T_t),\qquad U(\rho^tC_1)
\tag{PDC.27}
$$

have these different rows: $B(C_1)=F([0],[0])$ is nonprimitive and
translation preserves that fact. The native template $U$ commutes
with $\rho$. By [NSF, Lemma 9.2][NSF], every source shifted $2h+2$
times has branch replies through inclusive depth $h$. Hence (PDC.27)
has equal original prefixes through $h$.

Each row stratum has a constant label, yet their original finite
counterpairs exist for every $h$. Calling the algebraic label an
available observation would therefore give a false recovery result.
The full relations (PDC.21) retain these pairs; the correspondence
and common completion assert no such selector.

## 10. Supplier correspondence and evidence limits

**References 10.1 (allocation of the mathematical content).**

| Source | Exact supplied interface and boundary |
| --- | --- |
| [ABC, Theorems 2.2–2.3 and 4.2][ABC] | Normal coding and expansion on all finite native trees, exact translation images and mask/exterior correspondence. Integer translations outside those images are auxiliary algebra only. |
| [NativeGroundSolutionSpace][NGSS] | solutionEquiv and constrainedEquiv use the same Ext and the full complement of the original bound keys. The arbitrary predicate $G$ remains a predicate; it is not already a Cartesian residual normalizer. |
| [NativeUnificationCore][NUC], [NativeTermUnification][NTU], [NativeSubstitution][NSUB], [UnificationCompleteness][UC] | Exact Boolean/pair syntax, native encoding/decoding support, terminating free unification, substitution laws, soundness, MGU absorption and completeness. No free unary symbol models interpreted $\rho$. |
| [SourceTransportCentralizer][CENTRALIZER], first conjunct of source_transport_centralizer; [ARH, (4.4)][ARH] | $\rho^2z=\langle\rho z,z\rangle$ characterizes exactly the atomic orbit; its negation is the residual root-sort test. |
| [NSF, §§2–5][NSF] | Exact named collapse reduction, feasibility, scalar projection and fixed guarded navigation. Marker witnesses are not all-source coordinates. |
| [NIC, Theorems 3.2–3.3 and 4.3, Proposition 3.5][NIC] | Arbitrary-positive full native image cover, signed whole-source pullback and its Cartesian URR section. Its images need not be injective; this volume retains normal named values and proves the coordinate-prefix inverse. |
| [ARH, §§19–20][ARH] | Exact original constructor cells, observable original frontier addresses, native locality and its restricted constructor elimination. Its synchronous consumer still requires the actual synchronous residual hypotheses. |
| [ARH, §§4–6 and 10–18][ARH]; [NSF, §§9–10][NSF] | Existing root-certificate, synchronous, forward-closed and invariant-chart criteria at their own hypotheses. Failure of recognition is not a negative answer to the general task. |
| [SLH, Theorem 2.2][SLH] | Four-reply recovery on a certified $\rho^L$ image, with support length $|p|+\lceil L/2\rceil$. Used only after the exact image promise is proved. |
| [URR, Theorem 3.1 and Corollaries 3.2–3.3][URR] | Uniform equality reflection, one common residual tuple and policy-uniform completion on the full Cartesian native carrier. Its §§4–5 previously supply a specified feedback/packing producer. |
| [NPL, Theorem 5.3 and §10][NPL] | Exact complete-row image and the remaining full-row prefix-separation question. A finite image has no free selector. |
| [NFO, §§3–7 and §8][NFO] | Prescribed-budget decisions, finite-source obstructions at such budgets and conditional resource optimization. No terminating outer existential follows. |
| [NLC, Lemma 2.2, Theorems 4.1 and 6.1, §§8–9][NLC] | All-source branch factorization, simultaneous minimum-depth decision and supplied-context contact. Its anchored-comb limitation is for a specified row pair; finite labels can coalesce at a limit. |
| [TPO, Definition 1.2 and Corollaries 4.2–4.4][TPO] | No uniform native-normality or total canonicalization graph in its exact ambient term-power language. Here residuals range over native trees, so no such ambient-language definition is asserted. |

The repository overlap comparison is bounded to these owning sources
and their indicated interfaces. Their source statements are evidence
of the interfaces used, not a claim of a newly compiled application.
The weighted whole-code expansion, all-name rebasing and normality
discharge in §§3–5 give the repo-derived injective refinement and its
coordinate-prefix correspondence. The full-image and URR-section
conclusions also have the existing NIC derivation. No claim of
external priority or literature-wide absence accompanies them.

The free-term literature discussed by NSF, URR and NLC supplies context
for syntactic unification and disequality separation. No theorem about
an unrestricted equational theory or a term-power interpretation is
imported here by name. In particular the actual native feedback in
Example 9.1 prevents that shortcut. Feasibility, marker separation,
minimum-depth decisions, common completion and fixed-budget suppliers
retain their own authorship and scope.

**Convention 10.2 (verification and unresolved boundary).** Document
structure checks do not verify these proofs in Lean. The volume adds
ordinary theory only. The complete source domain is (PDC.2), the exact
new consumer domain is (PDC.15), and the still-unresolved general
decision is Open problem 8.5. No mathematical choice of coordinates
adds an actual operation or information to the retained observer.

[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[NFO]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FINITE_OBSTRUCTION.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[NGSS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.lean
[NUC]: ../../../D5/S0/Rewriting/NativeUnificationCore.lean
[NTU]: ../../../D5/S0/Rewriting/NativeTermUnification.lean
[NSUB]: ../../../D5/S0/Rewriting/NativeSubstitution.lean
[UC]: ../../../D5/S0/Rewriting/UnificationCompleteness.lean
[CENTRALIZER]: ../../../D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean

## 追加锚（本行以下为增补区）

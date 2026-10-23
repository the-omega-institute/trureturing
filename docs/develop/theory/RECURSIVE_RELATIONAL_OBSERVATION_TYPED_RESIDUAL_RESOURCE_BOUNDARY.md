# Recursive relational observation: typed residual resource boundaries

This volume isolates a boundary that remembers both future behavior and the
resources charged by a continuation.  The object is a typed partial process on
one actual common source.  A boundary is therefore a quotient of an actual
reachable image, with legal actions, failures, selectors, archives, clocks,
and resource responses included in its declared observation contract.

The construction combines [Boundary Dynamics](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md),
especially §§19--21 and §§26--27, with [Transport--Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md),
§§2.1, 2.17--2.20 and 3--4.  [Serial Joint Resource Frontier](RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md),
§§1, 5, 7 and 8 supplies the distinction between uniform, Pareto and weighted
resource objectives.  [Uniform Descriptor Boundary](RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_DESCRIPTOR_BOUNDARY.md),
§§4--7 supplies source-independent descriptor and factorization conditions.
The typed residual and ordered-path boundary is related to [Typed Residual
Cocycle Reconstruction](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md),
§§1--6, and the four-view conditions use [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md),
§§27--34.  The symbols $\alpha,\beta$ below are read through
[Fibonacci Atomic Relation Generation](FIBONACCI_ATOMIC_RELATION_GENERATION.md),
§§2--5 and §21.

The definitions and proofs here are ordinary mathematics at the stated
interfaces.  They add no Lean declaration or kernel verification, and they do
not assert a physical realization or a universal Fibonacci law.

## 1. One actual source and a typed partial process

**Definition 1.1 (actual common source).**  Let $\Omega$ be a set of
actual jointly generated source instances and let

$$
s:\Omega\longrightarrow S
$$

be the source map.  The working state is the actual image
$X=\operatorname{im}(s)$.  A declared forward-closed reachable carrier
$X_{\rm reach}\subseteq X$ may be used; whenever $X_{\rm reach}$ is written
below, all operations are required to preserve that carrier.  If no smaller
carrier is declared, set $X_{\rm reach}=X$.  A product such as an archive coordinate times a clock coordinate
is only notation for components of $s(\omega)$; independently realizable
coordinates may not be joined without a common $\omega$.  Every quantifier
below is over this one source and its actual reachable image.

Let $I$ be a set of interface types and $\kappa:X\to I$ the type map.
An action name $a$ has source type $i(a)$, target type $j(a)$, a
partial legal domain $D_a\subseteq X_{i(a)}$, and a successor

$$
T_a:D_a\longrightarrow X_{j(a)}.
$$

For a compatible word $u=a_1\cdots a_n$, write
$i(u)=i(a_1)$, $j(u)=j(a_n)$, and define its partial successor by
$T_\varepsilon=\mathrm{id}$ and
$T_{ua}=T_a\circ T_u$ on the states where every prefix is legal.  The same
word-composition convention is used for typed meter transports and charges.
Legal failures with declared successors are included in these partial
compositions.

Its complete one-step response is a typed record

$$
\operatorname{step}_a(x)=
\bigl(\mathsf{status},\mathsf{event},\mathsf{out},
       \mathsf{failure},\mathsf{record},\mathsf{clock},\mathsf{meter}\bigr).
\tag{1.1}
$$

The status distinguishes legal success, a legal executed failure with a
declared successor, and an illegal operation with no successor.  The record
contains every field declared observable by the task, including a selector
decision when the observer chooses the next name.  A legal failure is not
silently replaced by an illegal edge, and an absent operation is not an
executed failure.

**Definition 1.2 (typed action words and complete continuation trace).**  A
finite word $u=a_1\cdots a_n$ is type compatible when the target type of
each action is the source type of the next.  Fix a declared final-state
projection $\operatorname{fin}$; it may be the constant symbol
$\bot$, or any task-visible projection, but it is not the hidden full state.
Set $\operatorname{fin}(\bot)=\bot$.  Starting at $x$, execute the word
until the first missing or illegal action; if no successor exists, the final
field below is this explicit $\bot$ value.
For an initialized meter $m$ in the source type, write

$$
\operatorname{Trace}_m(x,u)=
  (\text{initial type},\text{ordered names},\text{types},\text{statuses},
   \text{events},\text{outputs},\text{failure reasons},
   \text{records},\text{clock labels},\text{meter updates},
   \operatorname{fin}(\text{final state or }\bot)).
\tag{1.2}
$$

The unmarked notation is the identity-meter trace:

$$
\operatorname{Trace}(x,u)=\operatorname{Trace}_{e_{\kappa(x)}}(x,u).
$$

When the next name fails a type or namespace check, the trace contains an
explicit illegal-token outcome, so such a word can still be included in a
test family even though no successor is taken.

The trace retains a legal failure, an illegal attempt, normal termination and
the empty word as different values whenever the contract distinguishes them.
The **complete continuation profile** is

$$
\Phi_{\mathcal U}(x):\mathcal U\longrightarrow\mathcal L,
\qquad
\Phi_{\mathcal U}(x)(u)=\operatorname{Trace}(x,u),
\tag{1.3}
$$

for a declared family $\mathcal U$ of finite typed tests.  A test may
carry an explicit illegal or missing-action token when the contract observes
that outcome.  If a controller is part of the task, $\mathcal U$ also
contains the words that can be produced by its selector.  A current readout
without the complete
continuation trace is not yet a residual resource boundary.

**Definition 1.3 (resource response).** Let $(M,\oplus,e)$ be a declared
resource monoid, or a typed family of monoids $M_i$ with transport maps
along action types.  The meter component in (1.1) is a value in the relevant
monoid and has a declared unit.  It may count reads, updates, literal length,
memory allocation, clock ticks, archive writes, or any vector of such
coordinates.  A resource response is part of $\mathcal L$, not an
after-the-fact annotation.  If the resource is a vector, equality in (1.3)
is componentwise according to the task contract.

## 2. The resource-aware coarsest right congruence

**Definition 2.1 (resource-aware future relation).** For $x,y\in X$, put

Here and below, the trace is the one belonging to the selected resource
contract: the fresh contract uses the identity-meter trace, while the
inherited contract uses the current-meter trace on $(x,m)$.  The two carriers
are not silently identified.

$$
x\equiv_{\mathcal U}^{\rm res}y
\quad\Longleftrightarrow\quad
\Phi_{\mathcal U}(x)=\Phi_{\mathcal U}(y).
\tag{2.1}
$$

Equality includes every declared resource response, action name and order,
legality and failure label, selector-visible record, clock value and archive
field.  It is only a relation on the actual image $X$, and only for the
declared test family $\mathcal U$.

**Definition 2.2 (right congruence and forward invariance).** A relation
$R\subseteq X\times X$ is a typed right congruence for $\mathcal U$ when
it relates only equal types and, for every allowed action $a$,

1. related states agree on whether $a$ is illegal, legally failing or
   successful, and agree on all one-step response fields;
2. whenever $a$ has a successor on both sides, their successors are again
   related:
   $xRy\land x,y\in D_a\Rightarrow T_a(x)R T_a(y)$;
3. the selector and its namespace choice factor through the relation whenever
   they are part of the task.

The relation is **forward invariant** when the second condition holds for all
reachable action steps, including legal failure successors.

**Theorem 2.3 (coarsest right congruence on the declared image).** Assume
that $\varepsilon\in\mathcal U$, every one-step word allowed by the declared
menu is in $\mathcal U$, and $\mathcal U$ is prefix-closed and closed
under appending every action that the contract allows after a tested prefix
(including the continuations after a legal failure).  If a selector or
namespace allocator is part of the task, its decision (or distribution) must
also be included in each trace or assumed to factor through the profile.
Then $\equiv_{\mathcal U}^{\rm res}$ is a typed right congruence and is
the largest relation whose classes have a
well-defined complete response profile.  Equivalently, if $R$ is any
response-preserving forward-invariant equivalence relation on $X$, then

$$
R\subseteq\equiv_{\mathcal U}^{\rm res}.
\tag{2.2}
$$

Thus $X/\equiv_{\mathcal U}^{\rm res}$ is the coarsest resource-aware
right quotient for this task.  In the order of inclusion on relations it is
also the **maximum response-preserving forward-invariant relation** on the
declared image: every other admissible forward relation is contained in it.

**Proof sketch.**  Equality of profiles gives equality for the empty word and
for every one-step word, hence equal types, legality, labels and meter
responses.  For a legal first action $a$, equality of the profiles on all
words $av$ gives equality of the successor profiles on every continuation
$v$; this is forward invariance.  If $R$ preserves every declared
response, two $R$-related states have equal value on each $u\in\mathcal U$,
so they are related by (2.1), proving (2.2).  The argument is a factorization
argument on the actual image; it does not construct a quotient for sources
outside $X$. $\square$

The word **minimal** in this theorem is relative to the declared task,
resource coordinates and reachable image.  It does not mean minimal for all
possible future experiments, all hidden physical variables or every source
fiber.  It also does not imply that the quotient is finite: an ordered archive,
an unbounded clock or a fresh namespace can make infinitely many residual
classes even when each individual step has a finite table.

**Corollary 2.4 (boundary factorization).** Let $q:X\to B$ be a proposed
boundary.  It is dynamically sufficient for $\mathcal U$ exactly when
there are induced legal domains, response maps and successors on
$q(X)$ such that

$$
\operatorname{Trace}(x,u)=\overline{\operatorname{Trace}}(q(x),u)
\quad\text{for all }x\in X,u\in\mathcal U.
\tag{2.3}
$$

The coarsest such boundary is obtained by the quotient map
$x\mapsto[x]_{\equiv_{\mathcal U}^{\rm res}}$.  If $q:X\to B$ is any
other sufficient boundary, then its kernel is contained in the profile
kernel and the profile map factors through $q$; equivalently, the quotient
map is a coarsening of every other exact representation.  A finer
representation need not factor through the coarsest one.

**Definition 2.5 (initial profile and stable residual core).** A weaker task
may expose ordinary continuation responses and an aggregate resource total at
the initial cut, while exposing a fresh resource response only after a later
cut.  Let $\operatorname{Ord}(x,u)$ omit that fresh resource field and let
$A_x(u)$ be the aggregate total measured from the initial cut.  Define
Here “initial cut” is relative to the state being tested: after a prefix $p$,
$A_{T_px}(v)$ is the aggregate profile re-formed at that successor cut under
the declared meter contract.  Thus a fresh response that was hidden inside a
total from $x$ can become an observable component when $T_px$ is tested as a
new boundary state.

$$
xK_0y\quad\Longleftrightarrow\quad
\forall u\in\mathcal U,
\ \operatorname{Ord}(x,u)=\operatorname{Ord}(y,u)
\ \land A_x(u)=A_y(u).
$$

On the same actual reachable carrier let
$\mathcal U_{\rm com}(x,y)$ be the tested prefixes legal from both states;
$\varepsilon$ is included because it is always common.  Define

$$
xKy\quad\Longleftrightarrow\quad
xK_0y\ \land\ \forall p\in\mathcal U_{\rm com}(x,y),\quad
K_0(T_px,T_py).
$$

A legal failure with a declared successor is included among the common legal
prefixes.  If a tested prefix is legal on only one side, $xK_0y$ already fails
because its ordinary response contains the unequal legality, so no undefined
successor is formed.

**Theorem 2.6 (stable-core theorem).** Assume the declared action family is
closed under all finite legal continuations, with explicit illegal outcomes,
that $\varepsilon\in\mathcal U$, and that the tested family is prefix-closed
and contains every legal suffix after a tested prefix.  Assume also that
$K_0$ is an equivalence on the actual reachable carrier.  Then $K$
is the largest forward-invariant equivalence relation contained in $K_0$.
Consequently, the quotient by $K$ is the coarsest exact boundary for the
mixed task in which ordinary responses, initial aggregate totals and all
later fresh responses must be preserved.  Any finer autonomous exact
realization whose kernel is contained in $K$ has a canonical surjection onto
this quotient.  Static
factorization of a trace table alone does not imply that the finer
representation has a well-defined autonomous update.

**Proof sketch.** Reflexivity, symmetry and transitivity follow pointwise
from the corresponding properties of $K_0$.  If $xKy$ and $a$ is a common
legal first action, every legal continuation $p$ after $a$ gives
$K_0(T_{ap}x,T_{ap}y)$, so $T_ax\,K\,T_ay$; the first-step response is the
$p=\varepsilon$ case.  If $R$ is any forward-invariant equivalence contained
in $K_0$, induction over a legal prefix gives $R\subseteq K$, proving
maximality.  The quotient statement is the universal property of the
largest admissible identification.

**Corollary 2.7 (cancellation shortcut).** Let $F_z(v)$ denote the fresh
suffix-cost component of the declared response from residual state $z$.
Let $\sigma_{x,p}$ and $\oplus_{x,p}$ be the separately declared transport
and combination map from that fresh suffix response into the aggregate type
at the cut $x$.  Suppose the aggregate and fresh costs satisfy the typed
cocycle

$$
A_x(pv)=A_x(p)\mathbin{\oplus_{x,p}}
\sigma_{x,p}\!\left(F_{T_px}(v)\right),
$$

and, on attainable states, left cancellation (or injectivity of
$r\mapsto a\oplus_{x,p}\sigma_{x,p}(r)$) holds for the common prefix value
$a=A_x(p)=A_y(p)$.  In addition, the combination and transport maps are
contract-global, or factor through $K_0$ (so $K_0$-related $x,y$ have the same
$\sigma_{x,p}$ and $\oplus_{x,p}$).  Then $K_0$ is already forward
invariant, so $K_0=K$.
This is sufficient, not necessary: a particular noncancellative system may
still satisfy $K_0=K$ for other reasons.

## 3. Two continuation contracts for resources

The same symbol “continuation cost” can mean two different interfaces. They
must be declared before a quotient or a cancellation statement is used.

**Definition 3.1 (fresh-suffix contract).** A fresh-suffix contract measures a
continuation from the identity meter.  For a legal prefix $u$ with
$T_u x$ defined and a suffix $v$, the suffix response is evaluated from
the residual state $T_u x$ with the identity meter
$e_{\kappa(T_u x)}$ of its target type:

$$
\operatorname{FreshResp}(x;u,v)=
\operatorname{Trace}_{e_{\kappa(T_u x)}}(T_u x,v).
\tag{3.1}
$$

If a total price is required, a separately declared combination law must state
how the two typed values are combined.  In a single monoid it may take the
simple form

$$
\operatorname{price}_x(uv)=\operatorname{price}_x(u)\oplus
                         \operatorname{price}_{\rm fresh}(T_u x,v),
\tag{3.2}
$$

while a typed family uses an explicitly declared typed combination map in
place of $\oplus$.  The source subscript matters when the charge depends on
the actual inherited configuration; no untyped transport is implicit.

The suffix itself does not inherit the prefix meter. This contract is useful
for comparing independent continuation budgets and for constructing a static
descriptor table.

**Definition 3.2 (inherited-meter contract).** In an inherited-meter
contract, the meter is part of the same actual joint source.  If
$m_0(\omega)\in M_{\kappa(s(\omega))}$ is its initialized value, define

$$
\widehat s_0(\omega)=(s(\omega),m_0(\omega)),
\qquad
\widehat X_0=\operatorname{im}(\widehat s_0)\cap
\{(x,m):x\in X_{\rm reach},\ m\in M_{\kappa(x)}\}.
$$

Let $\widehat X_{\rm reach}$ be the least subset containing
$\widehat X_0$ and closed under every declared inherited transition on
actual legal trajectories, including legal-failure successors.  Thus every updated meter remains tied to the same
source trajectory, while an arbitrary Cartesian product of independently
chosen meters is not admitted.  The resource carrier in this contract is
$\widehat X_{\rm reach}$.
Lift the type map by $\widehat\kappa(x,m)=\kappa(x)$, and write
$\widehat D_a\subseteq\widehat X_{\rm reach}$ for the actual inherited
legal domain; it may depend on $m$.
All typed action and selector statements on the inherited carrier use
$\widehat\kappa$ and these lifted domains.
The boundary state contains the current meter $m$, and a typed action
updates it in place:

$$
(x,m)\xrightarrow{u}\bigl(T_u x,\tau_u(m)\oplus_{j(u)}c_{x,m}(u)\bigr),
\tag{3.3}
$$

where $T_u$, $\tau_u$ and $c_{x,m}(u)$ denote the composition of the declared
one-step inherited transitions.  For a typed family, the transports are
coherent:

$$
\tau_\varepsilon=\mathrm{id},\qquad
\tau_{uv}=\tau_v\circ\tau_u,
$$

with the corresponding typed composition law for the charges.  In a single
monoid, $\tau_u$ is the identity.  Later legality, selector choices or
outputs may depend on the inherited value.  The resource-aware profile for
this contract is therefore formed on $\widehat X_{\rm reach}$, not merely on
$X$.

For this inherited carrier, define the contract trace by

$$
\widehat{\operatorname{Trace}}((x,m),u):=\operatorname{Trace}_m(x,u).
$$

Thus the current meter is read from the actual joint state and is not reset
to the identity.  For a fresh-suffix carrier, the contract trace is the
identity-meter trace from Definition 1.2.  From this point on, every
unmarked profile, kernel or view is interpreted using the contract trace
appropriate to $X_{\mathsf C}$; in particular, inherited occurrences of
$\operatorname{Trace}(x,u)$ mean
$\widehat{\operatorname{Trace}}((x,m),u)$.

**Proposition 3.3 (the contracts are not interchangeable).** If a selector,
legality predicate or failure response can inspect the inherited meter, a
fresh-suffix boundary can be dynamically sufficient only after the meter is
added to the boundary or proved irrelevant. Conversely, an inherited-meter
quotient can be replaced by fresh suffix costs only under an explicit
factorization hypothesis: every inherited response and legality decision must
be a function of the fresh residual state and the declared combination law
(3.2) for every reachable prefix. The equation is sufficient for that
replacement, not a necessary form for every possible encoding.

**Proof sketch.**  Choose two prefixes with the same residual state but
different meters and an action whose legality threshold is between them.  The
fresh suffixes are equal while the inherited traces differ.  For the converse,
choose a continuation whose charge depends on the previous meter; resetting to
$e$ changes the selector or response.  These are finite source-level
counterexamples and do not require a physical clock interpretation. $\square$

The weighted continuation discussion in [Transport--Memory Completion
§2.17](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) uses
the same distinction between a task-relative suffix and a memory that is
carried into the next task.  A resource boundary must state which contract is
being used.  From this point on, write $X_{\mathsf C}$ for the actual
contract carrier: $X_{\mathsf C}=X_{\rm reach}$ for a fresh-suffix contract,
and $X_{\mathsf C}=\widehat X_{\rm reach}$ for an inherited-meter contract.
Every profile, kernel, controller and view below is formed on
$X_{\mathsf C}$; the symbol $X$ in those formulas abbreviates this
carrier.

## 4. Cancellation and finite-state order counterexamples

**Definition 4.1 (left and right cancellation).** In a possibly
noncommutative meter operation $\odot$, left cancellation means

$$
a\odot b=a\odot c\Longrightarrow b=c,
\tag{4.1}
$$

and right cancellation means

$$
b\odot a=c\odot a\Longrightarrow b=c.
\tag{4.2}
$$

If a known prefix meter is on the left of a total inherited meter, left
cancellation recovers a unique unknown suffix charge.  If a known suffix
meter is on the right, right cancellation recovers the unknown prefix charge.
In a commutative
cancellative monoid the distinction disappears algebraically, but the
prefix/suffix position still matters for the trace and selector.  Cancellation
recovers a meter value; it does not by itself recover the order of action
names.

**Finite table 4.2 (max and Boolean-or lose order).**  Consider one state
$q$, two typed self-actions, and the following complete one-step table.

| word | ordered trace | max meter | Boolean meter |
| --- | --- | ---: | --- |
| $\varepsilon$ | empty | $0$ | $0$ |
| $a$ | $A$ | $2$ | $1$ |
| $b$ | $B$ | $3$ | $0$ |
| $ab$ | $AB$ | $3$ | $1$ |
| $ba$ | $BA$ | $3$ | $1$ |

Both actions return to $q$; the displayed trace is part of the declared
response.  The words $ab$ and $ba$ are distinct legal histories, but
their max and Boolean-$\lor$ summaries coincide.  This table demonstrates
loss of order by a summary; it does not by itself exhibit two distinct hidden
states.  Max is neither left nor right cancellative: $\max(5,1)=\max(5,4)$.  Boolean-or is likewise
noncancellative: $1\lor0=1\lor1$.  A boundary retaining only either
summary merges the two histories and cannot support an ordered continuation
task.  Even addition, which is cancellative on $\mathbb N$, remains
commutative and therefore does not encode the order of two return blocks; an
ordered archive or an order-sensitive action record is still required.

**Finite countermodel 4.3 (equal total max, unequal fresh suffix).**  Let
$x,y$ have the same type and the same current observations.  The legal words
from either are exactly $\varepsilon$, $a$ and $ab$, with

$$
 x\xrightarrow{a/1}u\xrightarrow{b/0}z,
 \qquad
 y\xrightarrow{a/1}v\xrightarrow{b/1}z',
$$

and all other attempts illegal with the same declared label.  Under the
max-meter total profile, both $x$ and $y$ report $0,1,1$ on
$\varepsilon,a,ab$.  Their successors $u,v$, however, report fresh suffix
costs $0$ and $1$ on $b$; thus $b$ is initial-illegal but successor-legal.
A boundary that stores only the total max profile therefore merges $x,y$ while
failing to define the next fresh
resource response.  The same construction works with Boolean-or or a
saturated counter.  If the action contract exposes the raw charge, or if
budget legality distinguishes it, the states are already separated; the
example targets the weaker aggregate-only contract.

**Proposition 4.4 (what cancellation can and cannot prove).** Suppose a
continuation contract has a cancellative meter and the boundary retains the
relevant prefix and total values.  Then a suffix meter is uniquely determined
in the appropriate cancellation direction.  If the meter is max, Boolean-
$\lor$, a saturated counter or another noncancellative summary, equal total
meters need not imply equal suffix meters.  In either case no conclusion about
the action order follows unless the trace kernel itself separates ordered
words.

**Proof sketch.** Apply (4.1) or (4.2) to the equality of total meters.  The
finite table and the finite countermodel give witnesses for cancellation
failure and for order loss.  The final statement follows because two distinct
ordered words can have the same multiset and the same additive or idempotent
summary. \square

This is the resource version of the return-block obstruction in [Typed
Residual Cocycle Reconstruction §3](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md):
a descended additive cocycle can account for a path, while a commutative
summary cannot in general reconstruct the path order.

## 5. Action-order closure and the mixed kernel

Fix a finite menu $\mathcal M$ of action names, including namespace and
type.  The menu is part of the task; enlarging it changes the theorem.

**Definition 5.1 (future and mixed kernels).** A one-step future kernel
records the response vector of the fixed menu:

$$
K_{\rm fut}(x)=\bigl(\operatorname{step}_a(x)\bigr)_{a\in\mathcal M}.
\tag{5.1}
$$

Let $\mathcal W_{\mathcal M}$ be the family of type-compatible words over
$\mathcal M$, together with explicit illegal traces for words that fail a
type or namespace check.  The **mixed action kernel** records every such
word:

$$
K_{\rm mix}(x)(u)=\operatorname{Trace}(x,u),
\qquad u\in\mathcal W_{\mathcal M}.
\tag{5.2}
$$

For a deterministic adaptive selector, its response tree contributes the
words generated by earlier responses.  A randomized or nondeterministic
selector requires the corresponding branching or distributional trace
contract.  The menu must include every namespace token reachable under the
contract; a fixed finite menu does not silently cover unbounded fresh
allocation.  When a closed-loop selector or allocator is part of the task,
append its decision/distribution and namespace choice to the trace, or require
as an explicit hypothesis that these maps factor through $K_{\rm mix}$.

The action-order issue is the same fixed-menu leakage isolated in
[Fibonacci relational fiber calculus, Continuation II §44](https://github.com/the-omega-institute/trureturing/blob/39f372d1ed54a8acc3e2ef8452bd011a662f48d4/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md) at `origin/dev`: equality of a per-action table does not imply equality under all permitted orders.  That reference is used here only for a fixed menu and does not supply a theorem for an enlarged or moving menu.

**Theorem 5.2 (mixed-kernel criterion).** Let
$R=\ker(K_{\rm mix})$ on the actual image, with the selector and
namespace maps included in the trace or assumed to factor through it.  Then
$R$ is a typed right congruence closed under
every finite action order from $\mathcal M$, including resource and
failure responses.  More generally, for an arbitrary relation $R$, the
premise

$$
xRy\Longrightarrow K_{\rm mix}(x)=K_{\rm mix}(y)
\tag{5.3}
$$

only gives observational soundness, namely $R\subseteq\ker(K_{\rm mix})$.
An autonomous quotient also requires $R$ to be an equivalence and its
successor, legality, selector and namespace maps to be well defined; this
forward-closure condition must be imposed separately unless $R=\ker(K_{\rm
mix})$.  If (5.3) fails for a pair that a proposed boundary merges, some
fixed-menu word distinguishes the pair and the boundary is not sufficient for
the corresponding continuation task.

**Proof sketch.** For $R=\ker(K_{\rm mix})$, take a word $av$.  Equality
of its complete trace and of the common first response leaves equal mixed
profiles for the successors after $a$, so the kernel is forward closed.
For the converse, choose a distinguishing word $u$; its response is a
permitted observation, so a boundary merging the pair is unsound.  The finite
countermodel in §4.3 shows why a weaker aggregate kernel does not supply this
closure; the one-state table in §4.2 only illustrates order loss inside a
single history. $\square$

Thus an action-order proof must close under $K_{\rm mix}$, not merely under
the coordinatewise future table.  A result proved for a fixed $\mathcal M$
does not silently quantify over fresh action names.

## 6. Uniform controllers, Pareto resources and weighted resources

**Definition 6.1 (uniform controller).** A controller is a typed tuple

$$
\Pi=(\mathsf{sel},\mathsf{upd},\mathsf{halt},\mathsf{emit},\mathsf{ns}),
$$

where `sel` chooses a legal namespaced action from the accessible boundary,
`upd` updates the inherited memory and meter, `halt` is a declared terminal
condition, `emit` produces the task output, and `ns` allocates fresh names
according to the namespace contract.  For a target map
$Q:X_{\mathsf C}\to Y$, define the pointwise predicate

$$
\operatorname{Correct}(\Pi,Q,x)
\;:\Longleftrightarrow\;
\Pi\text{ terminates on }x\text{ and emits }Q(x).
$$

Then

$$
\operatorname{Correct}(\Pi,Q)
\;:\Longleftrightarrow\;
\forall x\in X_{\mathsf C},\operatorname{Correct}(\Pi,Q,x).
\tag{6.1}
$$

The uniform synthesis statement has the quantifier order

$$
\boxed{\exists\Pi\;\operatorname{Correct}(\Pi,Q).}
\tag{6.2}
$$

It is not the weaker statement $\forall x\,\exists\Pi_x$, which permits a
different controller for every source.

Let the actual run resource be $c_\Pi(x)\in[0,\infty]^k$, where a
nonterminating run has an infinite coordinate and therefore cannot satisfy
$\operatorname{Correct}$.  For a uniform budget vector
$b\in[0,\infty]^k$, feasibility is

$$
\exists\Pi\;\operatorname{Correct}(\Pi,Q)\land
\forall x\in X_{\mathsf C}\quad c_\Pi(x)\le b.
\tag{6.3}
$$

Put $B(\Pi)=(\sup_{x\in X_{\mathsf C}}c_{\Pi,r}(x))_r$.  The Pareto order
is the coordinatewise order on $B(\Pi)$.  For a nonnegative rational weight
vector $\lambda$, use the extended-real convention $0\cdot\infty=0$ and
define

$$
W_\lambda(\Pi)=\sup_{x\in X_{\mathsf C}}
      \lambda\mathbin{\cdot}c_\Pi(x),
\qquad
W_\lambda^*=\inf_{\Pi:\operatorname{Correct}(\Pi,Q)}W_\lambda(\Pi).
\tag{6.4}
$$

The infimum need not be attained.  In general
$W_\lambda(\Pi)\ne\lambda\cdot B(\Pi)$: the supremum is taken after the
per-source weighted sum.  On two sources with costs $(1,0)$ and $(0,1)$,
$B(\Pi)=(1,1)$, while the weight $(1,1)$ has worst-run value $1$, not
$2$.

**Theorem 6.2 (uniform resource separation).** A controller satisfying
(6.2) may have a finite Pareto basis while a chosen weighted objective selects
a different controller.  A Pareto point need not minimize any strictly
positive weighted objective: the finite set
$\{(0,3),(1,2),(2,0)\}$ has middle point Pareto-minimal but unsupported by
positive weights.  Indeed, support by positive weights would require both
$\lambda_1+2\lambda_2\le3\lambda_2$ and
$\lambda_1+2\lambda_2\le2\lambda_1$, hence both
$\lambda_1\le\lambda_2$ and $2\lambda_2\le\lambda_1$, which is
impossible.  If zero weights are allowed, a weighted minimizer may also be
chosen from a non-Pareto tie because the ignored coordinate is not priced.

**Proof sketch.** Varying $\lambda$ changes which tradeoff is preferred, and
coordinatewise maxima may occur on different runs.  These are the distinctions
proved operationally in [Serial Joint Resource Frontier §§5 and 7](RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md).
They do not alter the uniform quantifier in (6.2). $\square$

## 7. The abstract carriers $\alpha$ and $\beta$

Let $A_0=\{\alpha,\beta\}$ be a typed set of atomic carriers.  A source
may be generated by ordered pairing $\langle x,y\rangle$, a successor or
transport operation $\rho$, and a declared observation of the resulting
relation.  The names $\alpha,\beta$ are labels in this carrier; they are
not numerical values, universal particles, or pre-existing spacetime points.

The Fibonacci Atomic Relation Generation volume (§§2--5) supplies examples
where a pair of atomic observations and a replacement law generate a count
or a recurrence.  Its §21 relation ports explain how ordered constructors
and records enter a boundary task.  Those statements are scoped to their
declared relation and observation maps.

**Proposition 7.1 (carrier interpretation).** A type-preserving relabeling
isomorphism of the atomic carrier, together with transported constructors,
legal actions and response maps, leaves Definitions 1--6 unchanged.  Merely
choosing two distinct symbols does not preserve a task automatically.  A
Fibonacci sequence appears only after an additional recurrence and counting
map are specified.

**Proof sketch.** The residual quotient uses types, traces and action
responses, not the spelling of atom labels.  A recurrence is extra structure
on the generated source, so it cannot be inferred from two labels alone.
Likewise, a physical spacetime interpretation requires a separately supplied
metric, clock, causal law and acquisition contract.  $\square$

Consequently this volume does not claim a universal Fibonacci geometry, a
physical time coordinate, or a physical realization of $\alpha$ and
$\beta$.  They are abstract atoms that can instantiate the typed residual
interfaces.

## 8. Four representations and their transport kernels

Let the same actual contract image $X_{\mathsf C}$ carry four declared maps

$$
q_{\rm sp}:X_{\mathsf C}\to Y_{\rm sp},\quad
q_{\rm tm}:X_{\mathsf C}\to Y_{\rm tm},\quad
q_{\rm bd}:X_{\mathsf C}\to Y_{\rm bd},\quad
q_{\rm mem}:X_{\mathsf C}\to Y_{\rm mem}.
\tag{8.1}
$$

The spatial map records a declared support or adjacency, the temporal map
records a clock/grade under its contract, the boundary map records a residual
class or response table, and the memory map records the state actually
available to the selector.  None is allowed to be an independently sampled
copy of another.

**Definition 8.1 (view kernel and transport condition).** A view $q$ has
the task kernel when

$$
\ker(q)=\ker(\Phi_{\mathcal U})
\quad\text{on }X_{\mathsf C}.
\tag{8.2}
$$

It has a transport action for $a$ when there are induced legal domains,
response labels and a successor $\overline T_a$ satisfying

$$
\begin{aligned}
x\in D_a&\Longleftrightarrow q(x)\in\overline D_a,\\
\operatorname{step}_a(x)&=\overline{\operatorname{step}}_a(q(x)),\\
q(T_a x)&=\overline T_a(q(x))\qquad(x\in D_a),\\
\operatorname{sel}(x)&=\overline{\operatorname{sel}}(q(x)),\qquad
\operatorname{ns}(x)=\overline{\operatorname{ns}}(q(x))
\quad\text{when these are in the contract}.
\end{aligned}
\tag{8.3}
$$

For an inherited meter, (8.3) is imposed on the pair $(x,m)$; for a fresh
suffix it is imposed on the residual state with the fresh identity meter.

**Theorem 8.2 (four-view recovery on one actual image).** If all four maps in
(8.1) satisfy (8.2) and (8.3) for the same $\mathcal U$, then each actual
image $q_i(X_{\mathsf C})$ is uniquely bijective with the image of the complete
resource profile.  The induced bijections commute with every typed action,
failure label, selector and namespace allocator (when their maps factor
through the view), clock transport and declared resource update.

If only the joint map

$$
J=(q_{\rm sp},q_{\rm tm},q_{\rm bd},q_{\rm mem})
$$

satisfies $\ker(J)=\ker(\Phi_{\mathcal U})$, then only the joint
view is guaranteed to recover the profile; no individual view may be called a
complete boundary.

**Proof sketch.** Define the map from an actual view value to a profile by
choosing any representative.  Kernel equality makes it well defined, and
surjectivity onto the actual image makes it bijective.  Equation (8.3)
transports legality, labels and successors, so the bijection commutes with
the typed process.  For the joint statement, apply the same factorization to
$J$; projecting its factors can enlarge a kernel.  This is the kernel and
transport criterion in [Boundary Dynamics §§26.2 and 26.5](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md)
and [Process Geometry §§30--34](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
$\square$

## 9. Boundary fields that cannot be silently dropped

The following fields belong to the boundary whenever they can change a
declared continuation.  Their absence is a change of task, not a harmless
compression.

1. **Fresh namespace.** An operation name includes a namespace, type,
   version and token.  Fresh allocation requires the token to be outside the
   actual archive (or to satisfy the declared alpha-equivalence rule);
   reusing a spelling from another source is not a common action.  Allocator
   state and owner/equality data enter the actual boundary whenever later
   legality can inspect them.
2. **Failure and illegal outcomes.** A legal failure with a successor, an
   illegal attempt, and normal success retain separate statuses and reasons.
   Their successor domains must descend through the same kernel.
3. **Selector.** If an internal controller chooses the next action, its
   accessible selector state and tie-breaking rule are part of the response.
   A passive future quotient cannot be used as a closed-loop controller
   without this factorization.
4. **Ordered archive.** A sequence of receipts, records or names is not
   interchangeable with a multiset or max summary.  If the task can ask for
   order, the archive is part of $\Phi_{\mathcal U}$.
5. **Clock and calibration.** Absolute epoch, duration, waiting label and
   calibration/reference data enter the response when they affect legality,
   selector choices or resource prices.  A positive additive grade is still
   only a grade unless its transport and units are declared.
6. **Permission and reference.** Access rights, phase references and source
   selectors are configuration fields whenever they alter the legal menu.
7. **Resource units and meter contract.** Read count, update count, literal
   length, allocation, memory retention and clock cost use declared units and
   either the fresh-suffix or inherited-meter composition law.

**Proposition 9.1 (omission creates a finite countermodel).** If any one of
the fields above can vary on two actual states while all retained boundary
fields agree, and some declared continuation, selector or response actually
depends on that field, then there is a finite continuation task for which the
retained boundary is not sufficient.

**Proof sketch.** Choose the first action whose legality, selector, output,
failure label, archive order or meter update differs.  A finite continuation
containing that action separates the states; its length need not be one or
two.  For an omitted clock or permission field, use the continuation whose
threshold or access predicate reads that field.  This is exactly the “same
current value, different future response” construction of [Boundary Dynamics
§§19--20](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md).
$\square$

## 10. Relation to existing resource and residual boundaries

The following reuse map states what is consumed and what remains an
assumption.

| Existing volume | Interface used here | Boundary retained here |
| --- | --- | --- |
| [Boundary Dynamics §§19--21, 26--27](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md) | Future response kernels, typed partial actions, right-congruence closure, four-view kernel conditions | Adds the resource response and explicit namespace/failure/archive/clock fields |
| [Transport--Memory Completion §§2.1, 2.17--2.20, 3--4](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) | Task-relative memory, common source, weighted continuation and lawful gluing | Separates fresh suffix from inherited meter and states their factorization obligations |
| [Serial Joint Resource Frontier §§1, 5, 7--8](RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md) | Uniform sourcewise budgets, Pareto basis, weighted worst-run prices and update/read tradeoff | Uses the quantifier $\exists\Pi\,\forall x$ and does not combine maxima from different runs |
| [Uniform Descriptor Boundary §§4--7](RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_DESCRIPTOR_BOUNDARY.md) | Source-independent descriptors, exact replies, boundary factorization and paired-history tests | Restricts minimality to the declared actual image and task |
| [Typed Residual Cocycle Reconstruction §§1--6](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md) | Typed residual graph, descended cocycle, ordered-path obstruction | Explains cancellation and why an additive resource still loses order |
| [Process Geometry §§27--34](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) | Common calibrated source, complete traces, four views and transport equations | Supplies the view-kernel proof shape; no physical metric is inferred |
| [Fibonacci Atomic Relation Generation §§2--5, 21](FIBONACCI_ATOMIC_RELATION_GENERATION.md) | Abstract atoms, ordered constructors and relation ports | Treats $\alpha,\beta$ as carriers only; no universal recurrence or physics |

The action-order closure in §5 is intentionally tied to the fixed menu
$\mathcal M$.  A theorem for one menu does not provide a theorem for all
future names, and a finite quotient for one resource contract does not provide
a quotient for a different clock, archive or meter contract.

## 11. Scope and open boundaries

All propositions above are theory-level ordinary mathematics over the stated
typed actual-image interfaces.  No new Lean verification is claimed.  The
following questions remain open unless supplied by an independent volume with
matching hypotheses:

* a general signed-fiber theorem giving a finite resource-aware quotient or a
  uniform controller outside the recognized descriptor and source domains;
* probability or quantum continuation kernels, including posterior memory,
  stochastic failure and quantum instruments with an inherited resource;
* a physical spacetime, metric, relativistic clock or energetic meaning for
  the four representations;
* arbitrary unbounded, continuous or noisy clocks, meters, namespaces and
  archives, including precision and robustness costs;
* a global complexity, acquisition, installation or memory optimum for the
  controller synthesis problem;
* a universal Fibonacci or $k$-bonacci law inferred solely from the atom
  names $\alpha,\beta$.

An open boundary is not a refutation of a restricted finite model.  It records
that the missing common source, action-order closure, resource contract or
transport evidence has not been supplied for the larger claim.

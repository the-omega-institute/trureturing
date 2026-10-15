# Recursive relational observation: native representative-reply normal form

This volume gives ordinary mathematical definitions and proofs. It is
reference input, without Lean kernel certification. Its native suppliers
are cited separately from the deductions proved here. The source is an
append-only theory volume for `generic-v1`; subsequent corrections and
extensions belong after its final append anchor, leaving existing bytes
unchanged.

The principal result preserves the exact solution set of every complete
native template while replacing its reply-dependence components by stars.
The equivalent owned-seed language keeps actual-tree compatibility and
each original whole-block potential once. Its seeds are analytical
variables, not additional observations. The paid implementation preserves
the original memory optimum, all late targets and the one-Read interface.
Effective all-size pressure certification remains an open obligation.

## 1. The unchanged native task

**Definition 1.1 (trees, literals and substitution).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\operatorname{ht}(\alpha)=\operatorname{ht}(\beta)=0,
\qquad
\operatorname{ht}(\langle u,v\rangle)
=1+\max\{\operatorname{ht}(u),\operatorname{ht}(v)\}.
$$

Pairing is free and ordered. Every finite word in $L,R$, including
$\varepsilon$, is a legal original-root literal. Its reply $r_t(a)$
belongs to

$$
\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}:
$$

it reports the addressed constructor, or absent if traversal passes a
leaf. Define the homomorphic substitution by

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

For public $D\ge1$, retain exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:
                         \operatorname{ht}(v)\le D\},\qquad
W_D=\{q:|q|\le D-1\},\qquad
\mathcal P_D=\{Rq:q\in W_D\}.
\tag{RRN.1}
$$

The one actual initial source is stationary throughout preparation and
late acquisition. The iterates $\rho^kt$ specify prediction targets.
There is no subtree, equality, source-identity, age, reset, copying,
navigation or advice port.

**Assumption 1.2 (complete paid export).** One deterministic effective
preparation starts source-blind from $D$ and common source-independent
tables, does not know the later request, and terminates on every
$t\in\mathcal F_D$. Every source distinction is acquired through charged
literal Reads. Its exported code $E(t)$ includes every accessible
surviving source distinction: selectors, control, buffers, operands,
lengths, allocation, handles, counters and accessible timing. Any other
accessible field is a function of this code and public data. A separately
paid handoff and access-isolation service removes access to all other
preparation dependence and supplies lawful reader entry.

Only after export, a public source-independent $p\in\mathcal P_D$
arrives. A common deterministic effective reader uses $E(t),D,p$ and
installed tables to choose zero Reads or one fresh Read of the same
stationary source at an arbitrary finite original-root word. The choice
precedes the reply and every supplied count. The final predictor must
satisfy

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad\text{for every }t\in\mathcal F_D,\ p\in\mathcal P_D,
\text{ and subsequently supplied authentic }k\ge0,
\tag{RRN.2}
$$

without further Reads. Let $M_1(D)$ be the minimum complete attained
cardinality $|E[\mathcal F_D]|$ among these procedures. Preparation
Reads, work and temporary storage, table generation and installation,
post-request workspace, final predictor size, submitted address lengths
and letters, count representation, handoff, isolation, entry,
authentication and physical time are separate resources. These are the
task and service premises of [FMR, §1][FMR] and [NPC, §1][NPC].

## 2. Full temporal factors and complete native templates

**Convention 2.1 (credited all-count factor).** Use [AAR, Definition
12.2, Theorem 12.3 and Proposition 13.3][AAR]. Put
$s(r)=\#L(r)+2\#R(r)$ and $e(\alpha)=0,e(\beta)=1$.
If $q$ ends at an original branch, set $\Gamma_q(u)=(0,0)$.
Otherwise let the first original leaf on that path have label $\ell$
at $a$, and write $q=ar$. Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{RRN.3}
$$

On attained factors, the supplied decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{RRN.4}
$$

Here $c=1$ implies $b\ge2$, and (RRN.4) equals
$r_{\rho^ku}(q)$ for every $k\ge0$. The trajectory recovers $b$
as its first branch count and $c$ by the presence of an alpha stage.
Thus $\Gamma$ classifies complete trajectories, including initially
absent targets. Define, on all attained factor values,

$$
h(z)=\operatorname{Pred}(z,0).
\tag{RRN.5}
$$

This $h$ is a reply map, distinct from the height notation
$\operatorname{ht}$. In particular $h(\Gamma_q(u))=r_u(q)$.

**Definition 2.2 (canonical blocks and ports).** For $d\ge1$, put

$$
C_0=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup
\{\langle x,y\rangle:x,y\in S_d\}.
\tag{RRN.6}
$$

Fix $n\ge1$, and let $V=[n]\times W_d$ be the set of ports.
For $v=(i,q)$ and $x\in S_d^n$, write

$$
z_v(x)=\Gamma_q(x_i),\qquad y_v(x)=r_{x_i}(q),\qquad
G_q=\Gamma_q[S_d].
\tag{RRN.7}
$$

A complete native template chooses at every $v=(i,q)$ exactly one
constant equation $z_v=\zeta_v\in G_q$, or one donor equation

$$
z_v=\delta_v(y_{p(v)}),\qquad
p(v)=(j,a)\in V,\qquad \delta_v:\mathcal A\longrightarrow G_q.
\tag{RRN.8}
$$

The tables are total. Donors can be self donors, off-target donors or
members of cycles. Denote the simultaneous solution set in $S_d^n$
by $C_\Theta$, allowing the empty set. Every occurrence of a port
refers to the same actual coordinate of the same tuple.

**Convention 2.3 (credited saturation and canonicalization).** A
nonempty relation $B\subseteq S_d^n$ is admissible when every target
has a constant or one-reply witness of the form (RRN.8) on $B$.
[NDR, Theorem 2.2][NDR] supplies a complete template containing $B$
on these same coordinates. Integral and fractional cover optima
$K_d(n),Z_d(n)$, and all maxima of nonnegative masses, can therefore
be computed using complete solution sets.

For $\operatorname{ht}(v)\le d$, the completion $\pi_d(v)\in S_d$
retains every constructor through depth $d-1$ and replaces a branch
at that cutoff by $C_0$. It fixes $S_d$, preserves replies on $W_d$
and preserves all their $\Gamma$ factors. On a canonical block, a
length-$d$ word returns alpha if its parent is branch and absent
otherwise; longer words are absent. Thus every finite canonical probe
is simulated by one boundary reply in that same block or by a constant.
These are [FMR, Lemma 2.2 and Theorems 2.3–2.5][FMR], not new
normalization claims about projections of correlated fibers.

**Lemma 2.4 (separation and available guard values).** For every $d\ge1$:

1. The vector $(\Gamma_q(u))_{q\in W_d}$ determines $u\in S_d$
   uniquely.
2. For every $q\in W_d$,
   $\{\alpha,\beta,\mathsf{branch}\}\subseteq h[G_q]$.
   Consequently, for each $a\in\mathcal A$, a value
   $\zeta\in G_q$ exists with $h(\zeta)\ne a$.

Proof. Applying $h$ to the factor vector gives the complete constructor
array $(r_u(q))_{q\in W_d}$. At $d=1$ its three possible roots
determine $\alpha,\beta,C_0$. Inductively a root leaf is determined;
a root branch gives two constructor arrays of depth $d-1$ and hence
two unique children. This is also [CBN, Theorem 2.2][CBN].

For the second assertion, follow the path to $q$, placing alpha at
each unused sibling, and place respectively $\alpha,\beta,C_0$ at
its endpoint. The heights are at most $|q|+1\le d$. If an endpoint
branch occurs at depth $d-1$, it is exactly the permitted $C_0$;
all other terminal constructors are leaves. The three trees therefore
belong to $S_d$, including $q=\varepsilon$ and $d=1$, and give
the three stated replies. At least one differs from any prescribed
$a$, including $a=\mathsf{absent}$. $\square$

## 3. Elimination of the unary reply skeleton

**Definition 3.1 (reply skeleton).** For each donor equation put
$f_v=h\circ\delta_v:\mathcal A\to\mathcal A$ and draw an arrow
$v\to p(v)$. A constant port has no outgoing arrow and has the fixed
reply $h(\zeta_v)$. Every actual solution satisfies

$$
y_v=f_v(y_{p(v)})
\tag{RRN.9}
$$

at its donor ports. The skeleton by itself need not impose all original
factor equations or actual-tree consistency.

**Lemma 3.2 (one reply parameter per cyclic component).** Each weak
component of this finite arrow graph has exactly one constant sink
or exactly one directed cycle. A constant-sink component has one
skeleton solution. For a cyclic component choose its cycle ordering
$v_0,\ldots,v_{\ell-1}$ with
$p(v_j)=v_{j+1\bmod\ell}$, let $c=v_0$, and define

$$
F=f_{v_0}\circ f_{v_1}\circ\cdots\circ f_{v_{\ell-1}},
\qquad T=\{a\in\mathcal A:F(a)=a\}.
\tag{RRN.10}
$$

There are uniquely determined tables $a_v:T\to\mathcal A$ on all
ports of that component, with

$$
a_c(a)=a,\qquad a_v(a)=f_v(a_{p(v)}(a)).
\tag{RRN.11}
$$

Their tuples are precisely the component's skeleton solutions.
Writing

$$
b_v(a)=\delta_v(a_{p(v)}(a))
\tag{RRN.12}
$$

gives $h(b_v(a))=a_v(a)$, in particular $h(b_c(a))=a$.

Proof. Following outgoing arrows from any vertex reaches a sink or
repeats a vertex and enters a directed cycle. Vertices joined by an
arrow have the same terminal sink or cycle. This terminal object is
therefore constant on a weak component; two different terminal objects
cannot occur in one component. A sink must be a constant port, since
all other ports have exactly one outgoing arrow.

At a constant sink first set its reply to $h(\zeta_v)$ and propagate
backwards along incoming trees by (RRN.9). Every vertex has a unique
forward path to the sink, so this assigns every reply uniquely and
satisfies all equations.

On a cycle, prescribe $y_c=a$. Set
$y_{v_{\ell-1}}=f_{v_{\ell-1}}(a)$, then
$y_{v_{\ell-2}}=f_{v_{\ell-2}}(y_{v_{\ell-1}})$, continuing
back to $v_1$. The remaining equation at $c$ is exactly $F(a)=a$.
This also covers a self-loop, where $F=f_c$. Once the cycle replies
are set, propagate backwards along its incoming trees. This proves
existence, uniqueness and the characterization by $T$. Equations
(RRN.11) and $f_v=h\circ\delta_v$ give the last assertion.
No actual realization of these skeleton values has been asserted.
$\square$

## 4. Same-solution representative-reply templates

**Definition 4.1 (representative form).** A complete template is in
representative-reply form if every nonconstant arrow component is a
star with a designated port $c$: its center queries itself, and every
other port in that component queries $c$. Constant ports have no
outgoing arrows. A star's decoder at its center may restrict which
replies can occur there.

**Theorem 4.2 (exact native representative normal form).** For every
$d,n\ge1$ and every complete native template $\Theta$, one can
effectively construct a complete native template $\Theta^{\mathrm{rep}}$
on exactly the same $n$ blocks and the same port set $V$ such that

$$
C_{\Theta^{\mathrm{rep}}}=C_\Theta.
\tag{RRN.13}
$$

The new template has representative-reply form. Its centers are
existing cycle ports of the original skeleton. Constant-sink components
and cyclic components with exactly one fixed reply become constants.
An empty fixed-reply set is represented by a center guard with no
fixed reply. No block is duplicated, projected or independently chosen.

Proof. Work separately on the components of Definition 3.1. In a
constant-sink component, Lemma 3.2 determines all replies. Assign the
sink its original full constant factor. At every other port assign
the constant $\delta_v(y_{p(v)})$. Each assigned factor belongs to
the correct $G_q$, and its $h$-image is the propagated reply. Replace
every equation in this component by that full factor constant.

For a cyclic component use $c,T,a_v,b_v$ from Lemma 3.2. If $T$
has one member $a_0$, replace each equation by the constant
$z_v=b_v(a_0)$. Otherwise, for each $v$ choose a total table
$\widehat\delta_v:\mathcal A\to G_{q_v}$ which on $T$ equals
$b_v$. Off $T$, noncenter tables can be filled with any value in
$G_{q_v}$. At the center require

$$
h(\widehat\delta_c(a))\ne a\qquad(a\notin T).
\tag{RRN.14}
$$

Lemma 2.4 supplies each of these entries. On $T$, the center table
already satisfies $h(\widehat\delta_c(a))=a$. Replace the component
by

$$
z_v=\widehat\delta_v(y_c)
\quad\text{for all its ports }v,
\tag{RRN.15}
$$

including $v=c$. These are valid native donor equations at the existing
port $c$. If $T=\varnothing$, (RRN.14) is imposed at all four
arguments and the center equation is unsatisfiable. If $T=\mathcal A$,
there are no off-domain guard entries. No separate condition about
the attainability of absent at a root is needed.

To prove the forward inclusion in (RRN.13), let $x$ solve $\Theta$.
Its replies solve the skeleton. On a constant-sink component they
are the uniquely propagated replies and its full factors are the
specified constants. On a cyclic component, $y_c(x)\in T$ and
uniqueness in Lemma 3.2 gives
$y_v(x)=a_v(y_c(x))$ and $z_v(x)=b_v(y_c(x))$.
Thus all replacement equations hold, including singleton constants.

Conversely let $x$ solve the replacement. For a star center, applying
$h$ to its equation and using (RRN.14) forces $y_c(x)\in T$.
All its factors are therefore $b_v(y_c(x))$, and applying $h$
gives $y_v(x)=a_v(y_c(x))$. Equation (RRN.12) then gives every
original donor equation. In a singleton component the replacement
constants give these same replies and equations at its sole allowed
seed. In a constant-sink component their $h$-images are the propagated
replies; the original constant and donor equations follow from their
construction. This proves the reverse inclusion. Both inclusions were
proved on the original actual tuple $x$, so any remaining incompatibility
between components inside a block is preserved exactly.

Everything is finite: enumerate the components, compose maps on four
symbols, test their fixed points, propagate tables and choose guard
values from finite $G_q$. This proves effectivity. $\square$

**Corollary 4.3 (unchanged cover and mass optima).** Restricting complete
templates to representative-reply form leaves $K_d(n)$, $Z_d(n)$
and the maximum of every nonnegative mass on $S_d^n$ unchanged.
In particular it preserves masses with arbitrary whole-block weights
and with an arbitrary correlated weight $W:S_d^n\to[0,\infty)$.

Proof. Each original complete solution set is exactly the solution
set of its representative template, and representative templates
are themselves complete native templates. Thus the two collections
of solution sets coincide, including the empty set. Their cover
optima and masses coincide. Convention 2.3 relates them to all
admissible competitors. $\square$

The theorem changes the witness decoders and donors; it does not
claim CBN's separate same-witness property. It removes long cycles
from the reply skeleton, while retaining every relation imposed by
sharing an original block.

## 5. A two-way owned-seed language

**Definition 5.1 (native owned-seed network).** Fix $d,n\ge1$ and
the same public port set $V$. Choose a finite seed index set $J$.
Each $c\in J$ has a domain $T_c\subseteq\mathcal A$, possibly empty,
and a distinct designated owner port $o_c\in V$. Every port
$v=(i,q)$ has exactly one of the following prescriptions:

1. A constant $z_v=\zeta_v\in G_q$.
2. An assignment to one seed $c$, with a table
   $B_v:T_c\to G_q$ and value $z_v=B_v(s_c)$.

The owner $o_c$ is assigned to its own seed $c$ and satisfies

$$
h(B_{o_c}(a))=a\qquad(a\in T_c).
\tag{RRN.16}
$$

It follows in particular that a nonempty owner domain is contained
in the attained reply set of its owner. Distinct owners imply
$|J|\le n(2^d-1)$. Multiple occurrences of a seed use the same
variable. Let $\mathcal S=\prod_{c\in J}T_c$, and let $z_v(s)$
be the prescribed value for $s\in\mathcal S$. Define

$$
\begin{aligned}
\mathcal X_i(s)
 &=\{u\in S_d:\Gamma_q(u)=z_{(i,q)}(s)
                                      \text{ for all }q\in W_d\},\\
\mathcal S_{\rm real}
 &=\{s\in\mathcal S:\mathcal X_i(s)\ne\varnothing
                                      \text{ for every }i\}.
\end{aligned}
\tag{RRN.17}
$$

Lemma 2.4 makes every $\mathcal X_i(s)$ empty or a singleton.
Only $s\in\mathcal S_{\rm real}$ reconstruct an actual tuple
$x(s)\in S_d^n$. This condition is part of the language; seed
assignments are not assumed to be freely or jointly realizable.

For nonnegative whole-block weights $w_i:S_d\to[0,\infty)$ put

$$
\Phi_i(s)=\sum_{u\in S_d}w_i(u)
       \prod_{q\in W_d}
          \mathbf1_{\{\Gamma_q(u)=z_{(i,q)}(s)\}},\qquad
Z(\mathcal N;w_1,\ldots,w_n)
   =\sum_{s\in\mathcal S}\prod_{i=1}^n\Phi_i(s).
\tag{RRN.18}
$$

Each $\Phi_i$ is zero or the weight of its one reconstructed actual
block. Its scope contains at most $2^d-1$ distinct seeds, regardless
of how often a seed occurs within that block. Each original $w_i$
is owned once, by $\Phi_i$, even when its arguments meet many stars.
These potentials are specifically (RRN.18); arbitrary hypergraph
potentials are not substituted without a native realization proof.

**Theorem 5.2 (exact correspondence in both directions).** For every
$d,n\ge1$ the following statements hold.

1. Every complete native template gives an owned-seed network with
   a bijection $C_\Theta\leftrightarrow\mathcal S_{\rm real}$.
   Its seed coordinate is the actual reply at its existing owner port.
2. Every owned-seed network in Definition 5.1 gives a complete native
   representative template on the same $n$ blocks, whose solution
   set is in bijection with $\mathcal S_{\rm real}$ by those same
   actual owner replies.
3. Under either correspondence, for all nonnegative $w_i$,

$$
\sum_{x\in C_\Theta}\prod_iw_i(x_i)
       =Z(\mathcal N;w_1,\ldots,w_n).
\tag{RRN.19}
$$

For a general nonnegative correlated weight $W$ the corresponding
identity is

$$
\sum_{x\in C_\Theta}W(x)
       =\sum_{s\in\mathcal S_{\rm real}}W(x(s)).
\tag{RRN.20}
$$

Proof. For the first direction apply Theorem 4.2. Give each surviving
star one seed with its domain $T$ from (RRN.10), let its center be
the owner, and use the tables $b_v$ of (RRN.12). Constantized ports
remain constants. The owner identity is Lemma 3.2. If a component has
empty $T$, retain its empty seed and owner; no seed tuple and no
native solution exist.

For any solution, the actual owner replies lie in their domains and
determine all its factors by Theorem 4.2. Each block is then uniquely
determined by Lemma 2.4. Conversely, a realizable seed assignment
reconstructs one actual tuple. The owner identity makes the actual
owner replies exactly those seeds, so all star equations hold.
Theorem 4.2 returns an original solution. These maps are inverse.
They also cover the case with no surviving seeds: the empty seed
tuple reconstructs either one actual tuple or none.

For the converse, extend every table $B_v$ at a nonowner assigned
to $c$ arbitrarily from $T_c$ to $\mathcal A$, with values still
in its $G_q$. At the owner $o_c$ retain $B_{o_c}$ on $T_c$ and
choose its other entries to satisfy

$$
h(\widehat B_{o_c}(a))\ne a\qquad(a\notin T_c).
\tag{RRN.21}
$$

Lemma 2.4 again supplies the guard, including at a root port. Every
port assigned to $c$ queries the actual owner port $o_c$ and uses
its extended table. A constant prescription becomes a constant
equation. This is a complete representative template.

In any native solution, the equation at $o_c$ forces its actual
reply $s_c$ into $T_c$ by (RRN.21). The other equations give
precisely all prescribed $z_v(s)$, so the actual tuple is $x(s)$
and $s$ is realizable. Conversely a realizable $s$ gives a unique
actual tuple, and (RRN.16) makes its owner replies equal $s_c$.
Every extended decoder is consequently evaluated on its original
domain, and every equation holds. Different seed tuples cannot give
the same actual tuple, since its owner replies recover all their
coordinates. This proves the second bijection without a missing
shared-realization premise.

For (RRN.19), expand the finite products of sums in (RRN.18).
A nonrealizable seed assignment has at least one empty compatibility
set, hence contributes zero even if some weights vanish. A realizable
assignment contributes exactly $\prod_iw_i(x_i(s))$. The bijection
counts each solution once. Every whole-block weight occurs in exactly
one factor; it is never attached separately to its reply occurrences.
Equation (RRN.20) follows from the same bijection without any product
assumption on $W$. $\square$

**Proposition 5.3 (empty, singleton and no-seed cases).** The
correspondence includes all of the following degeneracies. An empty
domain makes both the seed sum and native solution set empty. A
singleton domain can be removed by replacing every port assigned to
it by its sole full-factor value. With no seeds, the sum contains
one empty assignment and equals the product of the constant block
potentials, which may be zero. A domain of size four needs no
off-domain guard.

Proof. A product with an empty factor has no seed tuples. Its native
owner has no fixed reply by (RRN.21), so no solution exists. If
$T_c=\{a\}$, every admissible seed assignment already has $s_c=a$.
Replacing $B_v(s_c)$ by $B_v(a)$ at all of that seed's ports leaves
the same compatibility sets on the other seeds. The omitted owner
reply is still $a$ because of (RRN.16); the two solution maps remain
inverse. The assertions about no seeds and a full domain follow from
the empty-product convention and the absence of arguments outside
$\mathcal A$. None of these facts requires positivity of the weights
or existence of an actual tuple compatible with all constants.
$\square$

## 6. Exact pressure language and its remaining overlaps

**Theorem 6.1 (all-size cap equivalence).** Fix $d\ge1$,
$w:S_d\to[0,\infty)$ and $C>0$. The following are equivalent:

1. Every $n\ge1$ and every complete native template on $n$ blocks
   satisfy

$$
\sum_{x\in C_\Theta}\prod_{i=1}^nw(x_i)\le C^n.
\tag{RRN.22}
$$

2. Every $n\ge1$ and every network of Definition 5.1, with its
   potentials formed from that same $w$ by (RRN.18), satisfy

$$
Z(\mathcal N;w,\ldots,w)\le C^n.
\tag{RRN.23}
$$

Both directions preserve the number $n$ of original potential owners.

Proof. To deduce (RRN.23) use the native template constructed in
Theorem 5.2's converse and its exact weighted identity. To deduce
(RRN.22) use the owned-seed network constructed from that native
template and the other direction of the same identity. Empty sets
and zero masses are included in both statements. $\square$

**Convention 6.2 (pressure and the original lower witness).** Write

$$
A_n(w)=\max_\Theta\sum_{x\in C_\Theta}\prod_iw(x_i),\qquad
\beta_d(w)=\sup_{n\ge1}A_n(w)^{1/n}.
\tag{RRN.24}
$$

Theorem 6.1 expresses this same all-size pressure as the supremum
over owned-seed networks. For a probability $\mu$ on $S_d$,
[NPC, Theorems 5.3 and 6.2][NPC] supply

$$
2^{-\sigma_d}=\min_{\mu\in\Delta(S_d)}\beta_d(\mu),\qquad
\sigma_d=\inf_{n\ge1}\frac{\log_2K_d(n)}n.
\tag{RRN.25}
$$

Their minimum includes zero coordinates. If either equivalent cap
condition holds for a probability $\mu$, [NPC, Theorem 7.1][NPC]
gives the unchanged original-task consequence

$$
M_1(D)\ge\left\lceil C^{-2^{D-d}}\right\rceil\quad(D\ge d),
\qquad \lambda\ge-2^{-d}\log_2C.
\tag{RRN.26}
$$

This uses one actual perfect scaffold with $2^{D-d}$ present blocks
inside $\mathcal F_D$. An arbitrary original-root late literal is a
constant or is a function of one canonical boundary reply in one
of those same blocks. Restricted code fibers retain all their
correlations, and the analytical product law gives their mass bound.
The scaffold is a restriction for a lower bound, not an additional
reader input or an imposed form for general competitors.

**Convention 6.3 (the overlap retained by the language).** Independent
arrow components in §3 need not occupy disjoint blocks. One original
block can contain ports assigned to several different seeds, and one
seed can occur in several different original blocks. The full
$\Phi_i$ is a joint function of all those seeds. Its value can be
zero because their proposed factors do not fit one actual canonical
tree. Seed combinations in different blocks must agree on every
shared seed.

Thus the identity in (RRN.18) is a sum of products with shared
arguments; it is not a product of sums over stars. The arbitrary
correlated weight in (RRN.20) requires its full joint scope as well.
No seed is copied into an independent variable, and no potential is
counted at every incidence. CBN's constructor representation and its
owned potentials remain available, but their finite-domain or binary
constraint properties give no all-size pressure bound by themselves.
The fixed native incidence families of [GCB, Theorem 1.2][GCB]
already demonstrate why full block potentials remain relevant after
reply identifications.

## 7. Paid normal form in the original late-target task

**Theorem 7.1 (no alphabet enlargement and exact optimal alphabet).**
Fix $D\ge1$. From any correct original preparation and reader with
$m$ attained names, one can effectively construct a correct original
preparation and reader with $m_0\le m$ attained names whose late
reader uses the constant or representative query of a template from
Theorem 4.2 at each name. Sufficient preparation bounds on every
original source are

$$
T_{\rm prep}\le2^D-1,\qquad
Q_{\rm prep}\le D,\qquad
A_{\rm prep}\le(D-1)2^D+1.
\tag{RRN.27}
$$

Here $T,Q,A$ count Reads, maximum submitted literal length and total
submitted letters. Each nonconstant late query is an actual literal
$Ra$ with $a\in W_D$, hence has length at most $D$. This restricted
reader class has exactly the original optimum $M_1(D)$. In particular,
if the given competitor attains that optimum, $m_0=m=M_1(D)$.

Proof. Restrict the original code to the explicit canonical sources
$\langle\alpha,u\rangle$, $u\in S_D$. Let $I$ be its attained
names there and let

$$
B_e=\{u\in S_D:E(\langle\alpha,u\rangle)=e\}\quad(e\in I).
\tag{RRN.28}
$$

These nonempty fibers partition $S_D$, and $m_0=|I|\le m$.
For a fixed $e$ and target, the original reader's zero-Read decision
or submitted literal is fixed before a reply and before a count.
Equal replies give identical final predictors. Correctness for every
subsequent $k$ then makes the complete target trajectories equal;
Convention 2.1 makes their factors equal. Every arbitrary finite
canonical literal is a constant or a function of one boundary reply
by Convention 2.3. Thus $B_e$ is admissible without any target-prefix
or independence restriction.

Choose complete witnesses for $B_e$ and normalize them by Theorem
4.2, obtaining a representative template whose solution set contains
$B_e$. This containment suffices: the chosen tables are correct on
the assigned fiber even when its complete solution set is larger.
No enlargement of the actual name fibers is required.

For actual $t=\langle\alpha,v\rangle$, before any request, Read
every original-root literal $Rq$, $q\in W_D$, in a public fixed
order, including absent replies. These replies determine
$u=\pi_D(v)$ by Lemma 2.4 and canonicalization. Export only the
fixed-width name

$$
E^{\mathrm{rep}}(t)=E(\langle\alpha,\pi_D(v)\rangle).
\tag{RRN.29}
$$

All names in $I$ are attained since $\pi_D$ fixes $S_D$. Installed
name tables can be generated by simulating the given terminating
preparation on the finitely many explicit canonical sources. Witness
tables can be found by finite exhaustive checking on their fibers;
their existence was just proved. This generation depends on public
finite trees and the given procedures, not on the unknown actual
source. Scanning its boundary is the charged source acquisition that
selects a table entry.

After $p=Rq$ arrives, the exported name selects the normalized target
equation. If constant, output that factor with zero Reads. Otherwise
its representative is an existing port $a_c\in W_D$. Submit the
one actual word $Ra_c$ to the same stationary $t$ and apply the
installed normalized decoder to that actual reply. The reply agrees
with that of $\pi_D(v)$ at $a_c$, so the equation supplies
$\Gamma_q(\pi_D(v))=\Gamma_q(v)$. Equation (RRN.4) answers every
subsequently supplied authentic $k$. No actual seed vector has been
exported or observed; an execution receives just its selected
representative's one reply. The reader and query do not receive $k$
in advance.

There are $2^D-1$ scan words, their maximum length is $D$, and

$$
\sum_{l=0}^{D-1}(l+1)2^l=(D-1)2^D+1.
\tag{RRN.30}
$$

This proves (RRN.27). Use a public scan, public allocation, fixed-width
name representation and padded finite table computation. Under
Assumption 1.2, isolate all other source dependence, including the
constructor array, selection workspace, preparation control and
transcript. The surviving complete alphabet is precisely $I$.

Every restricted reader is an allowed original reader, giving one
inequality between the optima. The construction from every original
competitor gives the other. If the input attained the original
minimum, a strict decrease below $m$ would contradict its definition,
so the resulting alphabet has exactly $m$ names. $\square$

**Corollary 7.2 (exact cardinality for an arbitrary competitor).** If
one also requires exactly $m$ attained names for a given possibly
nonminimal original competitor, this is achievable with representative
readers and sufficient preparation bounds

$$
T_{\rm prep}\le2^{D+1}-1,\qquad
Q_{\rm prep}\le D+1,\qquad
A_{\rm prep}\le D\,2^{D+1}+1.
\tag{RRN.31}
$$

The assigned fibers may change. Neither (RRN.27) nor (RRN.31)
asserts preservation of the competitor's preparation cost.

Proof. The finite set $\mathcal F_D$ has at least $m$ sources because
$m$ is an attained deterministic alphabet size. Start with the
$m_0\le m$ nonempty full-family fibers from Theorem 7.1. While
their number is below $m$, at least one contains two sources;
otherwise their total number would be $|\mathcal F_D|<m$.
Split off one source as a new name and duplicate the parent name's
representative template. Iteration gives exactly $m$ nonempty
fibers, each a subset of a fiber where that template is correct.

All finite sets and this refinement can be generated source-blind.
The original $m$ can itself be computed by simulating the terminating
given preparation on every explicit member of $\mathcal F_D$.
The actual source selects its refined name through a paid scan of
every $Rq$ with $|q|\le D$. Since $\operatorname{ht}(v)\le D$,
this complete constructor array determines $v$ itself, and hence its
public refined table entry. Its scan counts are (RRN.31), using
(RRN.30) at $D+1$. Export only the refined name and apply the same
isolation and padding conventions. Duplicating a public reader table
adds no source-bearing late query and changes no predictor requirement.
$\square$

**Proposition 7.3 (joint implementation at actual occurrences).** Suppose
$Ra_1,\ldots,Ra_n$ are public prefix-free, actually present block
roots in one stationary original source, with $|a_i|\le H$ and
block height at most $d$. A finite joint cover by complete solution sets,
with its templates normalized by Theorem 4.2, is implemented by charged
original-root preparation
words $Ra_iw$, $w\in W_d$, and by zero Reads or one actual late
word $Ra_jw_c$ at a representative port. Sufficient joint scan bounds
are

$$
\begin{aligned}
T&\le n(2^d-1),\qquad Q\le H+d,\\
A&\le n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr).
\end{aligned}
\tag{RRN.32}
$$

When $H+d\le D$, all block targets $Ra_iq$, $q\in W_d$,
are permitted original late targets. A cover code for these block
targets is not by itself a reader for other targets of the full
source; Theorem 7.1 supplies the full-family assertion.

Proof. Each preparation word obtains exactly the specified boundary
reply of its actual block, including absent suffixes. Acquire the
whole tuple of canonical blocks and export its joint first-containing-
cover-member index; no block is independently recolored. Theorem 4.2
preserves each complete cover member exactly. Starting with an arbitrary
admissible cover instead, Convention 2.3 first enlarges its members to
complete solution sets with no increase in their number. Their targets
can therefore
use the installed center port, translated to the single literal
$Ra_jw_c$ on the actual source.

The original occurrences are present, so pairing homomorphism gives

$$
r_{\rho^kt}(Ra_iq)
   =r_{\rho^k(t|_{Ra_i})}(q)\qquad(k\ge0).
\tag{RRN.33}
$$

This is the precise presence premise of `original_present_transport`
in [NativeDepthPatterns][D5N]. The notation $t|_{Ra_i}$ identifies
an actual subtree mathematically; it supplies no subtree input.
A virtual wrapper's root and left cone are public constants, while
its $Rw$ is implemented only by the original word at the occurrence
followed by $w$, as in [FMR, Lemma 3.1][FMR].

There are $2^d-1$ words per block and their suffix lengths sum to
$\sum_{l=0}^{d-1}l2^l=(d-2)2^d+2$, including $d=1$.
Adding prefixes of length at most $H+1$ proves (RRN.32).
The actual target length is at most $H+d$. These are exactly the
paid occurrence bounds of [CBN, Proposition 7.2][CBN], now with
representative witnesses. An absent block root is never transported
as a subtree. A source-varying cut descriptor would need its own
acquisition and retained alphabet accounting. $\square$

**Convention 7.4 (separate resource accounting).** These constructions
do not preserve an old preparation transcript, its Read count or its
work bound. Fixed public scans replace that preparation, and only
their complete exported names remain accessible. Table generation,
installation and lookup work are finite but have no useful uniform
efficiency bound here. The factor predictor $(b,c)$ has $0\le b\le2D$
and $c\in\{0,1\}$, so
$\lceil\log_2(2D+1)\rceil+1$ bits suffice for it separately from
the complete retained name and the authentic count representation.
Isolation, entry and authentication are paid service premises;
padding does not establish a physical erasure or timing theorem.

## 8. Representative capacity and the unclosed global question

**Proposition 8.1 (a capacity profile for every original code).** For
the canonical fibers $B_e$ of any original $m$-name competitor,
choose complete witnesses and perform Theorem 4.2's normalization.
Let $J_e$ index its surviving nontrivial seeds, with domain sizes
$t_{e,c}\in\{2,3,4\}$. Nonempty fibers have no empty seed domains;
singleton seeds have been constantized. Then

$$
|B_e|\le\prod_{c\in J_e}t_{e,c},\qquad
\sum_{e\in I}\prod_{c\in J_e}t_{e,c}\ge |S_D|.
\tag{RRN.34}
$$

In particular some attained canonical name satisfies

$$
\sum_{c\in J_e}\log_2t_{e,c}
   \ge\log_2|S_D|-\log_2m.
\tag{RRN.35}
$$

Proof. A seed tuple determines the full factor vector at every port,
and Lemma 2.4 makes at most one canonical block compatible with that
vector. Thus the map from a solution to its owner replies is
injective. The fiber is contained in that complete solution set,
giving the first inequality. Sum over the partition (RRN.28).
There are $|I|\le m$ terms, so at least one is at least
$|S_D|/|I|\ge |S_D|/m$. Taking logarithms gives (RRN.35),
with an empty product interpreted as one. $\square$

This is a bound on unresolved representative capacity. The product
can overcount incompatible seed tuples. It asserts neither their
independence nor simultaneous acquisition of their replies, and
does not charge a seed vector as the retained code.

**Open problem 8.2 (overlap-aware effective all-size pressure).** At a
fixed $d$, construct a total computable predicate
$V(d,\mu,C,\pi)$ on rational probabilities, rational $C>0$ and
finite strings, with the following two properties:

1. Acceptance proves (RRN.23) for every $n\ge1$ and every owned-seed
   network of Definition 5.1 with potentials formed from $\mu$.
2. For every rational $\epsilon>0$, some accepted pair satisfies
   $-\log_2C>\sigma_d-\epsilon$.

Theorem 6.1 makes these exactly soundness and optimizer-cofinality
for the unrestricted native-template pressure. No seed topology,
block correlation, zero weight or full potential may be omitted.
Theorems 4.2 and 5.2 prove neither condition for a proposed new
certificate family. The existing sound joint/scaffold/stability
calculus of [JTC, Definition 9.1 and Theorem 9.2][JTC] remains
available; its optimizer-cofinality is unproved. The single-residual
theorem in [SRP, Theorem 1.2][SRP] requires a specified one-residual
support. The present elimination has no such support hypothesis,
but retains the multi-seed block potentials that prevent that
restricted tensorization argument from directly applying.

At fixed depth there are finitely many local tables and every seed
has at most four values. Neither bounds the number of seeds or
eliminates the shared scopes of the $\Phi_i$. Computing one finite
network sum proves no all-size upper. Nor does enumeration of finite
proofs prove that accepted endpoints reach the optimizer.

[NPC, §8][NPC] distinguishes finite refutations, increasing computable
lower approximants to $\beta_d$, and the unproved upper certification
needed for this problem. A proof of the two properties above, or a
uniform effective error in

$$
\sigma_d\ge\frac{\log_2K_d(n)}n-\eta_d(n),\qquad
\eta_d(n)\longrightarrow0,
\tag{RRN.36}
$$

would address the unchanged effective lower-convergence gap. No
such verifier, modulus or noncomputability result is supplied here.

**Convention 8.3 (retained objectives and evidence ceiling).** The
credited native relations remain

$$
\lambda=\sup_{d\ge1}2^{-d}\sigma_d,\qquad
0\le\lambda-2^{-d}\sigma_d\le2^{-d}\phi,
\qquad
\frac18\log_2\frac{33}{13}\le\lambda<\frac3{16}.
\tag{RRN.37}
$$

Here $U_0=1$, $U_{h+1}=1+U_h^2$ and
$\phi=\lim_h2^{-h}\log_2U_h$. FMR supplies the rate and depth
relations, NCE supplies the displayed lower, and D3 supplies the
displayed upper and $M_1(3)=4$. General exact $M_1(D)$, sharp
$\lambda$, effective optimizer-cofinality and the full
minimal-relations/internal-observer/mutual-recovery programme remain
open. The new normal form states what a boundary observer can recover
after its one paid representative reply: the selected full factor,
and hence every future requested reply. It does not recover the
whole source, an unobserved age, a seed vector or physical space and
time from the retained name.

## 9. Suppliers, primary correspondences and bounded checks

**Convention 9.1 (native attribution and source scope).** The native
sources NPC and CBN are used at public revision
`ad307958633c230c6e6611a324f090532e2ffac2`. FMR supplies paid
canonicalization and all-word simulation; NDR supplies complete
template saturation; AAR supplies the temporal factor. The new
`repo-derived` deductions here are the guarded same-solution star
normal form, its two-way owned-seed language, their paid representative
implementation and the capacity profile. Finite functional elimination
and equality-aware weighted summation are mature intermediates,
not claims of worldwide originality.

[NCM, Theorem 4.1 and Proposition 6.1][NCM] supply
$\sigma_2=\log_2(25/17)$ and a cyclic fiber with inadmissible
coordinate projections. [NCE, Theorems 2.2 and 6.1–6.2][NCE]
allow arbitrary cyclic donors in their mass certificate and give the
lower in (RRN.37). [D3, Theorems 2.3 and 4.1][D3] supply the
exact depth-three value and improved upper. The present source
does not claim a numerical improvement. JTC, SRP and GCB citations
refer to the immutable public source objects at
`7ab6d62df2a8206382bc9152d4e27c28ddcee6af`; their mathematical
conclusions remain ordinary fallible suppliers.

**Convention 9.2 (precise existing Lean interfaces).** In
[NativeDepthPatterns][D5N], `original_present_transport` assumes
`subtree a u = some t`; Proposition 7.3 uses that actual presence
condition. `original_prefix_locality` assumes equality of original
replies through the requested word length. Neither declaration
supplies a subtree or constructor array to the reader.

In [FiniteNaturalJoin][D5J], `join_covers` takes both `Covers left e`
and `Covers right e` for the same total assignment `e`. Its join
retains compatible rows; it gives no automatic existence of a global
assignment, no weighted all-size estimate and no native operational
bridge. Theorem 5.2 instead proves its actual realization and
one-lift correspondence explicitly.

The declarations `finite_root_minimax` in [NativeFiniteRootMinimax][D5M]
and `effective_native_birth_provenance` and `returned_native_reader`
in [NativeEffectiveRootCriterion][D5E], together with their
[minimax Blueprint][BM] and [criterion Blueprint][BE], concern
the complete predecessor row after a certified actual substitution.
The latter criterion assumes a prefix-free cut, a complete row with
nonempty `OriginFiber` and $r\ge1$, and its installed reader runs
on the substituted source with compatible acquired image values.
Its finite attained root chart and same-$r,q$ decision supply no
all-length cap for the stationary original task. No transfer of that
endpoint is claimed. These are source correspondences, not new Lean
verification of this volume.

**Convention 9.3 (source-verified primary literature).** The following
are credited `literature-attested` intermediates or explicit boundaries
of transfer.

| Primary source | Exact correspondence and limit |
| --- | --- |
| Maximilien Gadouleau, Adrien Richard and Éric Fanchon, *Reduction and Fixed Points of Boolean Networks and Linear Network Coding Solvability*, Proposition 7 and §II, [version 1][GRF] | Eliminating a loop-free coordinate of a finite-alphabet coding function preserves fixed points through reconstruction. Unary-component elimination is proved directly in §3. The native full-factor tables, same-coordinate guards and actual one-Read implementation require §§4–7 and are not inferred from a fixed-point count. |
| G. David Forney Jr., *Codes on Graphs: Fundamentals*, §2.2, [version 2][Forney] | Equality constraints identify repeated variable occurrences. CBN §6 supplies the corresponding owned-potential identity; (RRN.18) preserves the same single ownership after the new seed elimination. No independent-replica or linear-code assumption is used. |
| Thomas Mejstrik and Ulrich Reif, *A Hybrid Approach to Joint Spectral Radius Computation*, §1.1 and §3, [version 2][MR] | The setting is a finite family of fixed-dimension square matrices, with product growth and finite-tree/invariant-polytope certificates. No such fixed-dimension representation of all overlapping native owned-seed networks, with both required pressure inequalities, has been established here. Those certificates therefore provide no cofinal native verifier. |
| Brigitte Mossé, Sasha Pignol and Elisabeth Remy, *On a theorem of François Robert*, Theorem 1, [version 1][Robert] | A circuit-free Boolean regulatory graph has one synchronous fixed point and convergence in at most its number of coordinates. The four-reply fixed-point propagation here is proved directly; it is not a physical-time assertion and supplies no weighted overlap bound. |

The inspected functional-network and matrix-certificate sources do
not supply the missing native all-size cofinality theorem. This is a
bounded source correspondence, not a claim that no such theorem
exists. The normal form uses the finite functional relation itself;
no graph-entropy, tensor-norm or matrix-radius identity is assumed
without its missing representation and inequality directions.

**Convention 9.4 (bounded exact verification).** In-memory exact
calculations checked the following finite cases, without retained
experiment files. At $d=1,n=2$, all
$(3+2\cdot3^4)^2=27\,225$ complete templates were evaluated on
all nine actual tuples. Original and normalized solution sets agreed
in every case; $8\,748$ were empty. The representative-star shape,
unique owner-reply reconstruction and the rational product-weight
identity, including zero weights, were checked on these same cases.

At $d=2,n=2$, $512$ deterministically generated complete templates
were evaluated on all $121$ actual tuples each; $499$ were empty.
The same set equality, reconstruction and weighted identities held.
Separately, $196$ directly generated owned-seed networks on those
ports checked the inverse guarded construction and the realization
bijection. Of them $51$ had an empty seed domain and $108$ had
a singleton domain; no-seed networks and repeated seed incidences
were included. The scan-letter identities were checked for depths
one through seven. These bounded checks test the stated constructions;
the arbitrary-size conclusions rest on the proofs, and no convergence,
physical-efficiency or Lean-certification claim follows from them.

[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[NPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[NCM]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[D3]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[JTC]: https://github.com/the-omega-institute/trureturing/blob/7ab6d62df2a8206382bc9152d4e27c28ddcee6af/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_TARGET_CERTIFICATES.md
[SRP]: https://github.com/the-omega-institute/trureturing/blob/7ab6d62df2a8206382bc9152d4e27c28ddcee6af/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SINGLE_RESIDUAL_PRESSURE.md
[GCB]: https://github.com/the-omega-institute/trureturing/blob/7ab6d62df2a8206382bc9152d4e27c28ddcee6af/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GRAPH_COVER_BETHE_BOUNDARIES.md
[D5N]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5J]: ../../../D5/S0/Certificates/FiniteNaturalJoin.lean
[D5M]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.lean
[D5E]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.lean
[BM]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.md
[BE]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.md
[GRF]: https://arxiv.org/html/1412.5310v1
[Forney]: https://arxiv.org/html/1306.6264v2
[MR]: https://arxiv.org/html/2308.05244v2
[Robert]: https://arxiv.org/html/2502.13750v1

## 追加锚（本行以下为增补区）

## 10. Two actual source slices and one literal geometry

**Definition 10.1 (binary and ternary slot sources).** Retain the whole
original task of Definition 1.1 and Assumption 1.2, including every
variable shape in $\mathcal F_D$, all requests $\mathcal P_D$, and every
subsequently supplied authentic count. For the following restrictions
only, fix $D\ge1$, put $N=2^{D-1}$, and list the words
$w_1,\ldots,w_N\in\{L,R\}^{D-1}$ in lexicographic order. Write
$a_i=Rw_i$, so every $a_i$ is an original permitted request of length
$D$. Use the two alphabets of actual trees

$$
Q_2=\{\alpha,\beta\},\qquad
Q_3=\{\alpha,\beta,C_0\},\qquad C_0=\langle\alpha,\alpha\rangle.
\tag{RRN.38}
$$

For $s\in\{2,3\}$ and $x\in Q_s^N$, insert $x_i$ at position $w_i$
of the perfect ordered height-$(D-1)$ scaffold, obtaining $v_x$, and
set $t_x=\langle\alpha,v_x\rangle$. For $D=1$ the scaffold is its
single slot. Every $v_x$ belongs to $S_D$, has height at most $D$,
and determines $x$ uniquely. Thus

$$
\mathcal C_{s,D}=\{v_x:x\in Q_s^N\}\subseteq S_D,
\qquad |\mathcal C_{s,D}|=s^N,
\qquad t_x\in\mathcal F_D.
\tag{RRN.39}
$$

A slice is a set of actual possible sources used to test an original
competitor. It is not an extra promise, known shape or acquired array
given to that competitor. All its restricted code fibers may remain
arbitrarily correlated. When a separate task is explicitly restricted
to this slice, that restriction is public and the full request menu and
count timing are retained.

**Lemma 10.2 (every finite literal on the same source).** On the
binary slice, the only nonconstant literal words are $a_i$, and each
reports the label $x_i$. On the ternary slice, the only nonconstant
words are $a_i,a_iL,a_iR$. The reply at $a_i$ distinguishes all three
values of $x_i$; either child word replies alpha for $x_i=C_0$ and
absent for $x_i\in\{\alpha,\beta\}$. Every other finite original-root
word is constant on the slice. In particular every literal has at most
$s$ replies on the $s$-ary slice, and each nonconstant word concerns
one uniquely specified slot and has length at least $D$.

Proof. The original root is branch. Its left child is alpha and every
strict extension of that left child is absent. In the right cone,
a word ending strictly before a slot ends at a scaffold branch. A word
reaching a slot has the unique form $a_i z$. At $z=\varepsilon$ it
reads that slot's constructor. A binary slot is a leaf, so every
nonempty $z$ is absent. A ternary slot is either a leaf or the fixed
pair $C_0$; suffixes of length one have the stated replies, and every
suffix of length at least two is absent in all three cases. These
cases include all finite words, irrespective of their length or their
relationship to the requested target. $\square$

## 11. Alternative query menus and preparation on every execution

**Definition 11.1 (menus at an attained name).** Fix $s\in\{2,3\}$ and
an original correct preparation and reader. On the slice put

$$
B_e=\{x\in Q_s^N:E(t_x)=e\},\qquad
I_s=\{e:B_e\ne\varnothing\},\qquad m=|E[\mathcal F_D]|.
\tag{RRN.40}
$$

For each $e\in I_s$, the reader's choice at any $p\in\mathcal P_D$
is zero Reads or one literal fixed by $e,D,p$ before the reply and
before any authentic count. Let $J_e$ be the set of distinct selected
words, over all these requests, whose reply is nonconstant on the
entire $s$-ary slice, and put $b_e=|J_e|$. A selected word constant
only on $B_e$ is still counted if it varies on the whole slice.
Zero-Read branches contribute no word. This finite menu counts
alternative addresses across requests, not simultaneous observations
or acquired memory. Write $T(x)$ and $A(x)$ for the actual preparation
Read count and submitted-letter sum on $t_x$, with repetitions charged.

**Theorem 11.2 (signatures, execution cylinders and counting).** For
all such competitors, every $e\in I_s$ satisfies

$$
|B_e|\le s^{b_e},\qquad
s^N\le\sum_{e\in I_s}s^{b_e},\qquad
\max_{e\in I_s} b_e\ge N-\log_s m.
\tag{RRN.41}
$$

On every individual terminating preparation execution on $t_x$ with
$e=E(t_x)$,

$$
T(x)\ge\max\{N-b_e,0\},\qquad
A(x)\ge D\max\{N-b_e,0\}.
\tag{RRN.42}
$$

For every integer $b\ge0$, the number of slice sources assigned menus
of size at most $b$ obeys

$$
|\{x:b_{E(t_x)}\le b\}|\le m s^b.
\tag{RRN.43}
$$

Proof. If $x,y\in B_e$ give the same reply at every word in $J_e$,
then their reader executions have the same query and reply for every
request: a query outside $J_e$ is slice-constant, or no query is made.
Thus their final predictors agree for every request. At $p=a_i$ and
subsequent count $k=0$, correctness gives the same constructor of
$x_i$ and $y_i$. The constructor identifies the actual symbol in
$Q_s$, so $x=y$. The reply-profile map on $B_e$ is injective. Lemma
10.2 bounds each of its $b_e$ coordinates by $s$ values, proving the
first inequality. Summing over the partition of $Q_s^N$ gives the
second; $|I_s|\le m$ gives the third. Summing only fibers with
$b_e\le b$ proves (RRN.43).

For (RRN.42), fix one complete preparation execution. Let $r$ be the
number of distinct slots touched by its nonconstant words from Lemma
10.2. Keep the actual symbols in these $r$ slots fixed and vary every
other slot freely. Every such input follows exactly the same
preparation transcript, including termination and its complete exported
name: induct on the executed actions, since each constant query has
the same reply and each nonconstant executed query concerns one of the
fixed slots. Hence this cylinder, of cardinality $s^{N-r}$, lies in
$B_e$. Compare

$$
s^{N-r}\le |B_e|\le s^{b_e}.
\tag{RRN.44}
$$

It follows that $r\ge N-b_e$. At least $r$ actual Reads, each of
length at least $D$, were submitted. Constant queries, repeated slots
and repeated words only increase the two charges. This proves the
claimed bounds on this execution and therefore on every execution.
For ternary slots a child test does not reveal the whole symbol; fixing
that symbol is merely a sufficient condition for following the same
transcript. No claim that every touched symbol was fully acquired is
needed. $\square$

**Corollary 11.3 (mean menu and small-menu fraction).** Give the slice
the analytical uniform law, let $X$ be its slot vector and let
$Y=E(t_X)$. For finite entropy with base-two logarithms,

$$
\mathbb E b_Y\ge N-\frac{H(Y)}{\log_2s}
             \ge N-\log_s m,\qquad
\Pr[b_Y\le b]\le\min\{1,m s^{b-N}\}.
\tag{RRN.45}
$$

Proof. Conditional on $Y=e$, $X$ is uniform on $B_e$. The injective
signature of Theorem 11.2 gives
$H(X\mid Y=e)=\log_2|B_e|\le b_e\log_2s$.
Because $Y$ is a deterministic function of $X$,
$H(X)=N\log_2s=H(Y)+H(X\mid Y)$.
Average the conditional bound and use $H(Y)\le\log_2m$.
The probability estimate is (RRN.43) divided by $s^N$.
The uniform law is a counting device; it is not a source prior,
source-dependent request or independence assumption inside $B_e$.
$\square$

## 12. Exact restricted frontiers and a paid full-family consumer

**Theorem 12.1 (simultaneous slice resource frontier).** Consider the
explicitly slice-restricted task, with public $D\ge1$ and
$s\in\{2,3\}$, and otherwise the preparation, complete export,
all-request reader and authentic-count requirements of Assumption 1.2.
Fix an integer menu budget $b\ge0$ and put $c=\max\{N-b,0\}$.
The minimum complete attained alphabet under $b_e\le b$ at every
attained name is exactly

$$
M_{s,b}^{\rm slice}(D)=s^c.
\tag{RRN.46}
$$

The minimum worst preparation Read count and letter sum are
simultaneously $c$ and $Dc$. In fact every admissible procedure pays
at least these two charges on every execution, and one procedure attains
both on every execution. Thus, for integer upper budgets $m_0\ge1$,
$Q,A\ge0$, the three upper bounds on names, preparation Reads and
letters are jointly feasible exactly when

$$
m_0\ge s^c,\qquad Q\ge c,\qquad A\ge Dc.
\tag{RRN.47}
$$

No bound on installed tables, local work or controller size is included
in this equivalence.

Proof. Theorem 11.2 applies unchanged to a correct slice reader. Its
partition bound gives $s^N\le m_0s^b$, together with $m_0\ge1$.
Its execution bound proves the two acquisition lower bounds.

For simultaneous attainment, before any request Read exactly
$a_1,\ldots,a_c$ and export their ordered $c$ symbols. Every one of
the $s^c$ names is attained. The fixed public schedule pays exactly
$c$ Reads and $Dc$ letters. Retain only the fixed-length symbol word;
the paid export and isolation service removes all other accessible
preparation dependence. For $c=0$ the name is constant and preparation
makes no Read.

After $p=Rq$ arrives, if $|q|<D-1$ its endpoint is a scaffold branch
and has the constant branch trajectory. Otherwise $p=a_i$ for a unique
slot. Use its retained symbol when $i\le c$, and otherwise Read the
one actual word $a_i$ from the same stationary source. The three
possible root trajectories are

$$
\begin{array}{c|ccc}
\text{slot}&k=0&k=1&k\ge2\\\hline
\alpha&\alpha&\beta&\mathsf{branch}\\
\beta&\beta&\mathsf{branch}&\mathsf{branch}\\
C_0&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}.
\end{array}
\tag{RRN.48}
$$

These follow directly from $\rho$; a pair remains a pair under every
iterate. Equivalently their factors are $(2,1),(1,0),(0,0)$, as in
Convention 2.1. Output that factor before the authentic count and use
(RRN.4) afterwards with no more Reads. The menu at every name is
exactly the $N-c=\min\{b,N\}$ unretained slot words. Its maximum
late literal length is $D$ when a query occurs. This proves every
upper assertion and the joint feasibility criterion. $\square$

**Proposition 12.2 (actual full-family implementation of the frontiers).**
For each $D,s,b,c$ as above there is a correct procedure on the entire
original variable-shape $\mathcal F_D$ with exactly

$$
|S_D|-s^N+s^c
\tag{RRN.49}
$$

complete attained names. Its restriction to the canonical slice has
the fibers and late menus of Theorem 12.1. On every original source,
sufficient preparation resources are exactly the public scan charges

$$
2^D-1\text{ Reads},\qquad
\max|\text{literal}|=D,\qquad
(D-1)2^D+1\text{ letters}.
\tag{RRN.50}
$$

Its late reader uses zero Reads or one actual original-root literal of
length $D$. The construction is a full-family consumer of the slice
frontier, without an optimality assertion for (RRN.49).

Proof. Use Theorem 7.1's paid scan of every $Rq$, $q\in W_D$,
including absent words, to compute $u=\pi_D(v)$. Install the following
finite public naming table on $S_D$. For $u=v_x\in\mathcal C_{s,D}$,
assign the name consisting of its first $c$ slot symbols. Give every
other $u\in S_D$ its own singleton name, disjoint from the slice
names. The number of names is (RRN.49), and every one is attained
because $\pi_D$ fixes $S_D$. Export only the complete fixed-width
name; isolate the acquired array, membership tests and all other
source-dependent workspace under Assumption 1.2. The number, maximum
length and length sum of the submitted words are (RRN.50).

At a singleton name the canonical state supplies every requested
factor with zero late Reads. At a slice name use Theorem 12.1's reader.
For every original source assigned that name, canonicalization preserves
both its actual reply at the chosen boundary word and its requested
factor. In particular an actual branch at a terminal slot need not
have the unobserved children of $C_0$: its root trajectory is still
constantly branch. Thus the reader works on the entire inverse image
of its canonical fiber, for all original shapes, targets and authentic
counts. Every source-bearing operation is a stated original-root Read;
no actual subtree, shape tag, copied source or acquired selector is
supplied as an input. Table generation, membership work and the paid
services remain separate resources. $\square$

## 13. Consequences for original optimal codes and sparse-port compilers

**Corollary 13.1 (extensive selectable menus at the original optimum).**
Choose, for each $D$, any attaining original preparation and reader
with complete alphabet $M_1(D)$. At each $D$ evaluate its menus on the
uniform $s$-ary actual slice, with expectation denoted $\mathbb E_s$.
Then, for $s=2$ and $s=3$,

$$
\liminf_{D\to\infty}2^{-D}\mathbb E_s b_{E(t_X)}
\ge\frac12-\frac{\lambda}{\log_2s}
>\frac12-\frac{3}{16\log_2s}.
\tag{RRN.51}
$$

The same lower bound holds with the expectation replaced by the maximum
over attained slice names. In particular the mean binary-menu lower
limit exceeds $5/16$, and the mean ternary-menu lower limit exceeds
$3/8$.

Proof. Substitute $m=M_1(D)$ in (RRN.45), divide by $2^D$ and use
$N/2^D=1/2$ and the credited existence of
$\lambda=\lim_D2^{-D}\log_2M_1(D)$. The strict upper
$\lambda<3/16$ is [D3, Theorem 4.1][D3Menu]. For the last ternary
comparison, $3>2^{3/2}$ implies $\log_2 3>3/2$. A maximum is at
least its mean. This is a necessary address-selection resource for
optimal original codes; it is not a new lower endpoint for $\lambda$.
$\square$

**Theorem 13.2 (finite obstruction to a sparse-port compilation).**
For every $D\ge11$, let $\mathfrak S_D$ be the class of otherwise
unrestricted correct original procedures for which, on the ternary
slice,

$$
b_e\le3\,2^{D-3}\qquad(e\in I_3).
\tag{RRN.52}
$$

Every procedure in $\mathfrak S_D$ has strictly more complete retained
names than one existing paid correct procedure on the whole original
$\mathcal F_D$. Consequently no compiler can send every original
competitor to $\mathfrak S_D$ without increasing its complete attained
alphabet. The compiler may change all fibers, recolor globally and
replace preparation; those allowances do not remove the obstruction.

Proof. Theorem 11.2 forces each member of $\mathfrak S_D$ to have

$$
m\ge3^{\,2^{D-3}}.
\tag{RRN.53}
$$

For the comparison use precisely [D3, Theorem 4.1][D3Menu]'s paid
full-family construction. With $N_D=|S_D|$, it supplies an alphabet of
at most $H_{N_D}u_D$ names, where

$$
u_3=760/289,\qquad u_{D+1}=u_D^2+1,\qquad
N_D+1\le2^{2^D},\qquad
u_6=\frac{197235044275447727251205}{48661191875666868481}.
\tag{RRN.54}
$$

The exact positive-integer comparison $u_6+1<2^{12}$ is D3's
(D3.39). Since $u_D\ge1$,
$u_{D+1}+1\le(u_D+1)^2$. For $D\ge6$ this gives
$u_D<2^{3\,2^{D-4}}$. Also
$H_{N_D}\le1+\ln N_D<2^{D+1}$. Thus that paid construction uses
strictly fewer than

$$
2^{D+1+3\,2^{D-4}}
\tag{RRN.55}
$$

names. Finally $3^{16}=43046721>33554432=2^{25}$, and
$2^{D-7}\ge D+1$ for $D\ge11$: it holds at eleven and persists
on doubling the left side. Hence

$$
3^{2^{D-3}}>2^{25\,2^{D-7}}
\ge2^{D+1+24\,2^{D-7}}
=2^{D+1+3\,2^{D-4}}.
\tag{RRN.56}
$$

This strictly separates (RRN.53) from the actual competitor. Its paid
preparation has (RRN.50)'s bounds and its one late literal has length
at most $D$, by the same D3 theorem. There is therefore a lawful
full-family compiler input that no output in the defined class can
match in alphabet size. Every such output is itself an original
competitor and satisfies the lower regardless of its new fibers.
$\square$

In particular a request-independent common probe, or a fixed menu of
at most $3\,2^{D-3}$ actual port alternatives per name, belongs to this
excluded class. The count in (RRN.52) is weaker than the total address
range, because slice-constant alternatives are discarded. No assertion
that a published supplier requires this restriction is made.

## 14. Static signals across one source cut

**Definition 14.1 (a target-independent replacement signal).** For a
nonempty fiber $B_e$ of either slice, a static signal is an arbitrary
map $H_e:B_e\to\mathcal H_e$, independent of the later request,
together with a common decoder from $e,D,p,H_e(x)$ to the complete
factor $\Gamma_p(t_x)$ for every $x\in B_e$ and
$p\in\mathcal P_D$. Equivalently it may produce a predictor correct
for every subsequently supplied authentic count. Put
$c_e=|H_e[B_e]|$. This allows much more than one literal reply and
therefore relaxes a proposed fixed-probe replacement.

**Theorem 14.2 (exact same-source-cut capacity).** For every arbitrary
correlated nonempty $B_e$,

$$
\min c_e=|B_e|.
\tag{RRN.57}
$$

More precisely place the $N$ slot coordinates below one node of a
fixed finite Full tree, and place the public request coordinate outside
that node, with promise $B_e\times\mathcal P_D$ and task
$f_e(x,p)=\Gamma_p(t_x)$. Among total extensions of this task to
$Q_s^N\times\mathcal P_D$, the minimum response capacity at that
source cut is exactly $|B_e|$. The minimum reachable source-message
alphabet of fixed-tree protocols is the same. All other node resources
are left unrestricted in this statement.

Proof. If $H_e(x)=H_e(y)$, the decoder gives identical answers for
every $p$. At a slot where $x_i\ne y_i$, choose $p=a_i$ and use
$k=0$ in the equivalent predictor form. The root constructors differ,
a contradiction. Thus $H_e$ is injective on $B_e$. Sending the index
of $x$ attains $|B_e|$ abstractly.

For the extension assertion, the response row of a source assignment
is the function of all complementary request values. Every total
extension must give the specified responses on $B_e\times\mathcal P_D$;
the preceding slot argument distinguishes all $|B_e|$ of these rows.
Conversely select $x_0\in B_e$ and define a finite retraction
$g:Q_s^N\to B_e$ fixing $B_e$ and mapping its complement to $x_0$.
The total extension

$$
\widetilde f_e(x,p)=\Gamma_p(t_{g(x)})
\tag{RRN.58}
$$

has exactly $|B_e|$ response rows at that source cut. A fixed-tree
protocol can propagate the full source-coordinate tuple within that
subtree and send $g(x)$ at the cut; the root receives it and the
request and decodes (RRN.58). Conversely equal source messages with
the same exterior request give equal root outputs, proving the
protocol lower. The coordinate sets are disjoint, alphabets finite
and nonempty, and the promise is nonempty. This is an exact
specialization of the resource correspondence in
[FixedTreeCommonExtension.result][FTMenu] and its [owning
narrative][FTBMenu]. It does not implement native acquisition: that
fixed-tree model gives leaf coordinates to encoders and full child
message tuples to mergers. $\square$

**Corollary 14.3 (global signal and paid acquisition costs).** If a
static-signal architecture is correct on every original source, its
restriction to either slice satisfies

$$
\sum_{e\in I_s}c_e\ge s^N.
\tag{RRN.59}
$$

If $c_e\le c_D$ for every slice name, then $m c_D\ge s^N$.
Consequently a sequence of these architectures with
$\log_2c_D=o(2^D)$ has

$$
\liminf_{D\to\infty}2^{-D}\log_2m
\ge\tfrac12\log_2s>3/16.
\tag{RRN.60}
$$

It cannot preserve original optimal alphabet sizes, since their rate
is $\lambda<3/16$. A single common four-valued signal is a special
case. If the signal is retained beside $E$ before the request, the
joint complete attained alphabet on the slice is itself at least
$s^N$. Any deterministic initially source-blind literal preparation
that actually acquires this joint pair pays at least $N$ Reads and
$DN$ letters on every slice execution; these bounds are attained
in the restricted task by reading all $a_i$.

Proof. Sum $c_e\ge|B_e|$ over the partition to get (RRN.59).
Then $m c_D\ge s^N$, and taking normalized logarithms proves
(RRN.60). The pairs $(e,H_e(x))$ distinguish all slice inputs,
so their attained cardinality is $\sum_e c_e\ge s^N$ as well.
For the acquisition claim, if an execution left a slot untouched,
the transcript cylinder from Theorem 11.2 would contain at least
$s\ge2$ inputs with the same joint export. This contradicts
injectivity. Thus every one of the $N$ slots is touched by a
nonconstant word of length at least $D$. The fixed full slot scan
attains both charges. The lower concerns actual acquisition of the
joint pair, not a separately supplied free signal. $\square$

The source-cut statement keeps one actual slot vector across all
counterfactual requests. The native one-Read interface instead lets
$p$ select the submitted address, so a leaf request selects $a_i$
and receives only that slot's reply. Such controlled selection is not
a one-way static source message across this cut. A transfer that
retains this direction of selection is not excluded by Theorem 14.2.
Neither that theorem nor Theorem 13.2 excludes lawful finer cuts,
global pressure certificates or unrestricted effective approximation.

## 15. Public entries and the complete pretarget alphabet

**Proposition 15.1 (one-call factor-output controller with its entry
consumer).** Fix $D\ge2$ and the binary slice. Consider the following
explicit auxiliary architecture. The pretarget source-dependent code
is constant. After $p$ arrives, it selects an entry in $Q\sqcup H$.
Thereafter $p$ is not an input: each running state in $Q$ fixes one
actual original-root word and, after its reply, a successor; each halt
in $H$ outputs a fixed temporal factor. Every required execution
terminates with at most one Read and serves all subsequent authentic
counts. The exact minimum installed size and exact minimum post-target
entry range are simultaneously

$$
K=|Q|+|H|=N+3,\qquad r_{\rm entry}=N+1,
\tag{RRN.61}
$$

while the complete attained pretarget alphabet is one.

Proof. A leaf request $a_i$ has two possible factors, $(2,1)$ and
$(1,0)$, so it cannot enter a halt. A single query at any word other
than $a_i$ is constant or reads another independent slot, by Lemma
10.2. Two inputs agreeing on that reply and differing at slot $i$
then require different outputs. Thus the running entry for $a_i$
must query $a_i$, forcing $N$ distinct running entries. At least
three halts are required for the two leaf factors and the branch
factor $(0,0)$. The latter is needed because $D\ge2$ supplies the
internal target $R$. Its entry cannot equal a leaf entry: with no
subsequent $p$ input, that entry already produces a leaf factor on
each attained reply, whereas $R$ must always produce branch.
Therefore at least $N+1$ entries and $N+3$ total states are needed.

Attain both by installing one running state at every $a_i$, two
leaf-factor halts and one branch-factor halt. Leaf replies lead to
their corresponding halts; complete unused reply edges with existing
halts. Every internal target enters the branch halt directly.
Preparation makes no Read and exports one fixed name. The installed
address tables and the public entry distinction carry no acquired
source dependence. All actual queries have length $D$.

The direct consumer is the initial-state resource of
[NativeLiteralMoore.NativeLiteralFeasible][MooreMenu]. In that
predicate the acquired code is itself a map from supplied
$\operatorname{ImageValues}(C)$ into $Q\sqcup H$, and its attained
range is bounded by $r$. If an adapter absorbs the original public
request into such an entry and thereafter removes $p$, the range
required by this auxiliary architecture is $N+1$, not the pretarget
source-code cardinality one. Equating those two resources would
misprice this concrete service. Conversely keeping $p$ as an external
input or paying its entry range is not excluded. Proposition 12.2
with $s=2,b=N$ realizes this constant-name slice reader inside an
actual paid full-family code, so the distinction also applies on that
attained original name. This is a consumer of the separate entry
accounting, not a new predecessor-row synthesis theorem. $\square$

## 16. Supplier scope, resource correspondence and the open programme

**Convention 16.1 (attribution and exact supplier contracts).** The
signature count specializes Proposition 8.1's representative-capacity
principle; injective signatures, deterministic decision-tree cylinders,
finite entropy and one-way indexing are mature mathematical ingredients.
Sections 10–15 give repository-derived consequences for actual native
literal selection and acquisition, including the exact restricted
frontiers and the defined compilation obstructions. No worldwide
originality claim is attached to them. All source correspondences below
use the committed public snapshot
`17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b`.

Theorem 7.1 supplies the paid canonical scan and preservation of every
original optimum; the frontiers do not replace it. D3 supplies the
fractional recurrence, its paid full-family implementation and
$\lambda<3/16$, reused in §13. [NCE, Theorems 16.1 and 17.1 and
Corollary 17.2][NCEMenu] supply the credited positive asymmetric
fixed-law pressure and original lower, so the retained interval is

$$
\frac18\log_2\frac{7792603}{3038031}\le\lambda<\frac3{16}.
\tag{RRN.62}
$$

The lower endpoint in (RRN.62) is the credited bound of that existing
supplier. None of the menu or static-signal bounds is a
new memory-rate endpoint or an assertion of fixed-law global optimality.

The exact declaration `FixedTreeCommonExtension.result` assumes a
finite Full tree, disjoint sibling coordinate sets, finite nonempty
coordinate alphabets, a nonempty possibly correlated promise and a task
on that promise. Its implementations receive leaf values and full
child tuples, and its canonical protocol uses representative choice.
It equates upward closures and attained coordinatewise-monotone costs
for one total extension and one fixed tree. Its root decoder is not
a charged literal source query. Theorem 14.2 computes one specified
cut of that interface; it does not give a uniform original-task bridge.

The exact declaration `NativeLiteralMoore.finite_literal_synthesis`
assumes a prefix-free finite cut $P$, an actual origin $u_0$, current
row $C=\operatorname{canonicalRow}(P,\rho(u_0))$, and upper budgets
$r,K,q,\ell$ with $r,K\ge1$. It is equivalent to
`NativeLiteralFeasible` for the complete predecessor fiber. Its
code receives already acquired $\operatorname{ImageValues}(C)$; the
controller runs on the stationary current image $\rho(u)$ and
outputs the whole predecessor row $\operatorname{canonicalRow}(P,u)$.
Its [owning narrative][MooreBMenu] separately requires paid acquisition,
export, installation, isolation, one-update authentication and entry.
The theorem permits encoder/table reselection. It supplies neither an
original pretarget preparer nor all late targets and authentic counts,
and no all-length native cap follows from its finite decision.
Proposition 15.1 concerns only the explicitly defined entry conversion;
it does not refute that synthesis theorem.

Kowshik–Kumar, [arXiv:1105.0240v2, §III-B, Theorem 4, Lemma 2 and
Example 1][KKMenu], supplies a primary comparison. The response-function
construction of Theorem 4 permits simultaneous representative
substitution on the Cartesian coordinate universe. For arbitrary joint
support, Lemma 2 is an all-cut feasibility condition for the specified
encoders, and Example 1 exhibits coupled encoder choices on diagonal
support. These statements do not supply paid original-root acquisition
or turn target-controlled selection into a static message. No theorem
from that paper is needed for the elementary proofs above, and no
separate optimization over child encoders is imposed on original fibers.

**Convention 16.2 (one source and separately priced resources).** In
every construction $t$ is the same actual stationary initial tree
through preparation and the zero/one later Read. Public scaffolds,
slot orders, naming tables and installed address alternatives are
source-independent descriptions. Their generation, installation,
storage and lookup are separate finite resources; source dependence
is acquired only by the charged actual literals. Merely distinguishing
requests in a public table creates no acquired memory. An analytical
union over all requests gives no observer simultaneous query replies.
An analytical retraction in Theorem 14.2 is not an installed free
source-identification port.

Every attaining preparation in Theorem 12.1 has its explicit charge
$c,Dc$, and its full-family consumer has (RRN.50)'s charge. Fixed
allocation and fixed-width export leave only the stated complete name;
access isolation and handoff remove all other source-dependent control,
buffers, lengths, timing and transcript fields under Assumption 1.2's
paid service. Work and temporary storage before export, post-request
workspace, final predictor, literal construction and submitted lengths,
count representation, entry, authentication, continuity, isolation and
physical time remain separate costs. The slice predictors have three
factor values; the general factor bound remains Convention 7.4's
$\lceil\log_2(2D+1)\rceil+1$ bits. No cost-preserving normalization
of an arbitrary preparation is asserted.

The recovered object is the selected factor and hence its full
subsequent authentic-count reply trajectory through (RRN.4). The static
signal, when required to answer every request, must instead distinguish
the full slot vector on its fiber. Neither task recovers an unknown age,
source identity, hidden history, physical geometry or authentication
from those mathematical factors. The restricted tasks and extra signal
requirements do not replace the original competitors defining $M_1(D)$.

**Open problem 16.3 (unchanged effective all-size obligation).** The
original question of §8.2 and [NPC, Definition 8.1][NPCMenu] remains:
construct a total computable $V(d,\mu,C,\pi)$ whose every acceptance
proves

$$
\forall n\ge1\ \forall\text{ complete native templates }\Theta,
\qquad \sum_{x\in C_\Theta}\prod_{i=1}^n\mu(x_i)\le C^n,
\tag{RRN.63}
$$

and whose accepted rational endpoints satisfy, for every $d\ge1$
and rational $\epsilon>0$,

$$
\exists\mu,C,\pi:\quad
V(d,\mu,C,\pi)\ \text{ and }\ -\log_2C>\sigma_d-\epsilon.
\tag{RRN.64}
$$

Here $\mu$ ranges over rational probabilities on the whole $S_d$,
$C>0$ is rational, and arbitrary correlations, donor cycles, actual
guards, repeated seed occurrences, compatibility zeros and each full
joint block weight once are retained. Equivalently one may seek a
uniform effective length error of the form (RRN.36) with an effective
tail modulus. No such verifier, cofinality theorem or length error is
constructed by the slice frontiers or by either finite supplier.
Soundness, finite verifiability, total computability and
optimizer-cofinality remain separate requirements. In particular the
local-to-global completion and loss control in COK §9.3 and GDB §11
are not supplied by (RRN.57).

The material constraint for an operational common-extension route is
now explicit: it must preserve extensive request-selected literal
alternatives, or pay the quantified static source-cut signal cost.
For a controller route it must also distinguish the complete pretarget
source alphabet from public post-target entries. These statements
exclude precisely those replacements, including arbitrary recoloring,
and leave other global mechanisms open. General exact $M_1(D)$,
sharp $\lambda$, effective all-size certification and the broader
minimal-relations/internal-observer and space/time/boundary/memory
mutual-recovery programme remain unresolved. All statements here are
ordinary mathematical arguments, without a kernel-certification or
full-programme-completion claim.

[D3Menu]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[NCEMenu]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[NPCMenu]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[FTMenu]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/D5/S3/Observer/Separation/FixedTreeCommonExtension.lean
[FTBMenu]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/Blueprint/D5/S3/Observer/Separation/FixedTreeCommonExtension.scribe.cs
[MooreMenu]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.lean
[MooreBMenu]: https://github.com/the-omega-institute/trureturing/blob/17de5db8995ffd6391ab2b5dc3a2a6b5d3496b6b/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.scribe.cs
[KKMenu]: https://arxiv.org/html/1105.0240v2

## 追加锚（本行以下为增补区）

# Complete native control and the exact joint resource frontier

## 1. Original sources, complete states and supplied correspondences

**Assumption 1.1 (the entire acquired task).** Fix the finite acquired
input of [CAR, Assumption 1.1 and Definition 3.1][CAR]. Its entire fiber
$D$ is nonempty and cycle-covered. Sources are all the nonempty finite
ordered free trees satisfying that input, in the native algebra

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\end{aligned}
\tag{NRF.1}
$$

More explicitly, for the given old cut $P$, old complete row $R$,
literal history $H_0$ and signed history $H_{\rm rel}$, the domain is

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{NRF.2}
$$

A signed record $(a,p,b,s,\bowtie)$ imposes

$$
p\in\operatorname{Pos}(\rho^a u)\ \land\
s\in\operatorname{Pos}(\rho^b u)\ \land\
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_s,
\qquad \bowtie\in\{=,\ne\}.
\tag{NRF.3}
$$

Both endpoint guards are mandatory for either sign. The whole old
exterior, repeated occurrences of each old class, all distinct-class
inequalities, every literal and every relation outside the target
remain imposed jointly. Entry is the same original-root register
$\rho^N u$ at the common authenticated epoch $N$, at least every
acquired epoch. The acquisition, payment, retention, authentication
and complete accessible-state cut are precisely CAR's hypotheses.
They supply no additional source-dependent timing, cache or selector.

The target is the original complete $R_Q(u)$ for the given finite
prefix-free original cut $Q$: the entire concrete marked exterior,
the originally reached holes in canonical address order, and their
complete whole-subtree equality partition. A target address absent
at epoch zero does not become a target hole through later growth.
No representative-per-output domain replaces (NRF.2).

**Definition 1.2 (complete native tables).** Use [CAR, Definition
11.1][CAR]. A table has a nonempty finite set $E$, common initial state
$e_*$, and exactly one fixed instruction at each state:

$$
\mathsf{Read}(p_e),\qquad \mathsf{ApplyRho},\qquad
\mathsf{Halt}(Y_e).
\tag{NRF.4}
$$

Here $p_e$ is one finite literal word over $\{L,R\}$. Its four
successors, for replies absent, $\alpha$, $\beta$ and branch, are
fixed. An update has one fixed successor and applies $\rho$ once to
the actual register. A halt carries one literal complete row and is
absorbing. Reads do not alter the register. Root, repeated and absent
reads are legal. Each instruction and its successors are shared by
all sources and every visit.

The number $|E|$ includes unreachable states and all accessible
program positions, mutable selectors, retained replies and output
distinctions. There is no additional online epoch, history, chart,
source witness, descriptor interpreter, address generator or cache.
The operation convention is one whole-word read and one whole-row
halt. Fixed words, output rows, the table and retained common data
have arbitrary finite installation, paid separately. State cardinality
does not bound their literal sizes.

For a prescribed $K\in\mathbb N$, let $\mathcal C_K$ be the tables
with $|E|\le K$ which, for every $u\in D$, halt from
$(\rho^N u,e_*)$ with $R_Q(u)$. This is a pointwise termination
requirement on the entire domain. In particular $\mathcal C_0$ is
empty.

**Definition 1.3 (actual resources and upper budgets).** For a table
$C\in\mathcal C_K$ and the same original source $u$, put

$$
\begin{aligned}
c_C(u)&=(q_C(u),a_C(u),\ell_C(u)),\\
\ell_C(u)&=\sum_{\text{actual read calls at }p}|p|,\\
b(C)&=(\sup_D q_C,\sup_D a_C,\sup_D\ell_C).
\end{aligned}
\tag{NRF.5}
$$

The first coordinate counts chronological raw read calls, including
repetition and absence. The second counts actual post-entry unit
forward updates. A root read contributes one to $q$ and zero to
$\ell$; halt contributes zero to all three. Terminal updates, when
present in the installed table, are actual charged updates.

Write $\overline{\mathbb N}=\mathbb N\cup\{\infty\}$ and define

$$
\begin{aligned}
\operatorname{Feas}_K(B)
&\ \Longleftrightarrow\
 \exists C\in\mathcal C_K\ \forall u\in D\quad c_C(u)\le B,
 \qquad B\in\overline{\mathbb N}^{\,3},\\
\mathcal F_K
&=\{B\in\mathbb N^3:\operatorname{Feas}_K(B)\}.
\end{aligned}
\tag{NRF.6}
$$

A coordinate equal to infinity imposes no bound. These are simultaneous
whole-fiber upper budgets, rather than a requirement to attain the
three entries of $B$ on a single source.

**Definition 1.4 (the exact source and word interfaces).** The
suppliers [CAR, Theorem 3.2, Lemma 4.1 and Theorem 6.2][CAR] give a
finite chart family $\mathcal A$ and a bijection

$$
\coprod_{\eta\in\mathcal A}
\{\mathbf n\in\mathbb N^{d_\eta}:
                  \operatorname{Adm}_\eta(\mathbf n)\}
\ \xrightarrow[\text{bijection}]{\Theta}\ D.
\tag{NRF.7}
$$

They give effective first-order Presburger predicates
$\operatorname{Adm}_\eta$ and
$\operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m)$, the latter
equivalent to equality of the two entire original $Q$ rows.
Admission includes every conjunct of (NRF.2) and every guard of
(NRF.3). Charts of dimension zero are allowed.

For the common finite skeleton depth $H$, physical descriptors have
finitely many types: a literal word of length at most $H$, or a pair
$(z,e)$ with $|z|=H$ and $e\in\{L,R\}$ and natural parameters
$(t,l)$ satisfying

$$
l\ge1,\qquad
l-1\le t-\omega(e)\le2(l-1),\qquad
\omega(L)=1,\quad\omega(R)=2.
\tag{NRF.8}
$$

The long descriptor represents a word $zs$ with suffix length $l$,
weight $t$ and final letter $e$, and has exact literal length $H+l$.
The subtractions in (NRF.8) are integer notation for equivalent
addition inequalities. Let $V(\delta)$ be validity and
$|\delta|$ its length. Every physical word has such a descriptor.
Every valid descriptor has an effectively constructible literal
realization of exactly that length.

For each reply $c$ the effective Presburger predicate satisfies

$$
\operatorname{Reply}_{\eta,c}(\mathbf n,j,\delta)
\ \Longleftrightarrow\
r_{\rho^j\Theta_\eta(\mathbf n)}(p)=c
\tag{NRF.9}
$$

for every admitted tuple, every natural epoch $j$, and every literal
realization $p$ of $\delta$. One realization works simultaneously on
all charts and epochs. In particular an absent response is not
replaced by a reached subtree, and a suffix ending in $L$ retains its
endpoint threshold.

For later all-infinite budgets, [NPS, Theorems 3.2 and 4.2][NPS]
supply exact unbounded finite-halting support and a terminating
decision of $\mathcal C_K\ne\varnothing$, with literal extraction.
They use exactly (NRF.7)--(NRF.9), one shared instruction per state
and one complete row per halt. The result permits arbitrary finite
installation, with no action or address horizon.

## 2. A paid-length stopping bound on the unchanged table

**Theorem 2.1 (only executed addresses enter the bound).** Fix any
native table with $s$ states, any finite source $u$ and entry epoch
$N$. If its actual run halts and has total submitted literal-address
length at most $L\in\mathbb N$, then

$$
q_C(u)+a_C(u)
\ \le\ s\bigl(\max(0,2L+2-N)+1\bigr).
\tag{NRF.10}
$$

No bound is imposed on an installed word that is not read on this
run. Consequently, if $C\in\mathcal C_K$ and
$\sup_D\ell_C\le L$, the same installed table has the uniform
action bound

$$
T_\ell(K,L,N)=K\bigl(\max(0,2L+2-N)+1\bigr)
\tag{NRF.11}
$$

on the entire original fiber.

Proof. Use the all-finite-source identity [JRF, (2.4)][JRF]:

$$
j\ge w(p)+2\quad\Longrightarrow\quad
r_{\rho^j u}(p)=\mathsf{branch},\qquad
w(p)=\#_L(p)+2\#_R(p).
\tag{NRF.12}
$$

It applies to every word, including the root, and every finite source.
On the given halting run each actually read word has length at most
$L$, because its nonnegative length is one summand of the actual
total. Thus its weight is at most $2L$. Set
$b=\max(0,2L+2-N)$ and $J=N+b$.

Before epoch $J$, a repeated pair $(j,e)$ would repeat the same
physical register $\rho^j u$ and the same complete control state.
Determinism would then repeat forever. A halting run therefore has
at most $sb$ actions starting at epochs $N,\ldots,J-1$. This count
includes an update that first enters epoch $J$, if it occurs.

At epochs at least $J$, every read actually encountered on this run
returns branch by (NRF.12). Its update successor also depends only
on the state. Suppose a nonhalt state were repeated in this tail.
The intervening segment would be a directed cycle consisting of
update successors and branch successors. Every read word on that
cycle was actually read, hence has weight at most $2L$, and will
continue to return branch at every later epoch. Starting at the
second visit therefore repeats that cycle forever, contradicting
halt. There are at most $s$ tail actions.

This argument does not declare all installed words short or all
installed reads eventually branch by epoch $J$. An arbitrarily long
unused word outside the repeated segment is irrelevant. It also
does not redirect a successor, delete a read, remove an update,
change a halt row, or add an online clock. Combining the two counts
proves (NRF.10); $s\le K$ gives (NRF.11). The source was arbitrary,
so the uniform conclusion keeps every original source. $\square$

**Proposition 2.2 (zero-length and halting boundaries).** Theorem
2.1 includes zero-length reads, late entry, early halt and cycles.
Its halting premise cannot be removed, even when $L=0$.

Proof. In Theorem 2.1, $L=0$ permits actual root reads; the
argument does not require positive address cost per raw call.
Entry with $N\ge2L+2$
has $b=0$, so the whole run is in the tail and uses at most $s$
actions. An initial halt has zero actions. An early halt before
$J$ uses only the first count. A read-only repeated configuration
cannot escape to a later epoch, since it executes no update.
An update-containing cycle in the tail cannot escape through a
later change of one of its read replies, since those replies are
already permanently branch. Before the tail, both kinds of cycles
are covered by the actual epoch-state argument.

The halting premise is essential. A one-state table reading the
root and sending every reply back to itself has total length zero
on every finite prefix and never halts. Hence a length cap alone,
without totality, is not a termination certificate. $\square$

**Definition 2.3 (the three available action horizons).** For finite
caps $k,d,L$ and a prescribed state bound $K$, put

$$
\begin{aligned}
T_q(K,k)&=k+K(k+1),\\
T_a(K,d)&=d+K(d+1),\\
T_\ell(K,L,N)&=K\bigl(\max(0,2L+2-N)+1\bigr).
\end{aligned}
\tag{NRF.13}
$$

The first two are the unchanged-table bounds of [CAR, Corollary
12.2][CAR]. A halting run with $q\le k$ has at most $k+1$
update-only blocks, each of at most $K$ updates. A halting run
with $a\le d$ has at most $d+1$ read-only blocks, each of at most
$K$ reads on an unchanged register. The third is Theorem 2.1.
Thus any one finite coordinate bounds the actions of every
successful candidate obeying that coordinate, without a
state-preserving normalization hypothesis.

## 3. Exact bounded descriptions with shared instructions and halts

**Definition 3.1 (finite paths are descriptions of the original graph).**
Fix a natural action horizon $T$ and enumerate the finite graph
choices of [CAR, Theorem 12.1][CAR]: a state set
$E=\{0,\ldots,s-1\}$, $1\le s\le K$, initial state, instruction
types and all required successors. Choose one descriptor type for
each read state. The resulting numeric descriptor tuple
$\boldsymbol\delta$ is shared by every source and visit.

Let $\Pi_T$ contain all formal paths from $e_*$ ending at their first
halt after at most $T$ nonhalt actions. Paths retain repeated
states, repeated and absent reads, and every update including
updates after the final read. No path continues through a halt.
The path of length zero is included precisely for an initial halt.

For a path $\pi$ and its $i$th read, let $e_i$ be its read state,
$c_i$ its reply and $a_{\pi,i}$ the number of preceding actual
updates. Define

$$
\begin{aligned}
A_{\eta,\pi}(\mathbf n;\boldsymbol\delta)
&=\operatorname{Adm}_\eta(\mathbf n)\ \land\
 \bigwedge_{i:\,\mathrm{read}}
 \operatorname{Reply}_{\eta,c_i}
       (\mathbf n,N+a_{\pi,i},\delta_{e_i}),\\
v_\pi(\boldsymbol\delta)
&=\left(q_\pi,a_\pi,
       \sum_{e\in E_R}m_{\pi,e}|\delta_e|\right),\\
S_{\eta,h}(\mathbf n;\boldsymbol\delta)
&=\bigvee_{\pi\in\Pi_T:\,\mathrm{end}(\pi)=h}
                         A_{\eta,\pi}(\mathbf n;\boldsymbol\delta).
\end{aligned}
\tag{NRF.14}
$$

Here $q_\pi,a_\pi,m_{\pi,e}$ are fixed natural counts of the
finite path, not symbolic unbounded repetition counts. Every read
test on a path uses the same source tuple. The paths are proof
objects; their vertices are not installed as additional states.

**Definition 3.2 (a bounded linear-cost design sentence).** Let
$\Psi_\pi(\boldsymbol\delta)$ be any specified finite conjunction
of linear inequalities on $v_\pi(\boldsymbol\delta)$, with fixed
integer coefficients and constants. For a chosen graph and
descriptor types require validity, and impose

$$
\begin{aligned}
\mathrm{Total}_T:\quad&
\bigwedge_\eta\forall\mathbf n\
\left(\operatorname{Adm}_\eta(\mathbf n)
       \Longrightarrow\bigvee_{h\in E_H}
                         S_{\eta,h}(\mathbf n;\boldsymbol\delta)\right),\\
\mathrm{Cost}_T:\quad&
\bigwedge_{\eta\in\mathcal A,\,\pi\in\Pi_T}\forall\mathbf n\
\left(A_{\eta,\pi}(\mathbf n;\boldsymbol\delta)
       \Longrightarrow\Psi_\pi(\boldsymbol\delta)\right),\\
\mathrm{Shared}_T:\quad&
\bigwedge_{\eta,\theta,h}\forall\mathbf n\,\forall\mathbf m\
\left(
S_{\eta,h}(\mathbf n;\boldsymbol\delta)\land
S_{\theta,h}(\mathbf m;\boldsymbol\delta)
\Longrightarrow
\operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m)
\right).
\end{aligned}
\tag{NRF.15}
$$

In the last line $\eta,\theta$ range over $\mathcal A$ and
$h$ ranges over $E_H$. All implications lie within the displayed
universal quantifiers.
The design sentence is

$$
\exists\boldsymbol\delta\quad
\left(\bigwedge_{e\in E_R}V(\delta_e)\right)
\land\mathrm{Total}_T\land\mathrm{Cost}_T\land\mathrm{Shared}_T.
\tag{NRF.16}
$$

Take its finite disjunction over graphs and descriptor types.
For $K=0$ this disjunction is false.

**Proposition 3.3 (exact priced application of bounded synthesis).**
The sentence (NRF.16) is effectively decidable and extracts a literal
table with at most $K$ complete states when true. Its finite outer
disjunction is equivalent to the existence of a table in
$\mathcal C_K$ whose runs have at most $T$ nonhalt actions and
satisfy the specified path cost inequalities on every source.
Unvisited installed words remain unbounded.

Proof. Reuse the shared-instruction and shared-whole-halt path
construction in [CAR, Theorem 12.1][CAR], with fixed horizon $T$.
The following identifies the additional price predicate and both
operational directions.

For fixed paths, (NRF.14) is Presburger by (NRF.9).
Each $m_{\pi,e}$ is a numeral. Length is constant for a short
descriptor and $H+l_e$ for a long one, so the third coordinate
of $v_\pi$ and every prescribed $\Psi_\pi$ are linear. The source
dimensions and all chart and path disjunctions are finite.
Consequently (NRF.16), including the cross-source shared-halt
condition, is first-order Presburger over nonnegative integers.
[Ginsburg--Spanier, Theorem 1.2][GS] decides its truth or falsity;
arbitrary first-order quantifier alternation is allowed.

A successful original candidate with the claimed horizon supplies
one enumerated graph by relabeling states only. Give each read
state the descriptor of its actual word. This keeps every successor
and every word's responses and length on all sources. Its actual
trace on $\Theta_\eta(\mathbf n)$ satisfies $A_{\eta,\pi}$.
Conversely, for this fixed descriptor valuation every satisfied
$A_{\eta,\pi}$ describes the unique actual trace: induct on
actions using (NRF.9) at $N+a_{\pi,i}$. No earlier halt is crossed.
Its cost is exactly $v_\pi$. This proves totality and all cost
clauses. Two sources ending at the same installed halt have the
same whole output, proving the shared clause.

For a true sentence, extract a common natural descriptor tuple.
This can be done by enumerating tuples and deciding each remaining
formula after truth of the existential sentence has been decided.
Positive existence guarantees this extraction terminates; a
negative answer never depends on that enumeration. Realize one
literal word per read state. For each halt $h$, decide whether
some $S_{\eta,h}$ is nonempty. If it is, extract an admitted tuple,
expand its actual finite source and compute its entire original
$Q$ row. Install that row at $h$. The shared clause makes it
correct for every source and every path reaching $h$. For an
unreachable halt use the row of any source in the nonempty $D$.

Every original source has its tuple by (NRF.7); totality supplies
a terminal compatible path, and action induction identifies it
with the actual run of the installed graph. Its cost inequalities
and whole output follow from (NRF.15). No witness, path position,
epoch or chart becomes online control. Literal installation is
finite and separately paid. Only reachable terminal paths impose
prices, so an instruction never visited by any source has no
induced length bound. $\square$

## 4. Every pattern of finite and infinite upper bounds

**Theorem 4.1 (exact mixed-budget native feasibility).** Under
Assumption 1.1, for every $K\in\mathbb N$ and
$B=(B_q,B_a,B_\ell)\in\overline{\mathbb N}^{\,3}$,
$\operatorname{Feas}_K(B)$ is decidable. A true answer extracts
one literal table in $\mathcal C_K$ satisfying all finite bounds
on every original source. A false answer excludes every such
table, including arbitrarily long finite installations.

Proof. If $K=0$, the answer is false. If every coordinate is
infinite, apply [NPS, Theorem 4.2][NPS] directly, with the original
fiber, $N,Q,K$ and the interfaces of Definition 1.4. Its exact
unbounded support theorem supplies both totality and extraction;
no action horizon is inserted into this case.

Otherwise compute at least one available horizon from (NRF.13):
$T_q(K,B_q)$ when $B_q$ is finite,
$T_a(K,B_a)$ when $B_a$ is finite, and
$T_\ell(K,B_\ell,N)$ when $B_\ell$ is finite. Use the minimum
of the available horizons. Every successful candidate respecting
the finite coordinates has that action bound on its unchanged
table, by Definition 2.3. In Proposition 3.3 impose exactly

$$
\Psi_\pi=
\bigwedge_{i\in\{q,a,\ell\}:\,B_i<\infty}
                        (v_{\pi,i}\le B_i).
\tag{NRF.17}
$$

That proposition is therefore necessary for every allowed
comparator, as well as sufficient. Its true and false decisions
terminate and its extraction preserves the prescribed states.
The eight choices of finite-coordinate set are exhausted:
the empty set uses NPS, and each of the seven nonempty sets
uses its actual available horizon. Neither an infinite coordinate
nor an unvisited word is silently capped. $\square$

**Proposition 4.2 (exact profiles of an extracted or supplied table).**
Every $C\in\mathcal C_K$ has finite $b(C)\in\mathbb N^3$.
For a supplied literal table, membership in $\mathcal C_K$ is
decidable under Assumption 1.1. When membership holds, its exact
coordinate maxima and its exact worst same-run rational weighted
sum are computable, with original-source witnesses for each
maximum.

Proof. For the supplied table put

$$
W_C=\max\bigl(\{0\}\cup\{w(p_e):e\in E_R\}\bigr),\qquad
T_C=|E|\bigl(\max(0,W_C+2-N)+1\bigr).
\tag{NRF.18}
$$

[CAR, Theorem 11.2][CAR] bounds every halting execution by $T_C$.
Unlike (NRF.11), this table-specific bound may inspect all
installed words; here those words are already finite input.
Enumerate its formal first-halt paths through at most $T_C$
actions and use their fixed-word instances of (NRF.14).
Totality of this finite union is decidable. For each terminal
path, equality of $R_Q(\Theta_\eta(\mathbf n))$ to the actual
installed row is decidable by [CAR, Lemma 4.1(4)][CAR].
These tests, together with $|E|\le K$, are exactly membership:
any actual halt is inside the bound, and compatible paths are
actual executions. A failure to halt cannot be hidden beyond
this bound.

For a member, decide the nonemptiness of every terminal path
support and extract one admitted tuple for each nonempty support.
There are finitely many such paths and at least one, since
$D\ne\varnothing$. They cover every source, and their costs
$v_\pi$ are fixed finite triples for this literal table. Thus

$$
\begin{aligned}
b_i(C)&=\max_{\pi:\,\exists\eta,\mathbf n\ A_{\eta,\pi}}
                              v_{\pi,i},\\
W_\lambda(C)&=
\max_{\pi:\,\exists\eta,\mathbf n\ A_{\eta,\pi}}
                              \lambda\cdot v_\pi.
\end{aligned}
\tag{NRF.19}
$$

In each maximum, the extracted tuple of a maximizing path expands
to an original source realizing it. Different coordinates may
select different sources. For the weighted maximum, one path and
one source realize the entire sum. All predicates retain the full
fiber; the finite witnesses do not replace it. $\square$

## 5. A terminating complete Pareto extraction

**Definition 5.1 (finite certificates and their missing region).**
For finite $A\subseteq\mathbb N^3$, write

$$
\uparrow A=\{x\in\mathbb N^3:\exists v\in A,\ v\le x\}.
\tag{NRF.20}
$$

For each $v\in A$ choose a coordinate $f(v)$ with
$v_{f(v)}>0$. If a member has all coordinates zero, no such
choice exists. For each resulting function $f$, define a mixed
upper box by

$$
B_i^f=
\min\{v_i-1:v\in A,\ f(v)=i\},\qquad
\min\varnothing=\infty.
\tag{NRF.21}
$$

For $A=\varnothing$ there is one empty function and its box is
$(\infty,\infty,\infty)$.

**Proposition 5.2 (an exact negative completeness test).** For any
finite list $A$ of feasible finite budgets, there is a feasible
budget outside $\uparrow A$ if and only if

$$
\bigvee_f\operatorname{Feas}_K(B^f)
\tag{NRF.22}
$$

is true. This is a terminating decision. A true answer supplies a
literal table with at most $K$ complete states whose exact worst
vector lies outside $\uparrow A$; a false answer proves
$\mathcal F_K=\uparrow A$.

Proof. For $x\in\mathbb N^3$,

$$
x\notin\uparrow A
\ \Longleftrightarrow\
\bigwedge_{v\in A}\bigvee_{i:\,v_i>0}(x_i\le v_i-1)
\ \Longleftrightarrow\
\bigvee_f(x\le B^f).
\tag{NRF.23}
$$

This is a finite distributive expansion, including the empty
conjunction and empty disjunction cases. If a feasible finite
$x$ is outside, its witness table satisfies one of these mixed
boxes. Conversely a table extracted for a true mixed box has a
finite exact vector $b(C)$ by Proposition 4.2; this vector lies
in that box and is outside $\uparrow A$. Theorem 4.1 decides all
finitely many disjuncts, including the all-infinite empty-list
case. If they are all false, no feasible finite budget is outside.
Since every element of $A$ is feasible and feasibility is upward
closed, this is precisely equality with $\uparrow A$. $\square$

**Theorem 5.3 (complete effective coordinate Pareto basis).** There
is a terminating procedure returning

$$
\mathcal B_K=\operatorname{Min}(\mathcal F_K),\qquad
\mathcal F_K=\uparrow\mathcal B_K,
\tag{NRF.24}
$$

where $\mathcal B_K$ is finite and may be empty. For every
$v\in\mathcal B_K$ it returns a literal table $C_v\in\mathcal C_K$
with $b(C_v)=v$, and an original-source witness for each coordinate
maximum. Moreover, for every extended budget,

$$
\operatorname{Feas}_K(B)
\ \Longleftrightarrow\
\exists v\in\mathcal B_K\quad v\le B,
\qquad B\in\overline{\mathbb N}^{\,3}.
\tag{NRF.25}
$$

Proof. Start with $A=\varnothing$. Apply Proposition 5.2. On a
false answer return $A$. On a true answer extract its table and
compute $x=b(C)$ by Proposition 4.2.

Search the finite integer box $[0,x]$ using Theorem 4.1 and
choose a feasible $y\le x$ minimizing $y_q+y_a+y_\ell$. There
is at least one, namely $x$. This $y$ is a global minimal member
of $\mathcal F_K$: any strictly smaller feasible vector would
also belong to $[0,x]$ and have strictly smaller sum. Extract a
table for $y$. Its exact vector is at most $y$, is itself feasible
and hence equals $y$ by minimality. Retain that table and the
coordinate witnesses of Proposition 4.2, append $y$ to $A$, and
repeat the completeness test.

Every appended $y$ is outside the old $\uparrow A$: otherwise an
old $v\le y\le x$ would contradict the choice of $x$. All retained
vectors are globally minimal, so no later vector can strictly
dominate or be dominated by a different earlier one.

For termination, use the elementary finite-dimensional
well-quasi-order argument behind Dickson's lemma. Every infinite
sequence of naturals has an infinite nondecreasing subsequence:
if some value occurs infinitely often, use it; otherwise each
finite initial interval occurs only finitely often, so successively
select increasing values at increasing indices. Apply this
subsequence argument first to the first coordinate, then to the
second, then to the third. Any infinite sequence in $\mathbb N^3$
has two terms in their original order with the earlier term at
most the later one coordinatewise. The sequence appended above
cannot have such a pair. Hence only finitely many iterations occur.
Each iteration and its extraction terminate, so the entire
procedure terminates.

At its terminal false answer Proposition 5.2 proves completeness,
and every retained vector is globally minimal. Conversely a
minimal feasible vector lies above some retained vector by
completeness and therefore equals it. This proves (NRF.24).
This procedure does not stop merely because the retained list is
an antichain or because no new vector has yet been enumerated:
its stopping signal is the exact negative decision (NRF.22).
The well-quasi-order argument proves that this signal must
eventually occur.

Finally every successful table has a finite exact vector. A
witness for an extended budget therefore has some finite vector
$x\le B$, and (NRF.24) supplies $v\in\mathcal B_K$ with
$v\le x\le B$. The converse follows from the retained attaining
table for $v$. This proves (NRF.25), including the case of an
empty feasible class. $\square$

## 6. Same-run rational objectives, including zero-weight faces

**Definition 6.1 (a separate minimax objective).** For a supplied
$\lambda\in\mathbb Q_{\ge0}^3$, define

$$
W_\lambda(C)=\sup_{u\in D}
 \bigl(\lambda_q q_C(u)+\lambda_a a_C(u)
                   +\lambda_\ell\ell_C(u)\bigr),\qquad
W^*_{\lambda,K}=\inf_{C\in\mathcal C_K}W_\lambda(C).
\tag{NRF.26}
$$

The infimum of the empty class is $\infty$, with no attaining
table. Every run cost and every individual table maximum is
finite by Proposition 4.2. The sum in (NRF.26) uses one actual
source before the supremum. In general it is not
$\lambda\cdot b(C)$; [NSF, Example 11.7][NSF] supplies an
explicit native sourcewise distinction. Coordinatewise
domination of maxima does not supply sourcewise domination of
weighted profiles.

**Theorem 6.2 (exact rational threshold decisions).** For every
$\lambda\in\mathbb Q_{\ge0}^3$ and supplied finite rational
$z\ge0$, the sentence

$$
\exists C\in\mathcal C_K\quad W_\lambda(C)\le z
\tag{NRF.27}
$$

is decidable, with literal extraction when true. This includes
every pattern of zero weights.

Proof. If all weights vanish, (NRF.27) is exactly
$\mathcal C_K\ne\varnothing$, decided by NPS Theorem 4.2.
Assume some weight is positive. Multiply by a common positive
integer denominator $d$ for the weights, and put
$w=d\lambda\in\mathbb N^3$ and $B=\lfloor dz\rfloor$.
The weighted run sums $w\cdot c_C(u)$ are integers, so
(NRF.27) is equivalent to their being at most $B$ for all $u$.

Choose any $i$ with $w_i>0$. Nonnegativity of every summand gives,
on the same run,

$$
w\cdot c_C(u)\le B
\quad\Longrightarrow\quad
c_{C,i}(u)\le\left\lfloor B/w_i\right\rfloor.
\tag{NRF.28}
$$

Consequently every candidate satisfying the objective has an
action horizon from (NRF.13), using this coordinate. One may
take the minimum over all positive-weight coordinates. Apply
Proposition 3.3 at that horizon with the single path inequality

$$
w_q q_\pi+w_a a_\pi+
w_\ell\sum_{e\in E_R}m_{\pi,e}|\delta_e|\le B.
\tag{NRF.29}
$$

Its coefficients are numerals, so it is Presburger even when
descriptor lengths are unbounded. The action horizon follows
from the actual objective of every allowed comparator; it is
not an installation cutoff or an extra promise. Zero-weight
coordinates contribute zero to (NRF.29) and impose no independent
price restriction. In particular a sole positive length weight
uses Theorem 2.1, not a deletion of free root reads. A sole
positive update weight uses the read-block bound in (NRF.13).
The necessity and sufficiency of Proposition 3.3 give the
exact threshold decision and extraction. $\square$

**Theorem 6.3 (exact attained weighted optimum).** Under Assumption
1.1, for every prescribed $K$ and every
$\lambda\in\mathbb Q_{\ge0}^3$, one can decide whether
$\mathcal C_K$ is empty. If it is nonempty, the finite rational
value $W^*_{\lambda,K}$ is effectively computable and is attained
by an extracted literal table with at most $K$ complete states.
An original source attaining that table's worst weighted sum
is also extractible. If the class is empty, the result is
$\infty$ and there is no attainer, including when all weights
are zero.

Proof. Use NPS Theorem 4.2 for emptiness and, in the nonempty
case, a literal table $C_0$. For zero weights the objective is
zero on every source of every table; $C_0$ attains the optimum,
and any original source, obtained from (NRF.7), witnesses it.

Otherwise take $d,w$ as in Theorem 6.2. Compute the exact
integer
$B_0=\max_{u\in D}w\cdot c_{C_0}(u)$
by Proposition 4.2. Test the finite range of integer thresholds
$B=0,\ldots,B_0$ by applying Theorem 6.2 with original weights
$\lambda$ and rational threshold $z=B/d$, and select the least true
one $B_*$. There is a true one since $C_0$ witnesses $B_0$.
Extract a literal table for that threshold.

Its integer worst weighted sum cannot be less than $B_*$:
if $B_*>0$, that would make threshold $B_*-1$ true; if
$B_*=0$, nonnegativity already gives equality. Hence its
value is exactly $B_*/d$. Any table with a strictly smaller
value would likewise have an integer weighted maximum less
than $B_*$ and contradict the same exact negative test.
This proves optimality over every table in $\mathcal C_K$,
not only over a preselected finite installation family.
Proposition 4.2 supplies a source realizing the whole sum.

The coordinate Pareto tables of Theorem 5.3 are not used as
weighted comparators. Each threshold in (NRF.29) is checked on
one actual path of one original source, and (NRF.19) takes
the maximum only after forming that sum. No tuple of unrelated
coordinate maximizers enters this proof. $\square$

## 7. Exact scope of the composed result

**Definition 7.1 (immutable mathematical suppliers).** The source
correspondence used above is the following.

| Supplier | Consumed statement and exact matching |
| --- | --- |
| [CAR §§1, 3--4][CAR] | The nonempty acquired cycle-covered fiber (NRF.2), all signed endpoint guards, the entire-source bijection (NRF.7), and complete original-row equality. No marginal, sampled or representative-per-output source domain is used. |
| [CAR §6][CAR] | Descriptor validity, exact literal length, one global word realization, and the all-chart, all-epoch reply equivalence (NRF.9). Source ranks, epochs and descriptor parameters remain natural arithmetic variables at the stated places. |
| [CAR Definition 11.1 and Theorem 11.2][CAR] | The complete native state contract and the installed-word-dependent stopping bound (NRF.18). The latter is used after literal extraction or for a supplied table, not as a search bound on unknown installations. |
| [CAR Theorem 12.1 and Corollary 12.2][CAR] | Bounded shared-instruction/shared-halt synthesis and unchanged-table action bounds from a finite read or update cap. Proposition 3.3 uses its correspondence with explicit additional linear path prices. |
| [CAR Theorem 12.4][CAR] | The fixed-literal-table membership test in Proposition 4.2 is its candidate check, including comparison against the actual installed whole row. Its bounded installation enumeration is not used to restrict the frontier. |
| [CAR Corollary 13.6][CAR] | A prescribed-state obstruction to transferring the unrestricted-control resource normalization. No zero-update replacement is assumed here. |
| [NPS Theorems 3.2 and 4.2][NPS] | Exact unbounded halting support and prescribed-$K$ decision/extraction on this identical acquired task. These settle the all-infinite box, detect the empty class, and supply a first finite literal comparator for weighted minimization. |
| [NPS Theorem 5.2 and §6][NPS] | Successful installations at a fixed five-state graph can have arbitrarily long actual runs. Its unbounded feasibility sentence does not price a product of symbolic word length and symbolic visit count. |
| [JRF (2.4)][JRF] | Eventual branch replies for every finite source and fixed literal address, including root and originally absent paths. This identity is restricted to actual visited words in Theorem 2.1. |
| [JRF Theorem 3.1 and Lemma 3.2][JRF] | These normalize unrestricted-control services using simulated control and caching. Their resource inequalities do not imply preservation of complete state cardinality; neither transformation is used here. |
| [NSF Theorems 4.3, 6.1, 7.3 and 8.1--8.2][NSF] | Existential native constraints with fixed numeral powers and fixed physical words, fixed-prefix decisions, and finite physical boxes on arbitrary signed fibers. Its $K$ in Theorem 7.3 bounds reads, not complete states. These are overlap boundaries, not a substitute for the uniform descriptor or unrestricted prescribed-state suppliers. |
| [NSF Theorems 9.3 and 10.3, Proposition 10.4][NSF] | Effective recovery criteria for a forward-closed whole fiber or supplied observable invariant charts. A supplied finite prefix selector provides actual observations, but these criteria do not prescribe the complete native state cardinality or supply arbitrary-word synthesis on an arbitrary signed fiber. |
| [Ginsburg--Spanier, Theorem 1.2][GS] | Decision of first-order Presburger sentences over nonnegative integers after the explicit native correspondence. No multiplication of two unbounded quantified variables is passed to this decision. |

Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger
Formulas, and Languages*, Pacific Journal of Mathematics
**16**(2), 285--296 (1966), Theorem 1.2 on page 287 and the
remarks on page 288, give precisely the natural-number sentence
decision and the inequality/universal-quantifier conventions
used in (NRF.15)--(NRF.16).
This Presburger decision result is literature-attested. Finite
Boolean distribution, finite-box minimization and the
finite-dimensional well-quasi-order argument are standard
methods, included inside the native extraction proof. Their
effective native application consumes Theorem 4.1's decision
on every mixed box, including its negative answers.
The executed-length stopping bridge, the composed complete-state
frontier and the zero-weight native threshold construction are
repo-derived ordinary deductions at these hypotheses. They
assert no literature-wide novelty or priority.

**Definition 7.2 (arithmetic and control boundaries).** In
Proposition 3.3 the action horizon is already a fixed numeral
before path enumeration. Thus each visit multiplicity
$m_{\pi,e}$ is a numeral multiplying a descriptor length.
In the all-infinite case there is no length-cost expression:
the proof invokes NPS's phase support at its supplied scope.
Theorems 4.1 and 6.2 do not claim a single Presburger formula
in a variable horizon for all budgets, a semilinear presentation
of all installation/cost profiles, or a decision procedure for
arbitrary nonlinear parameter products.

Every source quantifier ranges over the full admitted chart
domains in (NRF.7). Halt witnesses are construction data used
to write one concrete row, and extremal witnesses are sources
attaining an already verified whole-domain maximum. Neither
kind of witness is given to the running controller or used
to replace the domain. Descriptors, paths, phases, epochs and
the Pareto search are external mathematical descriptions;
the extracted controller is the selected original graph.

**Definition 7.3 (unsettled extensions).** The decisions and
optima proved here concern exactly $\mathcal C_K$ on the
nonempty cycle-covered input. For a general signed fiber
outside that recognition, this volume supplies no replacement
for the uniform arbitrary-word arithmetic interface and NPS
unbounded synthesis hypotheses. NSF's existential fixed-word
decision and supplied-prefix tests alone do not discharge
those missing premises.

The results impose no global installation cap and optimize no
installation price. They also give no asymptotic complexity
bound, implemented solver, Lean kernel verification or physical
realization. Acquisition and the complete access cut remain
hypotheses. Bitwise emission, serialized outputs, physical
timing and complete future-law recovery have separate
contracts. No conclusion here settles those extensions.

[CAR]: https://github.com/the-omega-institute/trureturing/blob/ac159239a7c999bf163bd244eb18ba0a49c0de81/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[NPS]: https://github.com/the-omega-institute/trureturing/blob/d92994d6101179ca79ec60bf329ffc8386987e0a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PHASE_SYNTHESIS.md
[JRF]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[NSF]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf

## 追加锚（本行以下为增补区）

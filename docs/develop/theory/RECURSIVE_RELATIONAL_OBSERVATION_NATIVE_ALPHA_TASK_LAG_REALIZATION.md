# Native alpha task-lag realization at a minimum-alphabet acquired entry

## 1. Fixed tasks, early acquisition and the native source

**Assumption 1.1 (mathematical scope and native contract).** The statements
below are ordinary mathematical deductions, not Lean-kernel-verified
results. Use [NAR, Assumption 16.1][NAR] with its actual finite ordered
trees, complete acquired rows, early export and discard, and stationary
four-reply current port. In particular,

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle,
\qquad T_n=\rho^n\alpha.
\tag{NTL.1}
$$

Fix publicly $m\ge1$, $K\ge0$, a function
$f:\{0,1\}^m\to\{0,\ldots,K\}$, and an integer $D$ with
$r=2^D\ge m+1$. Set $H=K+1$, $q=H+1=K+2$, and
$I=\{0,\ldots,r-1\}$. Write $W_D=(w_j)_{j\in I}$ for the
lexicographically ordered depth-$D$ words. The entire initial domain is

$$
\mathcal A=\{0,\ldots,H\}^{I},\qquad
X_a=\mathcal B_D[(T_{jq+a_j})_{j\in I}].
\tag{NTL.2}
$$

All $r$ original ages vary independently on this cube. Slots
$0,\ldots,m-1$ will carry Boolean coordinates at the selected entry;
slot $s=m$ is the separate visible reference. Any remaining slots are
still independent in (NTL.2). Original offsets $jq$ are never renumbered.
Fix any public nonempty menu $\mathcal M\subseteq2^I\setminus\{\varnothing\}$
containing $S_* =\{s\}$. Here $S$ denotes the displayed slots, and
$Q_S=W_D\setminus\{w_i:i\in S\}$ is the actual cut. Thus $S=I$
allows the empty cut, but no menu member hides every original slot.

The task, menu and encoder rule are fixed before the actual initial
acquisition and before the future choice of $S$ or lag. The encoder
receives the genuinely acquired $R_{\varnothing}(X_a)$, exports just
one finite label $e(a)$, and makes all other source-bearing preparation
state inaccessible. Public tables are common to every $a$. Fix either
$\lambda_0=0$ or $\lambda_0=1$ and allow all $\ell\ge\lambda_0$.
After this same original source's own $\ell$ substitutions, the entire
later row is acquired from

$$
Y(a,\ell)=\rho^\ell X_a
 =\mathcal B_D[(T_{jq+a_j+\ell})_{j\in I}],
\qquad V_S(a,\ell)=R_{Q_S}(Y(a,\ell)).
\tag{NTL.3}
$$

The decoder entry is exactly $(S,e(a),V_S(a,\ell))$, with common
installed control. A complete row includes its literal exterior, reached
and absent guards, and equality and disequality of all hidden whole
subtrees within that row. It contains neither their values nor a hidden
epoch. Its native extra operation is $\operatorname{Read}_{Y(a,\ell)}(p)$
for any finite original-root word $p$, returning exactly
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$. The current source
does not change during these queries. There is no old-source reread,
subtree, age, free comparison, reroot or stronger query operation.

**Definition 1.2 (resources and target).** A reader is a common
deterministic effective controller that terminates correctly on every
history in its stated domain. The global target is the forgotten
substitution lag $\ell$, under (NTL.2)--(NTL.3). For each run let

$$
c_A=(C_A,L_A,P_A),\qquad
C_A=\#\text{ actual Read invocations},\quad
L_A=\sum_{\text{actual Reads at }p}|p|,\quad
P_A=\max\bigl(\{0\}\cup\{|p|:p\text{ submitted}\}\bigr).
\tag{NTL.4}
$$

Repeated, absent, visible and empty-word Reads are all invocations.
An empty relative suffix at $w_j$ is the paid whole word $w_j$ of
length $D$. Local parsing of an already supplied literal row adds no
new source invocation. The retained source-summary alphabet, its binary
representation, acquisition, installed task and encoder tables, source
and row storage, workspace, local computation, address production and
transmission, and output storage have separate resource accounts.
No bounds for these other accounts follow from (NTL.4).

## 2. An early encoder with exactly the native minimum alphabet

**Definition 2.1 (translation chains and the task selector).** For
$a\in\mathcal A$ put

$$
t(a)=\min_{j\in I}a_j,\qquad
v(a)=a-t(a)\mathbf1,\qquad h(v)=\max_j v_j.
\tag{NTL.5}
$$

Every normalized profile has $\min_jv_j=0$. Its full translation chain
in the original cube is
$\{v+t\mathbf1:0\le t\le H-h(v)\}$, of length $q-h(v)$.
For $b\in\{0,1\}^m$ define

$$
v(b)_j=\begin{cases}b_j,&j<m,\\0,&j\ge m,\end{cases}
\qquad t_b=K-f(b),\qquad a(b)=v(b)+t_b\mathbf1.
\tag{NTL.6}
$$

Call exactly these normalized profiles $v(b)$ designated. Define one
encoder on the *whole* cube by least nonnegative residues:

$$
e_f(a)=
\begin{cases}
(t(a)-t_b)\bmod q,&v(a)=v(b),\\
t(a)+1,&v(a)\text{ is not designated}.
\end{cases}
\tag{NTL.7}
$$

The public recognition of a designated profile means its first $m$
coordinates are bits and all remaining coordinates, including the
reference, are zero. This specifies $b$ uniquely. The definition uses
the fixed function $f$, not a later cut, lag or information about an
unacquired source.

**Theorem 2.2 (global feasibility, exact selector and minimum labels).**
For every choice in Assumption 1.1, (NTL.7) is computable from the
genuinely acquired initial row, takes exactly $q$ attained values, and
satisfies

$$
e_f^{-1}(0)=\{a(b):b\in\{0,1\}^m\}.
\tag{NTL.8}
$$

It separates every nonzero common translation of initial ages. It
therefore admits globally correct finite current-port lag recovery on
the full cube, for every $S\in\mathcal M$ and every legal unbounded
lag, under either convention. Among all encoders with that global
recovery property on this cube, $q=K+2$ is the minimum attained
source-summary alphabet. Its fixed-width representation uses
$\lceil\log_2q\rceil$ bits, excluding the other resources in
Definition 1.2.

**Proof.** For each designated $v(b)$, $h(v(b))\le1$ and
$0\le t_b\le K\le H-h(v(b))$. Thus $a(b)$ is a legal original
profile. The reference coordinate of $v(b)$ is zero, so $\min v(b)=0$
even when all bits are one. On its chain, distinct allowed $t$ lie
in an integer interval of length at most $q$; residues $t-t_b$ modulo
$q$ are distinct. Exactly $t=t_b$ receives label zero.

The only normalized profile with $h(v)=0$ is the zero profile,
which is designated by $b=0^m$. Every undesignated chain consequently
has $h(v)\ge1$, hence at most $q-1$ members. Its labels $t+1$ lie
in $\{1,\ldots,q-1\}$ and are distinct. This proves the range
bound, separation along every chain, and (NTL.8). The zero-profile
chain has $q$ members; its residue labels attain every element of
$\{0,\ldots,q-1\}$. Two profiles differing by a common translation
have the same normalized $v$, so the separation is precisely the one
required by [NAR, Theorem 16.5][NAR].

For actual acquisition, [NAR, Reuse 16.2][NAR] supplies the right clock
$c(T_n)=n$ and the acquired factors
$a_j=c(X_a|_{w_j})-jq$. Apply (NTL.5)--(NTL.7) to those parsed
values, export the resulting label, and discard the other acquired
distinctions as required. This is a finite computation on acquired
data, not a free age input. No bound on its table size or work is used.

To spell out the global use of the supplier, a visible slot gives
$z_i=c(Y|_{w_i})-iq=\ell+a_i$. Every hidden exponent lies in

$$
[jq+\max(\lambda_0,z_i-H),\ jq+z_i+H],
\tag{NTL.9}
$$

which contains at most $2H+1$ integers. NAR16.5's literal interval
reader recovers these exponents with at most
$(r-|S|)\lfloor\log_2(2H+1)\rfloor$ fresh calls. Visible
exponents are already parsed. With the whole normalized current
vector $x_j=a_j+\ell$, enumerate compatible $a'$ with the received
code and $x=a'+\ell'\mathbf1$, $\ell'\ge\lambda_0$.
Existence is supplied by the actual history. Two different lags would
give a same-code nonzero common translation, which has been excluded.
Return the unique lag. This proves global feasibility independently
of the special-entry analysis below; the call bound is sufficient,
not asserted optimal.

Finally reuse [NAR, Theorem 16.3][NAR]. The $q$ originals
$a=t\mathbf1$, $0\le t\le H$, with positive lags $q-t$ all have
the identical whole current tree
$\mathcal B_D[(T_{jq+q})_j]$. At any fixed allowed cut they have
the same full later row and all-address replies, but different required
lags. Any globally correct encoder must distinguish these $q$
originals. These witnesses apply under both lag conventions, and they
are in the unchanged independent cube. Together with the attained
range of (NTL.7), they prove the exact minimum. $\square$

The matching of a task selector with that minimum is the additional
interface here. Coloring chains is the elementary finite separation
method; the native lower bound, acquired clock and feasibility theorem
are reused. In particular, declaring the reference age fixed throughout
the source domain would remove the very obstruction used for the
minimum; Assumption 1.1 does not make that change.

## 3. Exactly one genuine acquired Boolean entry

**Definition 3.1 (the selected complete entry).** Put $z_*=K+\lambda_0$.
Let $V_*$ have the depth-$D$ exterior with the entire literal
$T_{sq+z_*}$ displayed at $w_s$, and an address-named hole at every
other original slot. All these holes are reached; their equality
partition consists of singleton classes, with all cross-class
disequalities. Define

$$
E_*=(S_*,0,V_*),\qquad
\ell_b=\lambda_0+f(b),\qquad
Y_b=\mathcal B_D[(T_{jq+z_*+v(b)_j})_{j\in I}].
\tag{NTL.10}
$$

The row description in this definition is justified by actual sources
in the next theorem. It is not permission to install a chosen hidden
partition or substitute a model tree for an actual continuation.

**Theorem 3.2 (both directions of the entire acquired-entry fiber).**
In the full global contract with encoder (NTL.7), the histories giving
entry $E_*$ are exactly

$$
\{(a(b),S_*,\ell_b):b\in\{0,1\}^m\}.
\tag{NTL.11}
$$

This is a bijection of $2^m$ inputs with $2^m$ genuine compatible
histories; their originals and current trees are each pairwise distinct.
Their required lag is exactly $\lambda_0+f(b)$.

**Proof, realization.** By Theorem 2.2, every $a(b)$ is in the
original cube and its early code is zero. Its legal lag is $\ell_b$.
Homomorphic continuation of this one fixed original gives, at every
slot,

$$
jq+a(b)_j+\ell_b=jq+K+\lambda_0+v(b)_j.
\tag{NTL.12}
$$

Thus its actual current tree is $Y_b$. Every skeleton slot is reached,
including a slot whose filling is a leaf. The displayed reference has
$v(b)_s=0$ and is exactly $T_{sq+z_*}$.

For completeness of the hidden partition, at any profile and lag in
the full cube the exponent in slot $j$ lies in
$[jq+\ell,jq+H+\ell]$. For $j<k$,

$$
kq+a_k+\ell-(jq+a_j+\ell)\ge q-H=1.
\tag{NTL.13}
$$

The right clock separates different $T_n$, so hidden fillings at
different original slots are actually unequal. Consequently their
within-row partition is discrete; every self-equality and every
cross-disequality is the stated one. The skeleton fixes the brackets,
and the visible literal fixes all labels and descendant absence guards
outside the holes. These are the complete row components of
[NAR, (NAR.16.6)][NAR] and `canonicalRow_record_iff`, not just a
scalar clock collision. Hence $V_{S_*}(a(b),\ell_b)=V_*$.

**Proof, exclusion of every other history.** Suppose a legal full-cube
history has this entry. Its code zero forces $a=a(b)$ for a unique
$b$ by (NTL.8): normalization of $a$ recovers $v(b)$ and then $b$.
Equality of the complete rows implies equality of their displayed
literal reference trees. Taking the right clock and subtracting $sq$
gives $a_s+\ell=z_*$. Since $a_s=t_b=K-f(b)$, this forces
$\ell=\lambda_0+f(b)$. No additional histories satisfy the entry.
The forward argument already checks all the hidden comparisons, so
none of these histories is removed by a forgotten row constraint.

Different $b$ have different normalized profiles, hence different
$a(b)$ and different originals by the acquired clocks. Their current
trees differ at any bit slot where the bits differ, again by the right
clock. Each alternative uses its own original and that original's
continuation throughout; alternatives are never spliced into one run.
$\square$

**Proposition 3.3 (an optional independent prior producing the same law).**
Fix $S=S_*$. Sample $A$ uniformly from the entire $q^r$-point cube,
and independently sample $L$ uniformly from
$\{\lambda_0,\ldots,\lambda_0+K\}$. Use the actual source $X_A$,
its early encoder and its own $L$ substitutions. The event
$\mathcal E=\{(S_*,e_f(A),V_{S_*}(A,L))=E_*\}$ has probability

$$
\Pr(\mathcal E)=\frac{2^m}{q^r(K+1)}>0.
\tag{NTL.14}
$$

Conditionally on $\mathcal E$, the $2^m$ histories of Theorem 3.2
are equiprobable, so their coordinates $B_0,\ldots,B_{m-1}$ are
independent fair bits. Their lag is $\lambda_0+f(B)$.

**Proof.** Each pair $(a,\ell)$ in this finite independent prior has
probability $1/(q^r(K+1))$. Theorem 3.2 supplies exactly $2^m$
distinct such pairs in the event, all with supported lags. Summing and
dividing proves (NTL.14) and the conditional distribution. Independence
of $A,L$ before conditioning does not assert independence of the
selected history's lag and original afterwards. This prior is a law on
allowed histories, not a restriction of the global recovery domain.
$\square$

## 4. Every literal address and its geometric coordinate price

**Definition 4.1 (adjacent native ages and coordinate prices).** At
$E_*$ put

$$
n_i=iq+K+\lambda_0,\qquad
p_i=w_iR^{\lfloor n_i/2\rfloor},\qquad
d_i=|p_i|=D+\left\lfloor\frac{iq+K+\lambda_0}{2}\right\rfloor
\quad(0\le i<m).
\tag{NTL.15}
$$

The exponent notation denotes a literal string of that many $R$
letters, with its whole original-root prefix. These are the prices
induced by the fixed depth, original offsets and adjacent-age
realization. They are not arbitrary user-prescribed weights.

**Theorem 4.2 (all-address coordinate factorization with shortest words).**
On the entire actual fiber (NTL.11), every finite native word has a
source-independent reply or a reply depending on exactly one bit
$b_i$. A nonconstant reply at a word in bit slot $i$ determines that
bit, and every such word has length at least $d_i$. Word $p_i$
attains $d_i$ and determines $b_i$ in one Read.

**Proof.** Reuse the all-word reply formula of [SLH, Theorem 6.2][SLH]
and [AOF, (AOF.8), Definition 8.2][AOF]. For a nonempty relative word
$u$, let $\omega(u)=\#L(u)+2\#R(u)$. In $T_n$ the complete table is

$$
\begin{array}{c|cccc}
 &\mathsf{absent}&\alpha&\beta&\mathsf{branch}\\ \hline
u\text{ ends in }R&n<\omega(u)&n=\omega(u)&n=\omega(u)+1&n\ge\omega(u)+2\\
u\text{ ends in }L&n\le\omega(u)&\text{never}&n=\omega(u)+1&n\ge\omega(u)+2.
\end{array}
\tag{NTL.16}
$$

At the empty suffix the replies are respectively $\alpha,\beta,$
and branch for $n=0,1,$ and $n\ge2$. This includes the last-edge
reach guard: subtracting a formal weight alone would wrongly allow
some left-ending paths through a leaf. In particular all absent words
remain in the table.

A whole word shorter than $D$ ends in the complete skeleton and
replies branch. Any longer word, including length exactly $D$, has a
unique decomposition $w_j u$. At a reference or remaining slot
$j\ge m$, its tree $T_{jq+z_*}$ is fixed on (NTL.11), so the reply
is fixed. At a bit slot $i<m$, its tree is $T_{n_i+b_i}$, and its
reply is the two-entry public table
$b_i\mapsto\operatorname{Read}_{T_{n_i+b_i}}(u)$.
If the entries differ, the reply determines the bit; if they agree,
the word is constant. This covers every word, including ones leaving
a tree, queries at holes, and queries with an empty suffix.

For shortest length, set $k=\lfloor n_i/2\rfloor$. If $|u|<k$,
then $\omega(u)\le2|u|\le2k-2$, and both $n_i,n_i+1$ are at
least $\omega(u)+2$. Nonempty such words reply branch on both;
the root case is also branch whenever this strict inequality admits
it. Hence no shorter suffix separates the adjacent ages. At $R^k$
the replies are $(\alpha,\beta)$ when $n_i=2k$, and
$(\beta,\mathsf{branch})$ when $n_i=2k+1$. These statements include
$k=0$ and ages zero and one. Adding the prefix gives (NTL.15).
The adjacent-interval price is also the $[n_i,n_i+1]$ specialization
of [AOF, Theorem 9.2][AOF]; the whole-tree exclusion above is what
allows that price to transfer here. $\square$

## 5. Faithful strategies and simultaneous query budgets

**Definition 5.1 (the priced coordinate problem).** A coordinate
classification tree receives an unknown $b\in\{0,1\}^m$ and may
ask for a coordinate $b_i$, adaptively, until it outputs $f(b)$.
Charge one invocation and $d_i$ letters for that query, with run cost

$$
c_T(b)=\left(C_T(b),\ \sum_{\text{queries }i}d_i,
\ \max(\{0\}\cup\{d_i:i\text{ queried}\})\right).
\tag{NTL.17}
$$

Repeated queries, if present, are counted. Correctness and finite
termination are required on all $2^m$ inputs. A native comparator
for $E_*$ satisfies the same conditions on precisely (NTL.11).
Neither model restricts local computation or counts installed states
in this query-cost contract.

**Theorem 5.2 (exact forward transport and sourcewise reverse dominance).**
For every such coordinate tree $T$ there is a native reader $A_T$ with

$$
\operatorname{out}_{A_T}(a(b),\ell_b)=\lambda_0+f(b),\qquad
c_{A_T}(a(b),\ell_b)=c_T(b)\quad\text{for every }b.
\tag{NTL.18}
$$

Conversely every native comparator $A$ for $E_*$ has a coordinate
tree $T_A$ with output $f(b)$ and

$$
c_{T_A}(b)\le c_A(a(b),\ell_b)
\quad\text{coordinatewise for every same actual history.}
\tag{NTL.19}
$$

**Proof, forward.** Replace each request for $b_i$ by the actual
literal word $p_i$ on $Y_b$, and decode its two possible replies
using Theorem 4.2. Induction on the run preserves the coordinate
answers, adaptive choices and termination. Return $\lambda_0$ plus
the tree's output. There is exactly one physical call of length $d_i$
per coordinate request, even for repetitions. Summing and taking the
peak along that one run gives all three equalities in (NTL.18).

**Proof, reverse.** Simulate $A$'s complete control and its received
reply history, with the public fixed entry $E_*$. For each requested
word, compute its case and the two possible replies of Theorem 4.2.
If constant, supply that reply locally. If it depends on $b_i$ and
that bit has already been queried, supply the reply from its actual
cached coordinate value. Otherwise query coordinate $i$ once, retain
that acquired bit, and supply the corresponding reply. This includes
constant absent words, visible rereads, repeated words, and different
words that expose the same bit. A nonconstant query may itself have
an absent reply on one of the inputs; that branch is processed by the
same two-entry table.

On the particular $b$, induction gives exactly the replies $A$ would
receive from the actual unchanged $Y_b$. It therefore makes the
same simulated choices and eventually outputs $\ell_b$. Subtract
$\lambda_0$ for the coordinate output. Each coordinate query is
matched to a distinct actual native invocation on that same history;
Theorem 4.2 gives $d_i\le|p|$ for the matched word. Unmatched native
calls cost nonnegative amounts. This proves the call, sum and peak
inequalities together, rather than matching separate optimizing runs.

Pointwise termination suffices. There are finitely many actual inputs,
and the simulated run is finite on each, so the resulting reachable
coordinate decision tree is finite. No source-dependent runtime cutoff
or hidden input is installed. Locally simulated replies are control
data, not newly acquired physical receipts at the skipped words.
$\square$

**Corollary 5.3 (equal feasible upper budgets and nondominated frontiers).**
For either class let $b(A)$ be the componentwise maximum of its run
costs over the paired histories, and let
$\mathcal F=\{v\in\mathbb N^3:\exists A,\ b(A)\le v\}$.
The native and coordinate $\mathcal F$ are equal, as are their
coordinatewise minimal elements. More strongly, the two classes admit
the same feasible sourcewise upper-budget functions
$B:\{0,1\}^m\to\mathbb N^3$.

**Proof.** Exact forward transport maps any feasible coordinate budget
to the same native budget. Sourcewise reverse dominance maps any
feasible native budget to a coordinate budget below it, for the same
$b$ in every inequality. The two inclusions give both assertions.
The coordinatewise minimal feasible budgets are therefore the same;
each is attained, since any strict slack in the worst vector of its
witness would contradict minimality. Repetitions and unnecessarily
long native words can have strictly larger cost than their reverse
simulation. Equality of all strategy-cost profiles is not asserted.
$\square$

For example, the standard finite decision-tree recursion, used here as
an algorithmic consequence rather than a new decision-tree theorem,
computes this common frontier. At a nonempty partial-assignment cell
$E$ let $\mathcal P(E)=\{(0,0,0)\}$ if $f$ is constant there.
Otherwise range over unexposed coordinates $i$, let
$E_{i,t}=\{b\in E:b_i=t\}$, and use

$$
\mathcal P(E)=\operatorname{Min}\bigcup_i
\left\{
\left(1+\max_t C_t,\ d_i+\max_t L_t,
\ \max(d_i,\max_t P_t)\right):
(C_t,L_t,P_t)\in\mathcal P(E_{i,t})
\right\}.
\tag{NTL.20}
$$

Only nonempty children occur. Each is a strict subcell, and at most
$m$ distinct bits are needed on any path. The choices in each child
are complete *triples for one continuation*. Thus the formula does
not combine separately optimal resources from incompatible strategies.
Coordinate maxima may occur at different inputs; every displayed
budget still belongs to one strategy. This is the same joint-budget
discipline as [AOF §§3--5][AOF] and [JRF, Definitions 1.2--1.3][JRF].
The enumeration need not be efficient in a compact description of $f$.

**Theorem 5.4 (global extension preserving the selected runs).**
Every native comparator for $E_*$ can be extended
to one globally correct reader for encoder $e_f$ on the whole domain
of Assumption 1.1, preserving all its native queries and outputs on
every history in (NTL.11).

**Proof.** The supplied entry is finite and explicit. Test whether
$S=S_*$, the code is zero and the *whole row* is $V_*$; this is
local computation on acquired data. On equality execute the selected
comparator unchanged. On inequality use the globally correct decoder
from Theorem 2.2. The exact fiber theorem makes the first branch
correct on every history that can enter it, and the other decoder is
correct on the remainder. The entry test submits no source queries.
Thus (NTL.18)--(NTL.19) and the conditional frontier also apply to
the restrictions of globally correct readers. Their costs on other
entries are not claimed equal to the selected-entry budgets. $\square$

## 6. Parity as a credited zero-immediate-information consumer

**Proposition 6.1 (uniform actual histories and the joint native price).**
Specialize to $K=1$ and $f(b)=\bigoplus_{i=0}^{m-1}b_i$. Thus
$H=2$, $q=3$, and

$$
d_i=D+\left\lfloor\frac{3i+1+\lambda_0}{2}\right\rfloor.
\tag{NTL.21}
$$

Give the actual histories (NTL.11) the uniform law, equivalently the
conditional law of Proposition 3.3. For any deterministic native
observation procedure whose complete observable transcript leaves at
least one bit unexposed on *every* possible transcript, that transcript
is independent of the required lag. In particular every single native
query carries zero lag information when $m\ge2$.

Every exact parity recovery run must expose every bit, with no
probabilistic qualification needed for this necessity. One reader
jointly attains the exact call, summed-length and peak vector

$$
\left(m,\ mD+\sum_{i=0}^{m-1}
\left\lfloor\frac{3i+1+\lambda_0}{2}\right\rfloor,
\ D+\left\lfloor\frac{3(m-1)+1+\lambda_0}{2}\right\rfloor\right).
\tag{NTL.22}
$$

**Proof.** The information and certificate ingredients are the classical
uniform-parity facts, already used in [WPE, §392 and Proposition
396.9][WPE]. In particular §392.1 gives the normalized two-bit kernel
$\frac12\mathbf1_{y_1\oplus y_2=x}$; its correction governs the
earlier §317 statement. The present use is their transfer to actual
native lag histories and the prices in (NTL.21).

Say a bit is exposed when some issued word has different replies at
its two adjacent slot ages. By Theorem 4.2 a complete transcript fixes
exactly the values of its exposed coordinates. Every assignment of
the remaining bits gives the identical transcript: replay the
deterministic choices, using fixed replies or the already fixed bit
at every step. Conversely a nonconstant reply fixes that bit. Thus
each positive-probability transcript cell is a Boolean subcube,
including its stopping decision, chosen words and all repeated and
absent replies. Local deterministic processing adds no new distinction.

If any bit remains free in such a cell, flipping it pairs even and
odd inputs bijectively. Under the uniform law, conditional parity,
and hence the two possible lags, is exactly fair in every such cell.
If all possible transcripts leave a free bit, this proves independence
and mutual information zero for the transcript random variable. The
free coordinate may depend on the transcript. Merely leaving a bit
free on one branch would only give balance on that branch, not global
independence. One native query exposes at most one coordinate, so
$m\ge2$ suffices for the single-query assertion. At $m=1$, $p_0$
already identifies the lag.

Without using probabilities, if an exact reader halted with bit $i$
unexposed, flipping that bit would preserve its complete run but
change the required output. Both histories are genuine by Theorem
3.2, a contradiction. Its run therefore contains at least one exposing
call for each $i$; these are different calls, each of length at least
$d_i$. This yields the simultaneous sourcewise lower bound
$(m,\sum_i d_i,\max_i d_i)$. Querying each $p_i$ once and taking
the parity attains it on every history. The $d_i$ are nondecreasing,
so this is (NTL.22). For $m=2,D=2$ the attained triples are
$(2,6,4)$ for nonnegative lags and $(2,7,4)$ for positive lags.
$\square$

The probability law is essential to the zero-information statement;
the exact-recovery lower bound instead uses the full support. After
$m-1$ bits have been exposed, one further bit determines parity, so
zero initial one-query information does not mean that every later
query has zero conditional information. Conversely arbitrary biased
input laws need not have the stated independence. This separation of
the joint law from its coordinate marginals agrees with [CG,
Proposition 14.12][CG] and [WPE, Definition 392.2][WPE]. No new XOR
or general synergy theorem is being asserted.

## 7. Recovery quotients, degenerate tasks and all-entry boundaries

**Proposition 7.1 (what is mutually recoverable).** At the selected
entry, lag and task value are mutually recoverable by
$\ell=\lambda_0+f(b)$ and $f(b)=\ell-\lambda_0$. The full
coordinate vector and the actual selected current tree are mutually
recoverable, with the latter-to-former direction attainable by the
paid coordinate words. But the lag output alone, even together with
the common entry, determines the original or current source on this
fiber if and only if $f$ is injective.

**Proof.** The first two formulas and (NTL.12) give the stated maps;
Theorem 4.2 supplies the actual paid recovery of all coordinates.
Theorem 3.2 makes both source maps injective in $b$. Therefore two
different inputs with the same $f$ have the same entry and lag but
distinct originals and current trees. This rules out source recovery
from just that output. Conversely an injective finite public $f$ has
an inverse on its image, so lag identifies $b$ and then both trees.
The recovered object in general is the task quotient
$\{0,1\}^m/{\sim_f}$, where $b\sim_f b'$ means $f(b)=f(b')$.
This is a finite mathematical inverse, not a bound on the cost of
constructing or storing a source. $\square$

**Proposition 7.2 (constant tasks and zero-age edges).** If $f\equiv c$,
the selected entry has exactly $2^m$ histories with lag
$\lambda_0+c$, and its frontier is $\{(0,0,0)\}$. Nevertheless
the full independent cube still requires exactly $q=K+2$ retained
labels for global lag recovery. In particular for $K=0$ the
construction uses $H=1,q=2$, not a collapsed zero-age cube; at
$\lambda_0=0$ the selected lag is zero and the first adjacent-age
query may have an empty suffix.

**Proof.** Nothing in the chain or fiber proofs requires a nonconstant
task or attainment of the top value $K$. A constant output is a
correct zero-query reader on the selected entry. The lower bound of
Theorem 2.2 concerns all initial profiles and all legal lags, so it
continues to apply. At $K=0$, $a(b)=v(b)$ is legal in the
$\{0,1\}^r$ cube. At zero lag the first bit slot contains either
$T_0=\alpha$ or $T_1=\beta$, and its canonical word is just
$w_0$. The word still has $D\ge1$ letters and costs one invocation
if used, though the constant task needs none. $\square$

**Proposition 7.3 (global finite calls do not give a global address cap).**
If $f$ is nonconstant, no globally correct reader for this encoder
and menu has a finite literal-address peak bound uniform over all
entries and legal lags. Its selected-entry frontier remains finite,
and Theorem 2.2 still gives a finite uniform global call bound.

**Proof.** Choose $b,b'$ with different task values. Their codes are
zero and their reference ages $K-f(b)$ and $K-f(b')$ differ.
At displayed singleton $S_*$ they are a zero-read conflict in
[NAR, (NAR.16.7)][NAR]. Theorem 16.6 there therefore rules out a
uniform address cap for this feasible encoder.

Concretely, add $u\ge0$ to both selected lags in (NTL.10). At
each $u$ the complete later entries of the two histories still
agree, including all hidden comparisons, while their outputs differ.
Their every slot exponent is at least $K+\lambda_0+u$. Hence all
whole words shorter than
$D+\lfloor(K+\lambda_0+u)/2\rfloor$ reply branch on both.
A deterministic correct reader must eventually obtain a differing
reply. The length of that word is at least this diverging bound.
Repeating shallow or absent calls does not defeat the equal-history
induction. $\square$

For a constant task this particular two-selected-history witness is
absent. The exact all-entry criterion is still NAR16.6: a fixed
encoder admits a uniform finite word cap exactly when it already
separates every zero-read menu conflict. A constant task at one
entry is not a claim about that condition at every other entry.
Nor does Theorem 3.2 assert a Boolean fiber at every cut or row.

**Assumption 7.4 (resource and realization limits).** Acquisition,
same-source continuation, stationarity, permission and truthful discard
are the native contract's premises. Formula (NTL.6) may evaluate
$f(b)$ to describe a realizing history. It is an existence
construction; it is not an inexpensive algorithm for discovering an
unknown task value from its later reads. The installed encoder may
use the whole public task table, of $2^m$ entries, and may require
other finite public data or computations on the full $q^r$ cube.
These descriptions are independent of the actual acquired source
but are not included in the retained $q$ labels.

Likewise, the currently stored source, old acquisition work, the
retained later row, code representation, local parsing, controller
workspace, cached replies, address production and output all have
their stated separate roles. Unrolling or simulating a decision tree
can change state count and memory usage. The precise internal-memory
distinctions in [NARC §§17--30][NARC] are not transported by
(NTL.18)--(NTL.19). In particular a $q$-label *source summary* does
not mean a $q$-state whole service.

The relation established here connects an early memory label, a later
boundary row, literal positions and a discrete substitution lag on
one explicit source family. It supplies a mutual-recovery theorem for
the task quotient under those conditions. It neither identifies
physical spacetime with these trees nor supplies a universal cheap
computation model or a completion of a minimal-relations programme.

## 8. Mathematical suppliers and the uncovered interface

**Definition 8.1 (native supplier correspondence).** The following
sources supply the indicated mathematical ingredients, with their own
hypotheses retained.

| Supplier | Ingredient used here | Scope not transferred |
| --- | --- | --- |
| [NAR §§16.1--16.10][NAR] | Full independent age cube, acquired clocks, full-row equality, common-translation obstruction, minimum $q$, feasible-encoder decoder and unbounded-address criterion | No prescribed Boolean-task fiber or sourcewise coordinate-cost equality is supplied by those endpoints alone |
| [NARC §§1--3][NARC] | Both fiber directions and all-address exclusion at a particular acquired two-slot input | Its fixed-reference interval task is not the arbitrary function $f$ here |
| [AA, Propositions 12.5--12.6][AA] | An earlier actual ordered-tree presentation of a finite query task, all-address adaptive simulations, and the distinction between a coarse retained field and installation of a complete same-source service | Its installed constant-composition trees and passive-cut task do not give an early NAR16.1 encoder or forgotten-lag fiber; its installation obstruction cannot be bypassed by a mathematical presentation |
| [SLH §§6.2--6.3][SLH] | Guarded all-word constructor replies, including absence, and elimination of redundant stationary reads | Certified-epoch arbitrary-source tasks there do not supply an unknown age or lag here |
| [AOF §§3--5, 8--9][AOF], [JRF §2.1][JRF] | Same-source simulation, shortest literal representatives, simultaneous upper-budget reasoning and adjacent-age price | No stronger native query, arbitrary weights, free navigation or workspace equivalence |
| [CG, Proposition 14.12][CG]; [WPE §392 and Proposition 396.9][WPE] | Exact common laws, corrected parity normalization, adaptive same-sample transcripts and the full-coordinate parity certificate | No general inference about information from marginal laws alone |

The native formal-source interfaces are `Source` and `substitution` in
[GenealogicalFiberTransport][GFT]; `Address`, `Reply` and `readout` in
[ActualTreeReadoutAcquisition][ATRA]; `rightClock`, `rights`,
`right_clock_iterate` and `right_clock_readout` in
[DelayedOriginalReadout][DOR]; and `literalRecord`, `actualPartition`
and `canonicalRow_record_iff` in [ActualCutPartitionDecoder][ACPD].
The last interface represents both equality and disequality of reached
holes. The certified-epoch `original_decoder_service` is not an oracle
for the forgotten lag. These are definitions and suppliers for the
mathematical correspondence, not a claim that this companion's
applications have been compiled or certified.

**Definition 8.2 (primary-literature correspondence and limits).**
Cicalese--Laber--Saettler, [*Decision Trees for Function Evaluation:
Simultaneous Optimization of Worst and Expected Cost*,
arXiv:1309.2796v2, §§1--2][CLS], gives the discrete function evaluation
problem with objects, target classes, a complete test family, positive
test costs and a prior. Here objects are $\{0,1\}^m$, nonempty target
classes are the fibers of $f$, tests are individual coordinates, and
the positive test prices are $d_i$. Their worst/expected scalar-cost
approximation results are not the three-coordinate equality proved
here, and are not invoked to claim an efficient exact frontier.

Deshpande--Hellerstein--Kletenik, [*Approximation Algorithms for
Stochastic Boolean Function Evaluation and Stochastic Submodular Set
Cover*, arXiv:1303.0726v2, §§1--2][DHK], explicitly gives a product
distribution on input bits, a cost per bit test, adaptive sequential
testing and an expected-cost objective. Proposition 3.3 supplies a
uniform product law on the *selected input coordinates*, so its
Boolean-target case has that probabilistic test interpretation.
The surrounding initial ages and selected lag do not become independent
after conditioning. Their approximation theorems and time guarantees
are not used for native acquisition, encoding or address generation.

Charpenay--Le Treust--Roumy, [*Optimal Zero-Error Coding for Computing
under Pairwise Shared Side Information*, arXiv:2211.03649v2,
Definitions II.1, III.1--III.3 and Theorem III.4][CLR], defines
characteristic conflicts by different target values at common
compatible side information, and uses proper colorings. That is the
mature separation principle behind an early summary. Their i.i.d.
block coding, expected prefix lengths and asymptotic rates are not
the one-export, attained-alphabet objective on (NTL.2); their side
information does not supply the literal current-port service.

These decision-tree, coding and parity ingredients are
`literature-attested` or already supplied by the cited repository
results. The `repo-derived` addition is their conjunction through a
specific native interface: a globally minimum early encoder whose
zero-label set selects exactly the desired Boolean histories, a
proof using the full acquired row in both directions, and all-word
sourcewise cost transport with the geometry (NTL.15). The comparison
does not assert worldwide originality. The relationship between the
task quotient and its source, the paid preparation assumptions, and
the all-entry address obstruction remain part of the theorem's scope.

[NAR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[NARC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md
[AA]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[AOF]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[CG]: RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md
[WPE]: RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md
[GFT]: ../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[ATRA]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[DOR]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[ACPD]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[CLS]: https://arxiv.org/html/1309.2796v2
[DHK]: https://arxiv.org/html/1303.0726v2
[CLR]: https://arxiv.org/html/2211.03649v2

## 追加锚（本行以下为增补区）

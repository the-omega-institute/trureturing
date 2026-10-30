# Recursive Relational Observation: Polynomial Acquisition of the Original Source Prefix and Cut

## 1. Source, service, indices and the acquisition target

**Definition 1.1 (the original entrance).** Fix an integer $d\ge0$.
Use the actual source of [GPO, Definition 27.1][GPO] and the complete
entrance of [ACR, Definition 9.1][ACR]. The initial root is alpha at cut
zero. Physical links persist, have names $a<b$, and keep that order.
Each update changes each old alpha leaf to beta and replaces each old
beta leaf by one alpha child and one beta child. Newborn leaves are not
updated again in that update. The old beta parents are processed in
physical lexicographic order. At the $j$th birth since initialization,
the actuator consumes $z_j$, putting beta at $a$ exactly when $z_j=1$.
The autonomous generator advances once per birth and receives no other
input. Reads and local calculations neither update the source nor advance
its generator.

Write $s_i=z_{i+1}$ for $i\ge0$. The authentic public promise is precisely
$s\in\mathscr R_d$: there is a monic polynomial of degree at most $d$
annihilating $s$ under forward shift $E$ at every nonnegative index.
Equivalently, some $0\le u\le d$ and binary coefficients satisfy

$$
s_{i+u}=\sum_{j<u}c_j s_{i+j}\qquad(i\ge0).
$$

Order zero means the zero sequence. Coefficients may vanish, the original
presentation may be nonminimal, and the transition may be singular. No
bound on the least positive period is imposed. This is not an eventual
recurrence promise with an unbounded onset.

Put $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$ and $B_t=F_{t+1}-1$. The unknown
completed cut $n$ is any finite integer at least

$$
n_0=\begin{cases}
\min\{t\ge3:F_t-1\ge2d\},&d>0,\\
2,&d=0.
\end{cases}
$$

The only numerical source input is $d$. Accessible law, seed, age,
phase, support, labels, chronological records, archives and age-bearing
allocation or duration information are erased. The actual source and
its authentic surviving root binding remain. A total paid presence
service accepts any fully materialized finite physical word $w$ at that
root and returns $\operatorname{Read}(w)=\mathbf1_{w\in S_n}$. There is
no relative-root call, label, rank, clock, law, period, equivalence or
chronology reply. No reset, clone or physical recutting operation is
used.

The service premises include genuine binding, grants, reliable completed
Reads, common finite source-blind instructions, finite local progress,
and sufficient growing owned readable backing. A completed-cut stationary
interval covers the realized acquisition, calculations, allocations and
intermediate and retained writes. If acquisition is composed with
installation, the interval and backing must additionally cover the entire
normalization and completed handoff of ACR Theorems 26.1 and 29.2.
These premises do not follow from a transcript or from an operation count.

**Definition 1.2 (indices, mathematical coordinates and paid data).**
The requested acquisition output is exactly

$$
(P,n),\qquad P=z_1\cdots z_{2d};
$$

$P$ is empty at $d=0$. It includes the original transient. A descriptor
of a shifted core, a necklace representative or an equivalent local tree
is not this output.

For a physical node $p$ let $(b_p,\sigma_p)$ denote its immutable creation
cut and initial label, and put

$$
\tau_p=b_p+2-\mathbf1_{\sigma_p=\beta},\qquad
q_p=n-b_p+\mathbf1_{\sigma_p=\beta}.
$$

The root has $(b_\varepsilon,\sigma_\varepsilon)=(0,\alpha)$ and rank
$n$. Ranks zero and one have singleton support. At rank $q\ge2$ the
child ranks are $q-1,q-2$, with the larger child at $a$ exactly for bit
one. At cut $e_p=\tau_p-1$ the cone is one beta leaf; its normalized
current cut is $T=n-e_p=q_p-1$. This is a mathematical coordinate
change on the same physical cone, not a change of source or observer
root. None of these coordinates is initially supplied.

The actual least monic annihilator factors as $E^a g(E)$ with $g(0)=1$,
$a+\deg g\le d$. Its unique coprime decomposition is $s=y+t$, where
$g(E)y=0$ and $E^at=0$. In particular $t_i=0$ for $i\ge a$, and
$z_j=y_{j-1}$ for $j>d$. The sequence $y$ retains the original
index-zero alignment. The invertible companion transition on its finite
binary state space makes $y$ periodic. These are mathematical properties
of the authentic promise, as in ACR Theorem 27.3; neither $a,g,y$ nor a
period is an entrance register. For zero use $g=1$ and degree zero.

A mathematical support denotes the whole finite prefix-closed set. An
acquired support below $v$ means that a finite paid root-literal scan has
actually reached every member and paid the terminal absence tests.
Subsequent ranks, normalized cuts and batches are calculated from that
acquired finite record. Merely naming a mathematical cone earns none of
its support.

**Definition 1.3 (resource coordinates).** Let

$$
h=\max\{k\ge1:a^k\in S_n\},\qquad H=2h+1,\qquad S=d+H+2.
$$

The procedure of ACR Proposition 9.2 earns $h$ by paid doubling and
bisection. It makes $2\lceil\log_2(h+1)\rceil$ Reads, has maximum
literal length at most $2h<H$, and proves $h+1\le n\le H$. Thus $H$
is earned, rather than a supplied upper cut or a bound inferred from
allocated space.

Count $Q$ source Reads, $M$ maximum full root-literal length, $J$ the sum
of those lengths, $C$ sequential local bit work including head motion,
$W$ every cumulative local bit write, and $V$ peak owned visited backing.
$W$ includes scratch initialization, overwritten counters and operands,
unsuccessful trials and retained output copies. Binary integers and
addresses are represented strings, not unit-cost unbounded registers.
The acquisition uses zero source updates and no coins. Physical weighted
tariffs, service durations, binding, grants, code supply, allocation,
retention and completed installation have their original separate bills.

## 2. Earning a bounded core-only cone

**Theorem 2.1 (the terminal-spine selection dichotomy).** For $d\ge1$
define, from $d$ alone,

$$
\ell=\min\{j\ge0:F_{j+2}>d\},\qquad
s_*=\min\{j\ge1:F_j\ge2d\},\qquad L=s_*+3.
$$

After earning $h$, exactly one of the following procedures applies.

1. If $h<\ell+L$, a complete paid scan at the original root has
   $O((d+1)^4)$ present nodes and directly acquires $(P,n)$.
2. If $h\ge\ell+L$, the present physical address
   $v=a^{h-L}$ has depth at least $\ell$. Its actual rank $q$ and
   normalized cut $T=q-1$ satisfy

$$
L+1\le q\le2L+1,\qquad L\le T\le2L.
$$

   A complete paid scan of this existing cone has $O((d+1)^2)$ present
   nodes. It acquires $T$ and the first $2d$ bits of each of its actual
   chronological batches $W_{s_*},W_{s_*+1},W_{s_*+2}$. Every birth in
   the cone uses the original aligned core $y$.

Both scans use only complete root operands of length at most $H$; neither
needs a supplied rank, cut, support, transient length or clock seed.

**Proof.** The paid spine endpoint $a^h$ has no $a$ child. Full binarity
implies that it is terminal, of rank zero or one. In the second case its
$L$ ancestors along the suffix lie below $v$. Along these edges rank drops
by one or two. If the endpoint rank is one, the initial rank is at least
$L+1$. If it is zero, the last edge must have dropped two, since a rank-one
node cannot branch; again the initial rank is at least $L+1$. In both
cases the initial rank is at most $2L+1$. This proves the displayed
bounds without observing a rank. In particular the cone is nonterminal.

Induction on rank gives a rank-$q$ cone $F_{q+1}$ terminal leaves and
$2F_{q+1}-1$ present nodes. The base ranks zero and one each have one
leaf. At rank at least two the two child counts add by the Fibonacci
recurrence. Its maximum suffix depth is $q-1$ for $q\ge1$ and zero at
rank zero. Thus the selected cone has exactly

$$
N_v=2F_{T+2}-1\le2F_{2L+2}-1.
$$

Start with $v$, whose presence follows from the acquired spine (or pay
one additional confirmation). At every confirmed node $vw$, pay both
$\operatorname{Read}(vwa)$ and $\operatorname{Read}(vwb)$. Schedule the
two positive children, or close the node after both negatives. The actual
source has no one-child case. Prefix closure and induction prove that
this finite scan acquires the entire cone, including its terminal
absences, with at most $2N_v+1$ Reads. It never treats an unqueried
fringe as absent. Since each ancestor edge decreases rank at least one,
$q\le n-|v|$. Each positive word and each terminal child test therefore
has length at most $|v|+q\le n\le H$. All submissions remain at the
original root, even though their suffixes are processed locally.

For the polynomial size estimate, minimality of $s_*$ gives
$F_{s_*-1}<2d$ and $F_{s_*}<4d$ (also at $d=1$). Adding any fixed
number of Fibonacci indices changes these bounds by an absolute factor.
The addition identity then gives $F_{2s_*+c}=O((d+1)^2)$ for each fixed
$c$. Hence $N_v=O((d+1)^2)$. Minimality of $\ell$ similarly gives
$F_{\ell+1}\le d$, $F_{\ell+2}\le2d$, and
$F_{2\ell+c}=O((d+1)^2)$. If the first case applies, then
$n\le2h+1\le2(\ell+L)-1$, so the root has at most

$$
2F_{2(\ell+L)}-1=O((d+1)^4)
$$

nodes. This proves the first scan bound, including all small $d$.

The depth of $v$ in the second case is $h-L\ge\ell$. Every branch at
physical depth $m$ occurs at update at least $m+2$, and its first
possible global birth index is at least $F_{m+2}$, by GPO Proposition
39.2. Consequently every birth in this cone has index greater than $d$.
The coprime decomposition in Definition 1.2 therefore makes it genuinely
core-only, including for singular original laws. Apparent periodicity
of observed words is not used to certify this condition.

The acquired cone's leaf count is $F_{T+2}$. These numbers are strictly
increasing for $T\ge0$, so counting the acquired leaves determines $T$.
A branch descendant of rank $r\ge2$ has height $r-1$ and normalized
birth update $k=T+2-r$. For $r\ge3$ its two child heights are $r-2,r-3$;
the larger child's physical position reveals its orientation. At $r=2$
both children are terminal, and its orientation is invisible. Therefore
the acquired support determines the orientations and updates of all
parents in batches $1\le k\le T-1$, without inferring the last batch.
Sort those parents by update and actual physical address. Equivalently,
start with a beta roster at normalized zero and update only old leaves;
the decoded orientations reproduce the actual roster inductively. In
update $k$ it contains $F_k$ beta parents. Their global addresses form
one consecutive interval of the actuator's actual ordered beta list,
so the decoded word is exactly $W_k$, not an independently sorted
semantic word. This re-establishes the needed implication of PCR
Theorem 2.1 and NRW Lemmas 1.4 and 2.1--2.3 on the acquired input.
Since $T\ge s_*+3$, all three stated batches lie at most $T-1$ and
have length at least $F_{s_*}\ge2d$.

For the small-root case, its leaf count $F_{n+1}$ determines $n\ge2$.
A branch of rank $r\ge3$ has actual birth update $n+2-r$ and observable
orientation by the same height argument. Sorting by update and physical
address recovers the first $B_{n-1}=F_n-1$ original births, precisely
GPO Theorem 28.2's correspondence. Maturity makes this at least $2d$.
The first $2d$ entries are the requested $P$, including its transient;
no assumption about the core is needed in this branch. $\square$

**Theorem 2.2 (the exact three-batch index relation).** In the second
case of Theorem 2.1, let $I_k$ be the one-based first global birth index
of $W_k$. These are mathematical indices, not acquired replies. Then

$$
I_{k+2}=I_{k+1}+I_k\quad(k\ge1),\qquad
W_k(i)=y_{I_k-1+i}\quad(0\le i<F_k).
$$

Thus, for $A=I_{s_*}-1$ and $B=I_{s_*+1}-1$, the three paid prefixes
are the first $2d$ entries of

$$
u=E^Ay,\qquad v'=E^By,\qquad w=E^{A+B+1}y.
$$

The exponent $A+B+1$, rather than $A+B$, retains the original one-based
birth alignment.

**Proof.** Put $e=\tau_v-1$. The preceding exterior forest consists of
the physical $a$ siblings skipped when the root-to-$v$ path takes a
$b$ edge. Those sibling cones are prefix-incomparable and all exist at
cut $e$. Write $D(t)$ for their number of beta leaves at cut $t\ge e$.
For any old-leaf forest its alpha/beta counts change as
$(C,D)\mapsto(D,C+D)$, independently of orientations. Thus
$D(t+2)=D(t+1)+D(t)$. Before actual update $e+k$ there have been
$B_{e+k-1}=F_{e+k}-1$ births, and exactly $D(e+k-1)$ beta parents
precede the cone. It follows that

$$
I_k=F_{e+k}+D(e+k-1).
$$

Both summands obey the integer Fibonacci recurrence. Within the cone
the actuator consumes consecutive bits in the actual physical order;
Theorem 2.1 decoded exactly that order. Its core-only condition gives
the second assertion. Subtracting one from the three starting indices
gives $I_{s_*+2}-1=A+B+1$. This is the actual exterior-clock identity
of ACR Theorem 27.2, justified on this same cone. No numerical value of
$e,D,A,B$ is required by the inverse below. $\square$

## 3. Recovering the original alignment without a deep clock search

**Theorem 3.1 (the acquired three-batch Hankel inverse).** The three
paid prefixes in Theorem 2.2 determine an explicit least recurrence
and original aligned seed for $y$ with polynomial local work and writes
in $d$. In particular they do not require a period word, a phase
exponent, a factorization or a search over the deep cone's integer
clocks. All divisions below are over $\mathbb F_2$ or by proved units.

**Proof.** The recurrence algebra used here is classical. In Shoup,
*A Computational Introduction to Number Theory and Algebra*, second
edition, Theorem 18.1 and Exercises 18.2--18.5 give the forward-shift
annihilator ideal, minimal Hankel system and polynomial-module action;
§18.2 gives synthesis from $2d$ acquired entries. Massey's
*Shift-Register Synthesis and BCH Decoding*, §§II--IV, Theorems 3 and
4 and their corollaries, gives the corresponding finite synthesis and
rational-series description. The argument below supplies the specific
parameter correspondence and source-alignment cancellation; it does
not claim a new generic recurrence theorem.

Every shift of the periodic $y$ has the same least monic annihilator
$g$, of degree $r_0\le d$ and constant coefficient one when $r_0>0$.
Indeed, shifts preserve annihilators, and shift is injective on
periodic streams, giving the reverse inclusion of their annihilator
ideals. Form, entirely from acquired entries,

$$
H_d(w)=(w_{i+j})_{0\le i,j<d},\qquad r=\operatorname{rank}H_d(w).
$$

To justify that the computed rank is the least degree, an order-$r_0$
recurrence bounds the rank above by $r_0$. If the leading $r_0$ by $r_0$
block had a nonzero column relation, the resulting nonzero polynomial
$f$ of degree less than $r_0$ would make $f(E)w$ zero at its first $r_0$
positions. It satisfies the same order-$r_0$ recurrence, so forward
induction makes it zero everywhere, contradicting minimality. This
proves $r=r_0$, exactly the intermediate Hankel argument in
ACR Theorem 21.2 and Shoup Exercise 18.3. It does not assume that the
observer already knew $r$.

At computed rank zero the core is zero. For example, the first $d$
zero entries of $w$ and an actual recurrence of degree at most $d$
force all of $w$ to be zero by forward induction; periodic shift then
forces $y=0$. Return the zero descriptor and perform no inversion.

Otherwise set $K=H_r(w)$, which is nonsingular by the preceding
argument. Compute binary vectors $b,c$ from

$$
K b=(w_r,\ldots,w_{2r-1})^{\mathsf T},\qquad
K c=(v'_1,\ldots,v'_r)^{\mathsf T}.
$$

The first solution gives the actual least polynomial

$$
g(X)=X^r+\sum_{j<r}b_jX^j.
$$

Its actual recurrence is one solution, hence the unique solution. The
second gives $f(X)=\sum_{j<r}c_jX^j$ with $f(E)w=Ev'$ at the first
$r$ positions. Both sides satisfy $g$, so this equality holds at every
nonnegative position. By Theorem 2.2,

$$
w=E^{B+1}u,\qquad Ev'=E^{B+1}y.
$$

Hence $E^{B+1}(f(E)u-y)=0$. The difference lies in $\ker g(E)$, where
shift is injective: the constant coefficient $g(0)=1$ makes any value
recoverable from its next $r$ values. Applying that fact $B+1$ times
is a proof of injectivity, not an algorithm iterating an unknown or
large $B$. It follows that

$$
f(E)u=y.
$$

Return $g$ and the seed

$$
y_i=\sum_{j<r}c_j u_{i+j}\qquad(0\le i<r).
$$

All operands occur in the paid prefixes: the largest index used is
$2r-1\le2d-1$. Exact binary rank and the two solves take polynomially
many field operations and $O((d+1)^2)$ data bits; sequential scanning
only adds polynomial work and writes. The algorithm computes no $A,B$
and never repeats $B$ backward steps.

For the conventions, this $g$ is the monic forward-shift polynomial.
Massey's connection polynomial is $C(D)=D^rg(D^{-1})$; conversely
$g(X)=X^rC(X^{-1})$. For the purely periodic core $C$ has degree $r$.
The singular factor $E^a$ belongs to the original all-index stream and
is never inverted. In an ordinary power series the denominator is
$C$, whereas in the reversed Laurent series
$\sum_{i\ge0}y_iX^{-i-1}$ the reduced denominator is $g$, as in Shoup
Theorem 18.2. These reciprocal conventions are not interchangeable.
The zero core has degree zero and the all-one core has $g=X+1$; the
latter gives $K=(1)$ and $f=1$. Repeated factors of $g$ have not been
removed or assumed absent. $\square$

**Proposition 3.2 (quotient-ring correspondence and nonminimal padding).**
For a nonzero core the preceding inverse is also expressed in
$R=\mathbb F_2[X]/(g)$ by

$$
N_y=XN_uN_{v'}N_w^{-1}\pmod g,
$$

where $\sum_{i\ge0}x_iX^{-i-1}=N_x/g$, $\deg N_x<r$, for
$x=y,u,v',w$. The inverse is justified even for reducible repeated-factor
$g$. Replacing $g$ by a nonminimal annihilator need not permit this
cancellation.

**Proof.** Shoup Theorem 18.2 identifies the reduced reversed-Laurent
denominator with the least forward annihilator. Each numerator is
coprime to $g$, since a common factor would cancel to a smaller
annihilator. Thus each $N_x$ is a unit modulo $g$, by Shoup Theorem
16.18. Also $X$ is a unit because $g(0)=1$. The identity
$L_{Ex}=XL_x-x_0$ implies $N_{Ex}=XN_x\pmod g$. Therefore

$$
N_u=X^AN_y,\quad N_{v'}=X^BN_y,\quad N_w=X^{A+B+1}N_y,
$$

which proves the formula after cancellation of the proved unit $N_w$.
No quotient field is assumed. Its degree-less-than-$r$ representative
is exactly the original numerator, not a phase class. For the all-one
stream, the nonminimal choice $g'=(X+1)^2=X^2+1$ instead has numerator
$X+1$, a nonunit modulo $g'$. Theorem 3.1 computes rank one and uses
$g=X+1$, so this failure excludes no original source. The quotient
identity is an alternative correspondence, not an additional input
requirement of the Hankel procedure. $\square$

## 4. From the acquired core to the actual early bits and cut

**Definition 4.1 (a singleton-core exact-height procedure).** In the deep
branch retain the aligned descriptor produced by Theorem 3.1; for $d=0$
use the known zero descriptor. Put

$$
h_0=\begin{cases}n_0-2,&d>0,\\0,&d=0.\end{cases}
$$

Use ACR Definition 28.1's height procedure, with the following exact
change: replace the core-presentation loop and its stages by this single
earned aligned descriptor. Keep both integer-clock loops, all rank
trials, termination tests, root-literal guards and the rank certificate.
For clarity these ingredients are specified here.

A present start $x$ of depth at most $h_0$ is presence-tested. Explore at
most $\ell$ further physical levels ($\ell=0$ at $d=0$), paying both
child-presence tests at each visited node and stopping at terminals.
At a nonterminal frontier $p$, of depth $m$, enumerate both integers

$$
1\le A_1,A_2<F_{2m+4},\qquad 2\le q\le H-m.
$$

The integers are hypotheses, never replies. Extend the first two by
the integer Fibonacci recurrence $I(k+2)=I(k+1)+I(k)$. Give the local
root descriptor $(0,\beta)$. For a relative branch $w$ with local
branch update $k$, its hypothesized global birth index is

$$
J(w)=I(k)+\sum_{ub\preceq w}
 \lambda_{\sigma_{ua}}(k-1-\theta_u),\qquad
\lambda_\alpha(t)=F_t,\quad\lambda_\beta(t)=F_{t+1}.
$$

Here $\theta_u$ is the already computed local branch update and
$\sigma_{ua}$ the immutable initial label of that skipped sibling.
This is ACR (ACR.115), with all proper-ancestor ages nonnegative.
The descriptor evaluates $y_{J(w)-1}$ to assign the two physical
child labels. Only paths are generated, not the whole trial tree.
At proposed rank $q$, form a longest suffix $x_q$ of length $q-1$
by choosing the rank-one decrement, with a fixed tie rule at rank two.
For $q=2k+1$ form a short suffix $y_q$ of length $k$ by rank-two
decrements. For $q=2k$ its length is $k-1$. Pay the following actual
root-literal tests:

$$
\operatorname{Read}(px_q)=1,\qquad
\begin{cases}
\operatorname{Read}(py_qa)=0,&q=2k+1,\\
\operatorname{Read}(py_qaa)=\operatorname{Read}(py_qba)=0,&q=2k.
\end{cases}
$$

Reject malformed lengths or a literal exceeding $H$. On the first
passing trial return height $q-1$; otherwise return zero. Recombine
explored branches by one plus the maximum child height. Hypothetical
clock pairs need not have a global realization. No fixed-seed shortcut
and no numerical deep-cone clock is used.

**Theorem 4.2 (all required heights are exact).** On every source in
Definition 1.1 the singleton-core procedure completes and returns the
actual height for every required present start of depth at most $h_0$.
It obtains the original $(P,n)$ by the early-parent procedure of ACR
Definitions 28.3 and 22.1, including arbitrary permitted transients.

**Proof.** ACR Theorem 27.3's depth cutoff, proved by the same
$j\ge F_{m+2}>d$ argument in Theorem 2.1, makes every surviving
frontier genuinely core-only. It exposes at most $2^{\ell+1}-1$
nodes per height call. ACR Theorem 27.2 includes the true two integer
clock seeds among the enumerated seeds and proves that the local-index
formula reproduces the actual cone. Its bound applies because these
frontiers have depth

$$
m\le h_0+\ell\le4\lceil\log_2(2d+2)\rceil,\qquad
F_{2m+4}=O((d+1)^8).
$$

The proof of that seed bound uses the actual branch-time inequality
$m+2\le\tau_p\le2m+2$; the first two local batches occur by update
$2m+3$, so their starts are at most $B_{2m+3}<F_{2m+4}$. This bound
is used only at these shallow frontiers. The cone acquired in Theorem
2.1 can have depth proportional to $H$; its clock seeds are not searched.

At the actual seed pair and rank $q$, the paths in Definition 4.1 are
actual longest and shortest paths. They pass the paid tests. An earlier
passing trial is equally sound: a present suffix of length $q-1$ forces
actual rank at least $q$. At an actual rank at least $q+1$, the required
short-word absences are impossible. In the odd case every word of length
$k+1$ would be present; in the even case the length-$(k-1)$ prefix has
rank at least three, so one of its two children branches and one of the
two tested grandchildren is present. This is the full soundness argument
of ACR Theorem 22.2, with its parity-dependent length constraint intact.
A failed trial supplies no bit value or first-disagreement location.
Terminal ranks zero and one both have height zero and need not be
separated. Exact frontier values recombine to the exact start height.
All tests fit the guard because $m+q\le H$.

Obtain $n=1+\operatorname{height}(\varepsilon)$. For birth
$j=1,\ldots,2d$, calculate

$$
\tau(j)=\min\{t\ge2:j\le B_t\}.
$$

Using already recovered bits from earlier updates, construct the old
labelled tree at $\tau(j)-1$, containing at most $2j-1$ nodes. Its
$(j-B_{\tau(j)-1})$th beta leaf in physical order is the actual
parent $p_j$, by induction and GPO Proposition 39.2. Bits earlier in
the same batch do not alter that old tree. Maturity implies
$\tau(j)\le n-1$ and $|p_jc|\le\tau(j)-1\le h_0$ for each child
$c$. Both children are present. Their ranks are $t_j+1,t_j$ with
$t_j=n-\tau(j)\ge1$; their exact heights are $t_j,t_j-1$. The larger
height is at $a$ exactly when $z_j=1$. Thus two exact-height calls
recover the authentic next bit and continue the induction. This uses
actual shallow-source replies beyond the acquired mature core. It does
not replace early bits by core bits or infer $n$ from a local age.

As in ACR Definition 28.3, solve the order-$d$ Hankel system for the
now authentic $P$, select any deterministic Gaussian solution as an
auxiliary verification descriptor, and run ACR Corollary 22.3's final
paid proper-candidate verifier. A solution exists by the all-index
promise. GPO Lemma 29.2's monic product-annihilator argument makes its
infinite behavior equal to the source. The final verifier therefore
passes; its row is not asserted to be $K_d(P)$. Keeping this verifier
also keeps its literal guards and at most $2d+3$ paid tests. At $d=0$
the early-bit loop and prefix are empty; the known zero descriptor still
constructs the paid root rank witnesses for every $n\ge2$, including
$n=2$. No cut is provided by the order-zero promise. $\square$

**Proposition 4.3 (the matched-source pair remains distinguished).**
With public $d=2$, source A $z=111\cdots$ at cut $11$ and source B
$z=0111\cdots$ at cut $12$ both have $h=10$. Their cones at $aa$
have identical complete presence support, rank nine, normalized cut
eight and 109 nodes, but their authentic outputs are respectively
$(1111,11)$ and $(0111,12)$. Both belong to the original comparison
domain. The complete protocol above distinguishes them.

**Proof.** Source A has order one. Source B has the singular order-two
presentation $s_{i+2}=s_{i+1}$ with seed $01$. Both have the aligned
all-one core. After the root birth all later bits are one. In A the
$a$ child has rank ten; in B it also has rank ten, since it was the
root's initial alpha child at the later cut. Their $a$-spines therefore
have total height ten. The $aa$ child has rank nine in both, and every
later orientation in it is one. This proves identical local support;
its node count is $2F_{10}-1=109$. For this $d$, $\ell=2$, $s_*=5$
and $L=8$, so Theorem 2.1 actually selects this same $aa$ cone in
both sources. Its acquired data and the recovered core alone cannot
separate the requested outputs.

At the root their child heights are respectively $(9,8)$ and $(9,10)$.
Theorem 4.2's subsequent root and early-child calls acquire the
corresponding heights and recover the distinct cuts and first bits.
For a direct paid separator, $ba^9$ is absent in A and present in B:
the $b$ ranks are respectively nine and eleven and all subsequent
orientations are one. No restriction of the comparison domain is
involved. Likewise, in $\mathscr R_1$ at cut four, $000\cdots$ and
$1000\cdots$ share the zero core but have prefixes $00$ and $10$;
$\operatorname{Read}(bba)$ is respectively one and zero. The transient
must be recovered by the global consumer. $\square$

## 5. Every-execution accounting and the full original domain

**Theorem 5.1 (polynomial paid acquisition).** Under exactly Definition
1.1, one deterministic source-blind procedure returns and retains the
authentic $(P,n)$ on every admitted execution, for every $d\ge0$ and
every mature finite cut. For an absolute constant $C_0$ it admits the
conservative bounds

$$
\begin{aligned}
Q_{\rm acq}&\le C_0(d+1)^{19}(H+1),&
M_{\rm acq}&\le H,&J_{\rm acq}&\le H Q_{\rm acq},\\
C_{\rm acq},W_{\rm acq}&\le C_0S^{60},&
V_{\rm acq}&\le C_0S^8,&U_{\rm source}&=0.
\end{aligned}
$$

All preparation and unsuccessful trials are included. The bounds hold
for zero and constant cores, repeated factors, nonminimal and singular
presentations, all permitted transients and exponential least periods.
They are polynomial in $d$ and the actually earned $H$, not asserted
polynomial in $\log n$.

**Proof.** Earn $h$. At positive $d$ use Theorem 2.1. In its small-root
branch the complete scan and the finite ordered-prefix decoder already
return the requested output. In its deep branch use Theorems 2.2, 3.1
and 4.2. At $d=0$ go directly to the single zero-core height procedure.
Every search is finitely bounded in terms of earned integers. The
inclusion and soundness proofs above show termination with exactly the
claimed output, not a conditional inverse with unearned inputs.

There are at most $4d+1$ height calls: one at the root and two per
original birth. Each has $O((d+1)^2)$ shallow nodes and frontiers.
Each frontier tries at most $O((d+1)^{16})$ clock pairs and $H$ ranks,
with at most three paid certificate Reads per trial. Presence and
termination tests, the $O((d+1)^4)$ small-root scan or the
$O((d+1)^2)$ deep scan, the paid spine and the final verifier are
absorbed in the displayed $Q$ bound. The original core catalogue and
all its stages are absent: the count is recomputed with one earned
core, not obtained by calling the exponential bound polynomial.
No period enumeration, phase search or deep clock enumeration replaces
that catalogue. Every complete source operand obeys $H$, proving $M,J$.

For bit accounting, an arbitrary shallow trial has seeds below
$F_{2m+4}$ with $m=O(\log(d+2))$. Up to normalized update $k\le H$,
its clock values are at most $F_{k+1}\max(A_1,A_2)$. There are at most
$H$ sibling masses in an index sum. Every resulting index has
$O(H+\log(d+2))=O(S)$ bits. Thus exponential numerical indices are
represented with polynomially many bits, and every addition, comparison
and counter change is paid. Term evaluation from the supplied core
uses ordinary binary companion powering or monic polynomial reduction.
Bostan--Mori, §1.3, identifies this as powering in the quotient ring,
not a field assumption or an acquired random-access interface. Recomputing
powers at each edge is allowed and polynomial in $d$ and the represented
index length.

Here is one sequential layout realizing the conservative envelope.
During the prelude keep the acquired finite tree in delimited records
with explicit complete physical addresses, two child links, leaf counts,
heights and traversal markers. There are $O((d+1)^4)$ records even in
the larger branch, and each record has $O(S)$ bits including its address
and represented indices. The three prefixes and their rank/matrix
scratch have polynomial size. Decode by bottom-up finite scans and
sort parent records by update and physical address, using pairwise
comparisons if desired. There are at most quadratically many record
comparisons and at most $H$ scans to propagate heights; allowing even
$O(S^{12})$ indexed bit operations covers traversal, sorting, Fibonacci
comparisons, all matrix operations and output copies. No suffix-support
record is retained without paying its writes.

After keeping the core descriptor, discard the expanded cone records.
For the height consumer retain the shallow depth-first tree, at most
two early-parent old trees, a constant number of literal/path buffers,
immutable path descriptors, a Fibonacci and clock table, companion
scratch, the two trial seeds, rank counters, one certificate and the
output. This is the layout in ACR Theorem 29.1, now with one core and
one stage. Before sequential accesses it needs at most $O(S^6)$ indexed
bit operations per trial: at most $H$ path edges, at most $H$ index
summands at an edge and polynomial companion evaluation. The same bound
covers loop preparation and full literal construction per trial.
The final verifier constructs at most $O((d+1)(H+1))$ edges, each by
those same represented operations.

Both layouts and their marker/copy scratch fit $O(S^8)$ visited bits;
the expanded record estimate is already $O(S^5)$. Implement each
indexed bit access by an actual scan and return across this layout.
Allowing $O(S^2)$ work and writes per visited cell for counters and
markers gives $O(S^{10})$ work and writes per indexed access. There
are at most $O(S^{20})$ height trials, so their total is at most
$O(S^{36})$. The prelude and other stated polynomial operations also
fit $O(S^{60})$, with ample slack for parsing, finite comparisons,
initialization and the retained acquisition-output copy. Every such
write, including discarded hypotheses and overwritten buffers, is
counted in $W$; no transcript archive or unbounded table is retained.
These are explicit mathematical upper envelopes, not optimized or
measured running times. Finite completed service and local progress
make each admitted finite operation complete, without supplying a
uniform physical duration bound. $\square$

**Proposition 5.2 (domain and observation boundaries).** None of the
following substitutions is part of Theorem 5.1: replacing the original
stream by its core, treating a final invisible batch as directly read,
fixing one clock seed, using a nonminimal Hankel block as nonsingular,
or replacing an acquired support by a finite menu without a completeness
proof. The theorem needs no restriction excluding any such source.

**Proof.** The small-root branch decodes only births through $n-1$;
the deep branch decodes only normalized batches through $T-1$.
A final rank-two cherry has identical support for its two orientations,
so no final orientation is used as a presence observation. The alignment
inverse uses the actual $+1$ identity in Theorem 2.2; deleting it
would replace $y$ by $Ey$ in the Hankel cancellation, which differs
for any nonconstant periodic core. Proposition 3.2 shows why nonminimal
padding cannot be inverted indiscriminately. Proposition 4.3 shows why
an aligned core alone cannot replace the original output. The selector
pays the complete scan and every negative terminal test, resolving the
finite-menu distinction of PCR Proposition 2.2.

Both shallow seeds are enumerated. ACR Proposition 28.5 gives actual
sources in $\mathscr R_5$ at the same depth-three address $aba$ with
clock pairs $(9,14)$ and $(9,15)$, while their first seed and local
normalization cut agree. Its argument only establishes the failure
of that exact-clock shortcut; it is not an acquisition lower bound.
Here neither coordinate is discarded. Exponential-period sources in
NRW Theorem 2.4 remain admitted: the three finite windows and the
Hankel inverse do not materialize their period. Singular transients
are handled by the depth cutoff and the later original-parent induction,
never by reversing a noninvertible all-index transition. $\square$

## 6. Exact original normalization and the four recovery views

**Theorem 6.1 (acquisition is additive to original normalization and
installation).** After Theorem 5.1, the exact original installed tuple
remains

$$
(P,K_d(P),n,B_n),\qquad B_n=F_{n+1}-1,
$$

with the original first-passing convention

$$
K_d(P)=(\rho_d(i_P),P[0:d]),\qquad
i_P=\min\{i:H(P)\rho_d(i)=b(P)\}.
$$

Here $H(P)_{ij}=s_{i+j}$ and $b(P)_i=s_{i+d}$ are formed from the
acquired original prefix; $\rho_d$ is exactly ACR Definition 21.1's
fixed enumeration. The empty descriptor is retained at $d=0$.
The acquisition work/write bounds add to, and do not replace, the
original $C_{\rm norm}(P),W_{\rm norm}(P),V_{\rm norm}(P)$ and the
Fibonacci, physical-write, optional phase and handoff bills of ACR
Theorems 26.1 and 29.2.

**Proof.** Acquisition has produced authentic explicit $P,n$, so the
normalizer's input hypotheses now hold without a conditional sample
oracle. The auxiliary minimal core and the Gaussian verification row
are different typed data from the first passing original row. At full
rank $\operatorname{rank}H(P)=d$, the solution is unique, so Gaussian
elimination returns precisely that original row independently of
$\rho_d$. Equivalently, if the least all-index annihilator is $E^ag$
with $a+\deg g=d$, ACR Theorem 21.2 supplies this full rank. The
polynomial full-rank normalizer can therefore follow the new acquisition
on every such source, without a sparse-core or short-period condition.

At deficient rank the original first-passing normalization remains
separately charged, including $e_d,\omega_d,v_d$, transfers of tested
rows and all row-test writes in ACR (ACR.90). A minimal polynomial or
an arbitrary passing solution does not prove firstness under $\rho_d$.
ACR §§31--32 concerns an auxiliary enumeration and establishes neither
a hardness nor a polynomial selection theorem for this original one.
No new deficient-rank firstness theorem is supplied here.

The remaining binary Fibonacci arithmetic and installed payload/control
writes have their unchanged bills. Ready and completed handoff require
actual granted readable backing, completed field writes, bindings,
permissions and synchronization, as in ACR Theorem 29.2. A local
arithmetic count supplies no grant, uniform tariff, lease duration or
indefinite stationary interval. Only after that original canonical
installation do GPO Theorems 34.2--34.3 and 39.4 supply the same-source
spatial incidence, terminal boundary, actual birth chronology and
synchronized memory views and their finite continuation. Later updates,
Reads, local commits and requested outputs retain their actual charges;
whole-tree or whole-chronology output pays its full length. Recovery
of an arbitrary erased journal or private generator presentation is not
a consequence. Thus the acquisition obstacle is removed at ordinary
mathematical proof level, while original deficient-rank normalization,
physical completion and the broader economical four-view recovery
problem retain their separate unresolved obligations. $\square$

## 7. Supplier domains and mathematical provenance

**Definition 7.1 (supplier correspondence).** The load-bearing new
statements are repository-derived: the paid terminal-spine dichotomy,
its acquired three-batch alignment inverse, and the composition returning
the original $(P,n)$ with the counted resource envelope. Their
classical recurrence steps are literature-attested intermediate results,
not claims of worldwide originality. The corresponding suppliers have
the following exact domains.

| Supplier | Input and conclusion used here | Boundary retained |
| --- | --- | --- |
| ACR Proposition 9.2 | Paid fixed-port spine earns $h$ and $n\le2h+1$ | No law, cut or support is supplied by the entrance |
| GPO Definitions 27.1, 29.1 and Theorem 28.2 | Actual alpha source, all-index $\mathscr R_d$, complete-support ordered-prefix inverse | Complete mathematical support is not already acquired support |
| NRW Lemmas 1.4 and 2.1--2.3; PCR Theorem 2.1 | Rank-at-least-three orientations, beta-origin batches and invisible newest batch | Used on the actually scanned finite cone, with physical child order |
| ACR Theorems 27.2--27.3 | Actual integer-clock/index formula, two bounded shallow seeds, depth core cutoff | Deep clocks may be large and are never enumerated |
| ACR Theorem 21.2 | Leading minimal Hankel nonsingularity and rank equal to all-index least order | Classical algebra applied to paid periodic shifts; no free rank input |
| ACR Definitions 28.1, 28.3 and Theorems 28.2, 28.4 | Singleton-core height search, actual early-parent induction and final verifier | Genuine core and both clock seeds are included; no provisional height is promoted |
| ACR Theorem 22.2, Corollary 22.3; ACRC Theorems 33.2--33.3 | Actual parity-length rank witnesses and original-prefix authentication | Witness construction is paid; a negative trial is not a bit oracle |
| ACR Theorem 29.1 | Sequential path/trial layout and represented-index accounting | Trial count is recomputed without the catalogue; physical tariffs remain separate |
| ACR Theorems 26.1, 29.2; GPO Theorems 34.2--34.3, 39.4 | Original normalization, completed canonical handoff and same-source consumers | No completed installation follows from acquisition alone |

The recurrence references are [Massey][MAS], §§II--IV, Theorems 3--4
and their corollaries; [Shoup][SHO], second edition, §§16.4, 17.4,
18.1--18.2, Theorems 16.18, 18.1--18.2 and Exercises 18.2--18.6;
and [Bostan--Mori][BM], version 1, §§1.2--1.3. Massey supplies shortest
finite synthesis and its connection-polynomial convention. Shoup
supplies the forward annihilator ideal, minimal Hankel and reversed
Laurent conventions and proved-unit criterion. Bostan--Mori supplies
forward evaluation from an explicit recurrence and seed over a monic
quotient ring. None supplies paid physical samples, a root age, a
source conformance certificate or original $\rho_d$ firstness.

The formal declarations `NativeRankedNavigationCompiler.atomic_navigation`
and `rank_only_refinement_compilation` concern fixed native ranked
expressions, semantic orientation, four-valued replies and positive
whole-subtree equality links. `NativeBirthVectorDecoder.decodeBirth_patternVector`
is correct on recursive code-image vectors, without an acquired
presence-to-code bridge. `ActualFibonacciSupportChain.actual_fibonacci_support_chain`
concerns strict native support inclusions and bounded-address agreement.
`NativeFullSourceProducer.native_source_producer` acquires finite native
trees with alpha/beta/branch/absent replies. `FiniteCompanionCyclicModule`
uses its specific polynomial $P(u,q)$, rather than an arbitrary acquired
binary core. These Lean types and their corresponding Blueprint Scribe
domains supply no presence-only theorem claiming Theorem 5.1. The
mathematics here is ordinary proof; no new compiled or kernel-verified
claim is made.

[ACR]: RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md
[ACRC]: RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT_CONTINUATION.md
[GPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md
[NRW]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RESIDUAL_WIDTH.md
[PCR]: RECURSIVE_RELATIONAL_OBSERVATION_PERIODIC_CLOCK_RIGIDITY.md
[MAS]: https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI411.pdf
[SHO]: https://shoup.net/ntb/ntb-v2.pdf
[BM]: https://arxiv.org/html/2008.08822v1

## 追加锚（本行以下为增补区）
## 8. Cut-independent beta paths and paid height recovery

**Definition 8.1 (the earned input and finite clock family).** Retain
exactly Definition 1.1 and the resource coordinates of Definition 1.3.
For positive $d$, use Theorem 2.1 unchanged: its small-root branch
already returns $(P,n)$; in its deep branch Theorems 2.2 and 3.1 earn
an explicit recurrence and index-zero aligned seed for the authentic
core $y$. For $d=0$ use the promised zero core. No original transient
bit is replaced by a core bit.

For an exact-height call at a present start $x$ of depth at most $h_0$
from Definition 4.1, pay its presence and explore at most $\ell$ further
levels, paying both children at every visited node and stopping at
terminals. Use $\ell=0$ at $d=0$. At a surviving nonterminal frontier
$p$ of depth $m$, consider the entire rectangle

$$
\mathcal A_m=\{(A,B):1\le A,B<F_{2m+4}\},\qquad K=H-m.
\tag{PSA.8.1}
$$

This is a locally generated family of integer hypotheses, including
pairs with no global source realization. ACR Theorems 27.2--27.3,
with the hypotheses already checked in Theorem 4.2, give
$m\le h_0+\ell=O(\log(d+2))$, $|\mathcal A_m|=O((d+1)^{16})$,
and inclusion of the two actual first-batch indices. Every birth in
this frontier uses $y$ at its original global index. Neither integer
coordinate is supplied or observed. The acquired deep cone is used
only to earn $y$; its potentially large clocks are not enumerated.

**Theorem 8.2 (a coherent physical path from each clock hypothesis).**
For each $(A,B)\in\mathcal A_m$, the following recursion over ordinary
integers defines a single infinite physical word $R_{A,B}=c_1c_2\cdots$,
independent of a proposed rank, cut or terminal tie:

$$
\begin{aligned}
J_1&=A,&J_2&=B,\\
b_k&=y_{J_k-1},&
c_k&=\begin{cases}a,&b_k=1,\\b,&b_k=0,\end{cases}\\
J_{k+2}&=J_{k+1}+J_k+1-b_k &&(k\ge1).
\end{aligned}
\tag{PSA.8.2}
$$

The letters are computed physical port names, not semantic-port
observations. At the actual pair $(I_p(1),I_p(2))$, the present part
of this word always selects the child initially labelled beta. If the
actual frontier has rank $q\ge2$, its longest present prefix therefore
has length $q-1$, including the final rank-two branch.

**Proof.** Fix any positive pair and extend $I_1=A,I_2=B$ by
$I_{k+2}=I_{k+1}+I_k$. In the hypothetical normalized beta-root history,
always choosing the initial-beta child makes the $k$th branch occur at
normalized update $k$. A chosen $b$ edge skips an initial-alpha sibling;
its beta mass immediately before branch $k$ is $F_{k-1-i}$ if that
sibling was created at branch $i<k$. Thus ACR (ACR.115) specializes to

$$
J_k=I_k+D_k,\qquad
D_k=\sum_{1\le i<k}\mathbf1_{c_i=b}F_{k-1-i}.
\tag{PSA.8.3}
$$

In particular $D_1=D_2=0$; a newly created skipped alpha sibling
contributes $F_0=0$, not one. The Fibonacci identity gives
$D_{k+2}=D_{k+1}+D_k+\mathbf1_{c_k=b}$. Adding the recurrence for
$I_k$ proves (PSA.8.2). This also proves that the recursion and the
full skipped-sibling formula specify the same word for every pair.
All $J_k$ are positive, so every referenced core index is nonnegative.

At the included actual pair, the external-forest clock and the
skipped-sibling sum are actual chronological indices by ACR Theorem
27.2. Because the entire frontier is genuinely core-only, its bit at
that index is $y_{J_k-1}$. Induction consequently identifies each
computed letter with the actual initial-beta port, for as long as the
path is present. The normalized coordinate is used in this proof of
correspondence; no physical recutting or relative-root call occurs.

On an actual nonterminal rank-$q$ cone, the initial-beta child has
rank $q-1$, even when $q=2$ and both children have singleton support.
Successive beta choices reach rank one after $q-1$ edges. No path is
longer, since each edge drops rank at least one. Choosing beta at the
last cherry is compatible with every longer hypothetical continuation:
there is no cut-dependent final physical tie. Continuing the local
recursion beyond the current leaf computes words only and does not
update the actual source. $\square$

**Theorem 8.3 (maximum measured extent is the exact frontier height).**
For each pair in (PSA.8.1), construct the first $K$ letters of
$R_{A,B}$ once. Using only paid complete literals at the actual root,
find

$$
L_{A,B}=\max\{0\le t<K:
 \operatorname{Read}(pR_{A,B}[1:t])=1\}.
\tag{PSA.8.4}
$$

An empty prefix means the already present $p$. One paid endpoint test
and at most $\lceil\log_2K\rceil$ internal bisection tests suffice.
Every operand has length at most $H$, and

$$
\operatorname{height}(p)=\max_{(A,B)\in\mathcal A_m}L_{A,B}.
\tag{PSA.8.5}
$$

No acceptance bit from a rank-dependent certificate is bisected.
No pair is promoted to an authentic clock by this measurement.

**Proof.** The actual support is prefix-closed. Hence, for every fixed
word, including one generated by a false or unrealizable pair,
$t\mapsto\operatorname{Read}(pR_{A,B}[1:t])$ is monotone decreasing.
The initial endpoint is present. A present root word has length at
most $n-1$, since the actual alpha root has rank $n\ge2$. The earned
bound $n\le H$ therefore makes the complete length-$H$ endpoint at
$t=K$ absent. Pay this endpoint test as well. Maintain an actually
present lower endpoint and an actually absent upper endpoint; query
the midpoint until their distance is one. Balanced bisection gives
the stated count and exactly (PSA.8.4), without any hypothetical reply
being treated as an observation. Nonterminal frontiers have $K\ge2$.

For every pair, a present suffix of length $L_{A,B}$ is an actual
path in this very cone, so $L_{A,B}\le\operatorname{height}(p)$.
This is soundness of measured path length, independent of authenticity
of the model that selected the letters. Theorem 8.2 and inclusion of
the true pair give one pair attaining $q-1=\operatorname{height}(p)$.
Taking the maximum proves (PSA.8.5). Every pair may be processed and
discarded after updating one retained maximum; no compound existential
query is assigned unit cost. $\square$

**Theorem 8.4 (logarithmic-Read acquisition on the original entrance).**
Under exactly Definition 1.1, there is one uniform deterministic
procedure returning and retaining the original transient-inclusive
$(P,n)$ on every admitted source and every mature finite cut. For an
absolute constant $C_1$, with $S=d+H+2$, its every-execution bounds are

$$
\begin{aligned}
Q_{\rm acq}&\le C_1(d+1)^{19}
 (1+\lceil\log_2(H+2)\rceil),\\
M_{\rm acq}&\le H,&J_{\rm acq}&\le HQ_{\rm acq},\\
C_{\rm acq},W_{\rm acq}&\le C_1S^{60},&
V_{\rm acq}&\le C_1S^8,&U_{\rm source}&=0.
\end{aligned}
\tag{PSA.8.6}
$$

There is no catalogue of source laws, period enumeration, supplied
hidden clock, free relative port or stronger reply. All singular
transients, nonminimal presentations, repeated core factors and
unrestricted periods in the original promise remain in scope.

**Proof.** Use Definition 8.1's paid prelude. In the small-root branch
nothing changes. Otherwise replace only the frontier height search of
Definition 4.1 by Theorem 8.3. Terminals encountered during shallow
exploration have height zero; their ranks zero and one need not be
distinguished. Recombine the exposed actual finite tree by one plus
the maximum of child heights. Theorems 8.2--8.3 prove all these heights
exact, including at $d=0$ with the known zero descriptor and its
bounded root clock family. They do not presume a supplied cut.

Now use Theorem 4.2's global consumer unchanged. Root height gives
$n=1+\operatorname{height}(\varepsilon)$. For each $j\le2d$,
previously recovered bits reconstruct the actual old tree at
$\tau(j)-1$, where $\tau(j)=\min\{t\ge2:j\le F_{t+1}-1\}$.
The actual physical ordering identifies its $j$th-birth parent.
Maturity gives $\tau(j)\le n-1$ and child depths at most $h_0$.
The two exact child heights are $n-\tau(j)$ and $n-\tau(j)-1$,
with the larger at $a$ exactly when $z_j=1$. This recovers each original
bit, including its transient, by induction. It uses actual root replies
at these shallow parents and never substitutes aligned core bits for
the requested prefix. Retain the auxiliary Gaussian descriptor and
ACR Corollary 22.3's final proper-candidate verifier from Theorem 4.2;
its at most $2d+3$ paid tests pass on the authentic answer. Its arbitrary
passing row is still not the original first row under $\rho_d$.

There are at most $4d+1$ height calls, each with $O((d+1)^2)$ shallow
nodes and frontiers. At a frontier, every one of $O((d+1)^{16})$ pairs
is charged at most $1+\lceil\log_2(H-m)\rceil$ Reads. Add all start,
child and terminal tests, the paid spine acquisition, the bounded-cone
or small-root scan and the final verifier. These give (PSA.8.6)'s
$Q$. There is no residual rank loop. Theorem 2.1 bounds prelude
literals by $H$; Theorem 8.3 bounds every bisection literal by $H$;
the unchanged final verifier has the same guard. Thus $M,J$ follow
for the full root words, not only their suffixes.

Here is explicit bit accounting for all pairs, whether or not they
attain the maximum. In (PSA.8.2), let $Z_k=J_k+1$. Then
$Z_{k+2}=Z_{k+1}+Z_k-b_k\le Z_{k+1}+Z_k$. Fibonacci comparison
with $Z_1=A+1,Z_2=B+1$ bounds every generated index by
$F_{k+1}(A+B+2)$. For $k\le K+2\le H+2$ this has
$O(H+\log(d+2))=O(S)$ bits. The hypothetical indices can be
exponentially large numerically; none is a unit-cost integer.

Generate at most $H$ letters per pair, evaluating each $y_{J_k-1}$
from the earned recurrence and seed by binary companion powering or
monic polynomial reduction. These operations apply over a quotient
ring even with repeated factors; no field inversion or period word is
needed. Bostan--Mori, §1.3, gives the classical explicit-recurrence
term-evaluation correspondence. Recomputing powers at every letter
costs polynomially many bit operations. Charge the two index-register
updates, carries, exponent scans, all power scratch initialization and
overwrites, core-bit writes, path writes and loop counters even on
nonattaining pairs. Bisection additionally charges each midpoint
calculation and a fresh full-root literal copy, including repeated
prefixes. Its $O(H\log(H+2))$ copied bits per pair are polynomial;
logarithmic Reads do not give logarithmic traffic or work.

More explicitly, the sequential layout in Theorem 5.1 retains at most
$O(S^5)$ bits in its largest prelude: $O((d+1)^4)$ delimited tree
records of $O(S)$ bits each, matrix scratch, prefixes and counters.
Its existing traversal, sorting and core-alignment calculation has
$O(S^{12})$ indexed bit operations. Subsequently retain only the core,
the shallow traversal, early-parent old trees, an $O(H)$-letter current
ray, $O(S)$-bit clock/index operands, companion scratch, one maximum,
bisection counters, full-literal buffers and the original output.
One pair, including its literal copies and every counter/operand
write, fits $O(S^6)$ indexed bit operations as in Theorem 5.1's
path construction; the scalar index recursion only reduces its
skipped-sibling work. No list of rays or discarded trial history is
stored.

Allow the conservative common backing cap $O(S^8)$, including scratch,
addresses, markers and output copies. Implement each indexed access by
sequential scans of that layout, paying head returns and represented
address/counter maintenance. Even $O(S^2)$ work and writes per scanned
cell gives $O(S^{10})$ sequential work and writes per indexed operation.
There are $O((d+1)^{19})\le O(S^{19})$ ray trials in total. Their
$O(S^6)$ indexed operations per trial therefore give at most
$O(S^{35})$ sequential work and writes. The prelude's corresponding
bound is $O(S^{22})$; the unchanged early-tree reconstruction, Gaussian
solve, final path verification and retained output have smaller bounds
than the conservative $O(S^{60})$ envelope. Source request handling
and every actual literal write are included locally; no uniform
service duration is inferred. Reinitializing and overwriting the same
cells increases $W$ each time, even though it does not increase $V$.
This proves $C,W,V$ for every execution, without favorable averaging
or free advice. $\square$

**Mathematical correspondence 8.5 (suppliers and boundaries).** The new
source-specific content is (PSA.8.2)--(PSA.8.5) and its composition with
the already acquired aligned core and original-prefix consumer. ACR
Theorem 27.2 supplies both bounded shallow integer clocks and the exact
skipped-sibling index; ACR Theorem 27.3 supplies the genuine core cutoff.
GPO Definition 27.1 supplies the actual alpha origin, simultaneous
old-leaf dynamics and physical $a<b$ chronological actuator. GPO
Proposition 39.2 supplies the original early-parent selection.
Theorems 2.1--3.1 supply the paid cone and alignment; their PCR complete-
support correspondence is applied only to an actually acquired cone.
These suppliers have exactly Definition 1.1's source and service domain.

Composition uses Theorem 6.1 with the original $K_d/\rho_d$ firstness
and deficient-rank normalization, including failed rows and transfers.
The Fibonacci payload, optional phase, binding, grants, code and service
apparatus, actual Read tariffs and durations, allocation, retention,
physical field writes and completed handoff retain their separate bills.
The stationary interval must cover all realized acquisition work and
writes, and additionally all installation work when installation is
requested. The local $V$ bound excludes the existing source material.
No uniform physical latency or weighted total-cost optimum is asserted.

Bentley--Yao, *An Almost Optimal Algorithm for Unbounded Searching*,
[SLAC-PUB-1679](https://www.slac.stanford.edu/pubs/slacpubs/1500/slac-pub-1679.pdf),
pp. 2--5, Algorithm B1, supplies classical comparison search; monotonicity
here is proved on fixed actual physical prefixes before invoking that
search. ACR Theorem 3.2 and Proposition 5.1 instead start with retained
authentic $P,L$ and are not erased-input acquisition suppliers. Their
retained-input threshold compiler is not assumed here. Massey, Shoup
and Bostan--Mori have the explicit-symbol algebraic domains stated in
§7: synthesis consumes acquired entries, and distant-term evaluation
consumes an explicit recurrence and seed. Neither supplies a source
sample or hidden clock.

A wrong-clock path can have the correct measured extent; this does not
certify its clock. Rank-two support cannot identify the last orientation;
selecting the computed beta port merely makes the path coherent across
cuts. Both integer coordinates are still enumerated. An acquired core
and a local height remain different from the original transient-inclusive
$P$ and actual $n$; Theorem 8.4 retains the global early-parent calls.
These distinctions account for the false-model, tie and local/global
boundaries without using them as counterexamples to the fixed-path
construction. The stated result is an ordinary source-specific proof,
not a new compiled Lean theorem or a claim of worldwide priority.

## 追加锚（本行以下为增补区）

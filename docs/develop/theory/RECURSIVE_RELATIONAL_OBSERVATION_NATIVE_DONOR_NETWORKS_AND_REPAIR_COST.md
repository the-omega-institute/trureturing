# Recursive relational observation: native donor networks and repair cost

## 1. The native task and the temporal recovery relation

**Definition 1.1 (actual source and literal observation).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,\qquad
h(\langle x,y\rangle)=1+\max\{h(x),h(y)\}.
$$

All entropy and rate logarithms are base two. Pairing is free and ordered.
Every finite word in $L,R$, including
$\varepsilon$, is a legal original-root literal. The reply $r_t(w)$ is
alpha, beta or branch at the addressed constructor, and absent when the
path passes a leaf. Define

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

For public $D\ge1$, the source and request families are exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
W_D=\{q:|q|\le D-1\},\qquad
\mathcal P_D=\{Rq:q\in W_D\}.
\tag{NDR.1}
$$

The actual initial source remains stationary through preparation and later
acquisition. The iterates $\rho^kt$ describe prediction targets, not updates
to that source. There is no subtree, equality, source-identity, age, reset,
copying, free-navigation or free-advice port.

**Assumption 1.2 (complete paid preparation and late reading).** One
deterministic effective procedure starts source-blind from $D$ and common
installed tables, does not receive the later target, and terminates on
every $t\in\mathcal F_D$. It acquires source dependence only through charged
literal Reads. It exports a finite code $E(t)$ whose complete attained
alphabet includes all accessible surviving source distinctions: selectors,
control, buffers, operands, lengths, allocation, handles, counters and
accessible timing distinctions. Every other accessible field after handoff
is a function of this code and public data. A separately paid service
isolates transcripts and other preparation material and supplies lawful
reader entry. Export, isolation, continuity and authentication are declared
services, not inferred physical operations.

Only after export is a source-independent public $p\in\mathcal P_D$
supplied. A common deterministic reader uses $E(t),D,p$ and the installed
tables. It makes zero Reads or one fresh Read of the same stationary source
at any finite word chosen from those inputs. It produces a final predictor
$Z$. Every subsequently supplied authentic $k\ge0$ must satisfy

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad(t\in\mathcal F_D,\ p\in\mathcal P_D,\ k\ge0),
\tag{NDR.2}
$$

without further Reads. No supplied $k$ guides the query. Define $M_1(D)$ as
the minimum $|E[\mathcal F_D]|$ among these jointly correct procedures.
Only that complete retained alphabet is optimized. Preparation Reads,
work, control, installed codebooks, temporary storage, post-request
workspace, final predictor size, address length, submitted letters, count
representation, entry, handoff, isolation and physical time are separate
resources.

**Convention 1.3 (credited exact temporal factor).** Use the factor
$\Gamma_q(u)=(b,c)$ of [AAR, Definition 12.2, Theorem 12.3 and
Proposition 13.3][AAR]. Put $s(r)=\#L(r)+2\#R(r)$ and
$e(\alpha)=0,e(\beta)=1$. At an original branch endpoint the factor is
$(0,0)$. Otherwise let the first original leaf on the path have address
$a$, label $\ell$, and $q=ar$. Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{NDR.3}
$$

Its supplied decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{NDR.4}
$$

On attained factors $c=1$ implies $b\ge2$. For every $k$ this equals
$r_{\rho^ku}(q)$. The trajectory recovers $b$ as its first branch count
and $c$ by whether an alpha stage occurs. Equality of factors is therefore
exactly equality of complete trajectories. This includes initially absent
targets; it does not identify their different blocking-leaf descriptors.
For a permitted original request, $b\le2D$.

The supplier's temporal calculation uses $T_k=\rho^k\alpha$,
$T_0=\alpha,T_1=\beta,T_{k+2}=\langle T_{k+1},T_k\rangle$.
Traversal subtracts one for $L$ and two for $R$, with each edge allowed only
when its preceding index is at least two. Thus a nonempty $R$-ending
suffix has an alpha stage and an $L$-ending suffix does not. Transport is
applied at its actually present original blocking leaf. This is why
(NDR.3) handles absence without transporting a nonexistent subtree.

**Definition 1.4 (canonical blocks and all correlated competitors).**
Following [FMR, Definitions 2.1 and 6.1][FMR], put

$$
C_0=\langle\alpha,\alpha\rangle,\quad
S_1=\{\alpha,\beta,C_0\},\quad
S_{d+1}=\{\alpha,\beta\}\sqcup
\{\langle x,y\rangle:x,y\in S_d\}.
\tag{NDR.5}
$$

These are actual trees of height at most $d$. Write $Q=W_d$,
$g_q(x)=\Gamma_q(x)$ and $r_a(x)=r_x(a)$ for $q,a\in W_d$.
A nonempty $B\subseteq S_d^n$ is jointly admissible when each target
$g_q(x_i)$ is constant on $B$, or is determined there by one reply
$r_a(x_j)$ for some $j,a$. Equivalently, for the selected donor experiment,

$$
r_a(x_j)=r_a(y_j)\ \Longrightarrow\ g_q(x_i)=g_q(y_i)
\quad(x,y\in B).
\tag{NDR.6}
$$

Choices may depend on the whole set $B$ and separately on $i,q$; donors
may be self donors or off-coordinate donors. No independence, acyclicity,
bounded component size or common experiment across targets is required.
Let $K_d(n)$ and $Z_d(n)$ be the integral and fractional cover optima of
$S_d^n$ over this entire family. Joint admissibility is downward closed on
nonempty subsets and invariant under coordinate permutations.

**Convention 1.5 (cited normalization, acquisition and rate theorems).**
[FMR, Lemma 2.2 and Theorems 2.3–2.5][FMR] preserve the full task by
canonical completion: keep all constructors through depth $d-1$, and
replace a branch at the cutoff by $C_0$. On $S_d$, a length-$d$ word
returns alpha exactly when its length-$(d-1)$ parent is branch and absent
otherwise; longer words are absent. Every arbitrary finite block probe is
therefore a function of one boundary reply in its original queried block,
or is constant. Zero-Read branches remain allowed. This is a proved
whole-encoder normalization; it is not a claim that arbitrary child
projections of an unchanged fiber are admissible.

A finite admissible cover is attained by paid acquisition and a
first-containing-member name. At actual prefix-free block occurrences
$Ra_i$, with $|a_i|\le H$, [FMR, Lemma 6.2][FMR] gives sufficient bounds

$$
T\le n(2^d-1),\quad Q_{\rm addr}\le H+d,\quad
A_{\rm letters}\le n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr).
\tag{NDR.7}
$$

The calls are the original-root literals $Ra_iw$, $w\in W_d$.
Installed colors are not supplied as source-dependent advice: the tuple
selecting the name is acquired by these calls. Public cover generation,
membership computation and isolation remain separate resources.

[FMR, Theorems 3.2–3.3 and 6.3–6.4][FMR] supply

$$
\begin{aligned}
M_1(D+1)&\le M_1(D)^2+1,\\
\lambda&=\lim_{D\to\infty}2^{-D}\log_2M_1(D),\\
\sigma_d&=\lim_{n\to\infty}n^{-1}\log_2K_d(n)
          =\inf_{n\ge1}n^{-1}\log_2K_d(n),\\
\lambda&=\sup_{d\ge1}2^{-d}\sigma_d,
\qquad 0\le\lambda-2^{-d}\sigma_d\le2^{-d}\phi,
\end{aligned}
\tag{NDR.8}
$$

where $U_0=1,U_{h+1}=1+U_h^2$ and
$\phi=\lim_h2^{-h}\log_2U_h$. Native gluing translates constituent
calls to actual root literals. Its upper construction covers every
variable shape; it does not impose independent child codes on competitors.

[NCM, Theorem 4.1][NCM] already supplies
$\sigma_2=\log_2(25/17)$ with a depth-two finite-length error.
[NCE, Theorems 6.1–6.2 and Corollary 6.3][NCE] already supply the
all-cyclic mass certificate, for $D\ge3$,

$$
M_1(D)\ge\left\lceil(33/13)^{2^{D-3}}\right\rceil,
\qquad \frac18\log_2(33/13)\le\lambda<0.216605159.
\tag{NDR.9}
$$

The bounds (NDR.9) leave effective lower convergence to the original rate
unresolved.

## 2. Exact finite decoder networks and binary projection closure

**Definition 2.1 (finite native constraint language).** Fix $d\ge1$.
Set $S=S_d$, $A=Q=W_d$, and $G_q=g_q(S)$. For every $z\in G_q$ allow
the unary relation $U_{q,z}=\{x:g_q(x)=z\}$. For $q\in Q,a\in A$
and every total map
$\delta:\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}\to G_q$,
allow the binary relation

$$
R_{q,a,\delta}=\{(x,y)\in S^2:g_q(x)=\delta(r_a(y))\}.
\tag{NDR.10}
$$

A complete decoder template $\Theta$ on $n$ vertices chooses, for every
$(i,q)$, either $U_{q,z}(x_i)$ or one constraint
$R_{q,a,\delta}(x_i,x_j)$, with any $j$, including $j=i$.
Let $C_\Theta\subseteq S^n$ be the simultaneous solution set.
The language depends only on $d$; graph size, donors, decoders and
topology are unrestricted. Constants are zero-Read witnesses. Self-donor
constraints are unary restrictions on the same coordinate, even though
written using (NDR.10).

**Theorem 2.2 (exact all-competitor containment).** Every nonempty
$C_\Theta$ is jointly admissible. Conversely every nonempty jointly
admissible $B\subseteq S^n$ is contained in some $C_\Theta$ on the same
$n$ coordinates. Integral and fractional cover optima, and the maximum
of any nonnegative mass over admissible sets, are unchanged when cover
members or maximizers are restricted to nonempty $C_\Theta$.

**Proof.** For each $i,q$, choose its actual witness on $B$. A constant
target supplies a unary relation. Otherwise (NDR.6) makes $g_q(x_i)$ a
well-defined function of the attained replies $r_a(x_j)$. Extend that
function arbitrarily to unattained replies in the nonempty set $G_q$.
The selected constraints all hold on $B$, so $B\subseteq C_\Theta$.
Conversely every selected constraint is itself an allowed decoder on its
entire solution set, proving that $C_\Theta$ is admissible.

Enlarge every member of a cover to its containing solution set. Coverage
cannot decrease, integral cardinality cannot increase, and fractional
coefficients retain their total weight, combining duplicates if needed.
All solution sets are themselves competitors, so the opposite optimum
inequality also holds. Nonnegative mass is monotone under enlargement,
which proves the maximum assertion. No projection, independent code or
restricted donor class is used. $\square$

**Definition 2.3 (binary projection join).** For a nonempty
$B\subseteq S^n$ define

$$
J_2(B)=\{x\in S^n:x_i\in\pi_iB\ (1\le i\le n),\quad
 (x_i,x_j)\in\pi_{ij}B\ (i<j)\}.
\tag{NDR.11}
$$

**Theorem 2.4 (binary closure preserves admissibility).** If $B$ is
jointly admissible, then $B\subseteq J_2(B)$ and $J_2(B)$ is jointly
admissible with the same chosen witnesses. Consequently every
inclusion-maximal admissible set equals its binary projection join.

**Proof.** Each chosen cross-coordinate equation for $B$ holds on its
binary projection, so it holds on every tuple in $J_2(B)$. A self-donor
equation or constant equation holds on the corresponding unary projection.
Thus $J_2(B)$ satisfies all the selected witness equations and the same
reader works there. The inclusion is immediate. Maximality gives equality.
For $n=1$ the unary projection suffices. $\square$

This is a statement about pairs of coordinates inside a relation. It does
not say that pairwise compatibility of whole source rows determines
admissibility of a set of rows. In particular it does not contradict
FMR §7's higher-arity obstruction to a whole-source confusability graph.
The join may have arbitrarily large connected components.

**Proposition 2.5 (finite enumeration and its remaining quantifier).**
Put $a=|W_d|$ and $g=\max_q|G_q|$. At most

$$
(g+nag^4)^{na}
\tag{NDR.12}
$$

complete templates need be considered at fixed $d,n$. Hence $K_d(n)$,
$Z_d(n)$ and every rational weighted maximum in Theorem 2.2 are decidable
finite problems. The fixed language does not impose a size or width bound
on the templates needed as $n$ varies.

**Proof.** For each of $na$ targets there are at most $g$ constants,
and at most $na g^4$ choices of donor, experiment and four-reply decoder.
Enumerate all choices, evaluate all tuples, and discard empty sets.
Finite set cover, finite rational linear programming and finite sums then
give the stated computations. This is a finite termination argument, not
a useful complexity estimate or an algorithm for a limit. $\square$

## 3. Finite type and mass interfaces without a lower modulus

**Definition 3.1 (exact type masses).** Fix $d,n$ and write $s=|S_d|$.
A type $\nu=(\nu_x)_{x\in S_d}$ has nonnegative integer entries summing
to $n$. Its class $T_\nu$ consists of tuples with those exact coordinate
counts. Define

$$
a_n(\nu)=\max_\Theta|C_\Theta\cap T_\nu|,\qquad
R_d(n)=\max_\nu\frac{|T_\nu|}{a_n(\nu)}.
\tag{NDR.13}
$$

Singletons are admissible, so every denominator is positive. By Theorem
2.2, $a_n(\nu)$ is also the maximum of $|B\cap T_\nu|$ over all
admissible $B$.

**Theorem 3.2 (finite type-cover comparison).** For every $d,n\ge1$,
with $H_m=\sum_{j=1}^m1/j$,

$$
R_d(n)\le Z_d(n)\le K_d(n)
\le H_{s^n}(n+1)^s R_d(n).
\tag{NDR.14}
$$

Consequently

$$
0\le\frac{\log_2K_d(n)-\log_2R_d(n)}n
\le\frac{s\log_2(n+1)+\log_2(1+n\ln s)}n,
\qquad
\sigma_d=\lim_{n\to\infty}\frac{\log_2R_d(n)}n.
\tag{NDR.15}
$$

**Proof.** For each fixed $\nu$, put dual mass $1/a_n(\nu)$ on
$T_\nu$ and zero elsewhere. Every admissible member has mass at most one,
so summing any fractional covering inequalities gives
$Z_d(n)\ge |T_\nu|/a_n(\nu)$. Maximize over $\nu$.

For the other direction choose an admissible
$B_\nu=C_\Theta\cap T_\nu$ of size $a_n(\nu)$.
Every coordinate permutation of it is admissible. The permutation group
is transitive on $T_\nu$, and each point is in exactly
$n!a_n(\nu)/|T_\nu|$ of these permuted sets, with multiplicity.
Giving each permutation coefficient
$|T_\nu|/(n!a_n(\nu))$ fractionally covers this type at cost
$|T_\nu|/a_n(\nu)$. Summing over all types gives a cover of $S_d^n$
at cost at most $(n+1)^sR_d(n)$, since there are at most $(n+1)^s$
types. The finite harmonic rounding of [FMR, Lemma 4.4][FMR] gives
$K_d(n)\le H_{s^n}Z_d(n)$, yielding (NDR.14).

For completeness, that rounding charges each newly covered point the
reciprocal of the number newly covered by the greedy chosen set. Within
any fixed admissible set these charges sum to at most $H_{s^n}$:
when $r$ of its points remain, greedy covers at least $r$ points.
Summing these charges against a fractional cover bounds the number of
chosen sets by $H_{s^n}$ times its weight. Singletons ensure termination.
Finally $H_{s^n}\le1+n\ln s$. The error in (NDR.15) tends to zero;
combine it with the supplied limit for $K_d(n)$. $\square$

The error compares two finite quantities. Neither $\log_2R_d(n)/n$ nor
$\log_2K_d(n)/n$ is thereby a certified lower endpoint for $\sigma_d$.
The latter is an upper bound on its defining infimum. A computable
converging sequence without a proved modulus does not supply two-sided
effective approximation.

**Proposition 3.3 (exact network mass obligation).** For nonnegative
$w:S_d\to\mathbb R$, define

$$
A_d(n,w)=\max_\Theta\sum_{x\in C_\Theta}\prod_{i=1}^nw(x_i).
\tag{NDR.16}
$$

It is exactly the maximum over all admissible sets. For $w>0$, put
$W=\sum_xw(x)$. Then

$$
P_d(w)=\lim_{n\to\infty}\frac{\log_2A_d(n,w)}n
       =\sup_{n\ge1}\frac{\log_2A_d(n,w)}n
\tag{NDR.17}
$$

exists and is finite, and

$$
\sigma_d\ge\log_2W-P_d(w),\qquad
M_1(d+h)\ge\left\lceil\frac{W^{2^h}}{A_d(2^h,w)}\right\rceil.
\tag{NDR.18}
$$

For positive $C$, the assertion $P_d(w)\le\log_2C$ is equivalent to
$A_d(n,w)\le C^n$ at every $n$. Finite values of $A_d(n,w)$ give
lower bounds on $P_d(w)$, not its needed upper certification.

**Proof.** Theorem 2.2 proves the maximum identity. Products of admissible
sets on disjoint coordinate groups are admissible, so
$A_d(n+m,w)\ge A_d(n,w)A_d(m,w)$, while
$A_d(n,w)\le W^n$. The superadditive limit argument proves (NDR.17).
Every cover partitions or covers total product mass $W^n$ with each
member of mass at most $A_d(n,w)$; hence
$K_d(n)\ge W^n/A_d(n,w)$. Take logarithms and limits for the first
bound. For the second, restrict any original complete code to actual
perfect-scaffold sources with $2^h$ simultaneous $S_d$ blocks. Every
restricted fiber is admissible by FMR's every-word restriction, and its
number is at most the original complete alphabet. The same mass count
gives the ceiling. The equivalence follows from the supremum in
(NDR.17). $\square$

The corresponding all-network inequality is an explicit finite tensor
sum for each template: multiply the indicators of (NDR.10) and its unary
constraints by $\prod_iw(x_i)$ and sum over $S_d^n$. A universal bound
must cover every such template at every length. It is not enough to
enumerate bounded components. Nor has completeness of product-weight
certificates for $\sigma_d$ been proved. The NCE weights already give
$W=429$ and $A_3(n,w)\le169^n$; their attained mass examples do not
supply a matching cover. This reproduces (NDR.9), not a new rate bound.

## 4. The credited five-state motif and its all-joint cap

**Definition 4.1 (the NCM native motif).** Reuse [NCM, Proposition 6.1][NCM].
Put

$$
\begin{aligned}
A&=\alpha,\quad B=\beta,\quad C=\langle A,A\rangle,\quad
J=\langle B,A\rangle,\quad Q_0=\langle C,A\rangle,\\
(u_0,u_1,u_2,u_3,u_4)
&=(C,J,\langle C,C\rangle,\langle J,J\rangle,\langle A,Q_0\rangle),\\
P&=\{u_0,u_1,u_2,u_3,u_4\}\subset S_3.
\end{aligned}
\tag{NDR.19}
$$

Let $\tau$ exchange $1,4$ and fix $0,2,3$. The credited two-module
relation is $B_* =\{(u_s,u_{\tau(s)}):0\le s\le4\}$.
For this interface, the reply and factor
tables, with columns $0,1,2,3,4$, are

$$
\begin{array}{c|ccccc}
\text{reply}&0&1&2&3&4\\\hline
\varepsilon&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}\\
L&\alpha&\beta&\mathsf{branch}&\mathsf{branch}&\alpha\\
R&\alpha&\alpha&\mathsf{branch}&\mathsf{branch}&\mathsf{branch}\\
LL&\mathsf{absent}&\mathsf{absent}&\alpha&\beta&\mathsf{absent}\\
LR&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha&\mathsf{absent}\\
RL&\mathsf{absent}&\mathsf{absent}&\alpha&\beta&\mathsf{branch}\\
RR&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha&\alpha
\end{array}
\tag{NDR.20}
$$

$$
\begin{array}{c|ccccc}
\text{factor}&0&1&2&3&4\\\hline
\varepsilon&(0,0)&(0,0)&(0,0)&(0,0)&(0,0)\\
L&(2,1)&(1,0)&(0,0)&(0,0)&(2,1)\\
R&(2,1)&(2,1)&(0,0)&(0,0)&(0,0)\\
LL&(3,0)&(2,0)&(2,1)&(1,0)&(3,0)\\
LR&(4,1)&(3,1)&(2,1)&(2,1)&(4,1)\\
RL&(3,0)&(3,0)&(2,1)&(1,0)&(0,0)\\
RR&(4,1)&(4,1)&(2,1)&(2,1)&(2,1)
\end{array}
\tag{NDR.21}
$$

**Lemma 4.2 (exact motif decoders and failure of an own donor).** The
relation $B_*$ is jointly admissible for every target in $W_3$ and every
finite native experiment word. Both projections equal $P$, on which no
own-coordinate experiment determines the $LL$ target.

**Proof.** The $LL$ factor has four values. Every experiment in $W_3$
other than $RL$ has at most three replies. The $RL$ reply merges $u_0,u_1$,
whose $LL$ factors differ. Length-three words are functions of their
length-two parent replies, and longer words are absent by Supplier 1.5.
Zero Reads cannot determine a nonconstant factor. This exhausts arbitrary
finite own-coordinate words.

In $B_*$, $LL$ is recovered from the mate's $RL$ reply using

$$
\mathsf{absent}\mapsto(3,0),\quad \alpha\mapsto(2,1),\quad
\beta\mapsto(1,0),\quad\mathsf{branch}\mapsto(2,0).
\tag{NDR.22}
$$

The same rule works in both directions because $\tau^2=1$. The complete
selection rule is

$$
\begin{array}{c|ccccccc}
\text{target}&\varepsilon&L&R&LL&LR&RL&RR\\\hline
\text{donor}&\text{none}&\text{own}&\text{own}&\text{mate}&\text{own}&\text{own}&\text{own}\\
\text{word}&\text{constant}&L&R&RL&L&RL&R.
\end{array}
\tag{NDR.23}
$$

The root factor is $(0,0)$. For $L,R$, map alpha, beta, branch to
$(2,1),(1,0),(0,0)$ on attained replies. For $LR$ read $L$ and map
alpha, beta, branch to $(4,1),(3,1),(2,1)$. For $RL$ read $RL$ and map
absent, alpha, beta, branch to $(3,0),(2,1),(1,0),(0,0)$. For $RR$ read
$R$ and map alpha, branch to $(4,1),(2,1)$. The tables verify all seven
targets in both coordinates. Equation (NDR.4) then gives every authentic
count, not merely the initial readout. $\square$

**Lemma 4.3 (credited all-cyclic entropy supplier, specialized to $P$).**
For every $r\ge0$ and every jointly admissible $T\subseteq P^r$, allowing
arbitrary cyclic donors and all finite words,

$$
|T|\le4^r.
\tag{NDR.24}
$$

**Proof.** For $r=0$ there is at most one tuple; empty $T$ is immediate.
Apply [NCE, Theorem 2.2][NCE] to the seven native target functions and
boundary experiments restricted to $P$, with unit weights, reply bound
$m=4$ and mass cap $C=4$. Its hypothesis is: every range-feasible subset
with mass greater than $C$ has a target not determined by an own experiment,
whose squared target-cell masses sum to at most $C^2$. The only subset
heavier than four is $P$ itself. It is range-feasible by (NDR.21); its
$LL$ target has cell sizes $2,1,1,1$, squared sum $7\le16$, and no own
witness by Lemma 4.2. Thus all hypotheses hold. Normalization of longer
words stays within the same coordinate, so they do not change the class.

Here is the relevant entropy mechanism, to make its all-joint scope
explicit. Let $X$ be uniform on $T$, let $I$ be the coordinates whose
marginal support is all of $P$, and put $Y_i=\Gamma_{LL}(X_i)$ for
$i\in I$. The chosen donor $j_i$ for that target is distinct from $i$,
and $Y_i$ is a function of both $X_i$ and $X_{j_i}$ under this same law.
Write $\mathcal C=\sum_iH(X_i)-H(X)$. For any ordering, the contribution
$H(X_i)-H(X_i\mid\text{earlier coordinates})$ is at least $H(Y_i)$
when $j_i$ is earlier. Average over all orders: each distinct donor is
earlier with probability $1/2$. Hence
$\mathcal C\ge\tfrac12\sum_{i\in I}H(Y_i)$, including cycles.

A coordinate outside $I$ has entropy at most $\log_2 4$. For one in $I$,
condition on the four target cells, with sizes $a_z=2,1,1,1$ and
probabilities $p_z$. The log-sum entropy bound gives

$$
H(X_i)-\tfrac12H(Y_i)
\le\tfrac12H(p)+\sum_zp_z\log_2a_z
\le\tfrac12\log_2\sum_za_z^2
=\tfrac12\log_2 7\le\log_2 4.
$$

Subtract the total-correlation charge from the sum of marginal entropies
to obtain $H(X)\le r\log_2 4$. Uniformity gives (NDR.24). This is the
NCE random-order argument, not an independence assumption or a new entropy
theorem. $\square$

## 5. Original-block components and the lawful conditioning interface

**Definition 5.1 (bounded original-block donor components).** For a
nonempty jointly admissible $H\subseteq S_d^N$, choose one valid witness
for every coordinate-target pair, using a constant witness whenever that
target is constant on $H$. Form an undirected graph on the original
$N$ coordinates: a selected nonconstant target in $i$ with a donor
$j\ne i$ adds the edge $\{i,j\}$. Self donors add no edge.
Call $H$ *$b$-component admissible* if some such witness system has every
connected component of size at most $b$. Each replacement set may choose
its own witnesses, decoders and component partition. Correlations between
components are permitted in $H$.

**Lemma 5.2 (projection only along donor-closed parts).** For a chosen
witness system let $\Pi$ be its connected-component partition. For every
$C\in\Pi$, $A_C=\pi_C(H)$ is jointly admissible on its coordinates, and

$$
H\subseteq\prod_{C\in\Pi}A_C.
\tag{NDR.25}
$$

**Proof.** Every nonconstant selected donor for a target in $C$ belongs
to $C$. Its equation on $H$ therefore involves only coordinates in $C$.
To verify it on $A_C$, lift any projected tuple to $H$ and apply that
equation. Constant equations and self-donor equations also descend. The
selected witnesses work on the whole projection. The inclusion follows
from projection. This does not assert that $H$ is a product, or that any
arbitrary coordinate projection is admissible. $\square$

**Lemma 5.3 (splitting actual modules after fixed-value conditioning).**
Suppose an admissible $A\subseteq S_5^C$ is restricted so every coordinate
has the actual four-module form

$$
\langle\langle z_{LL},z_{LR}\rangle,
              \langle z_{RL},z_{RR}\rangle\rangle,
\qquad z_w\in P.
\tag{NDR.26}
$$

Fix any collection of those modules to specified values. The relation
$T$ on all remaining $r$ module positions induced by the restricted set
is empty or jointly admissible in $P^r$. It need not be a product. In
particular $|T|\le4^r$; for $r=0$ there is at most one tuple.

**Proof.** Empty relations and $r=0$ satisfy the size bound directly.
Otherwise restriction preserves every witness equation on $A$. Each
target $q\in W_3$ in a remaining module at port $w$ is the permitted
parent target $wq\in W_5$, because $|wq|\le4$. Its selected experiment
in a parent coordinate either ends above the module frontier, giving
constant branch, or enters exactly one module. If that module is fixed,
its reply is a mathematical constant on the restricted set. Otherwise it
is one native experiment in one remaining module; its suffix has length
at most two for a normalized parent experiment. Thus its equation induces
an allowed constant, self or other-module witness on $T$. For arbitrary
finite parent experiments the same argument and Supplier 1.5 reduce the
suffix in its original module. Every required module target is covered.
Apply Lemma 4.3. The fixed module values are used only in this analytical
conditioning argument; no reader is supplied these values as free advice.
$\square$

## 6. Effective expanding graphs and native graph fibers

**Lemma 6.1 (effective four-regular graph family).** For every $j\ge0$,
with $N=8\cdot2^j$, there is a finite simple four-regular bipartite graph
$G_N=(V,E)$ on $N$ vertices such that

$$
|E|=2N,\qquad
|\partial A|\ge |A|/4\quad(1\le|A|\le N/2),
\tag{NDR.27}
$$

where $\partial A$ is the set of edges with exactly one endpoint in $A$.
A graph satisfying these rational inequalities can be selected effectively
from $N$ alone.

**Proof.** [Marcus–Spielman–Srivastava, Theorems 5.3 and 5.5][MSS]
give a bipartite Ramanujan two-lift at every stage starting from $K_{4,4}$.
A two-lift of a simple bipartite four-regular graph is again simple,
bipartite and four-regular, and doubles its order. Its new adjacency
eigenvalues lie in $[-2\sqrt3,2\sqrt3]$; old eigenvalues are retained.
The trivial eigenvalues $\pm4$ stay simple, since no new eigenvalue can
equal them. Thus these graphs are connected and their second largest
adjacency eigenvalue is at most $2\sqrt3$.

For $a=|A|$, put $f=\mathbf1_A-(a/N)\mathbf1$. With adjacency matrix
$M$ and Laplacian $L=4I-M$, $f\perp\mathbf1$, and

$$
|\partial A|=f^{\mathsf T}Lf
\ge(4-2\sqrt3)\|f\|^2
=(4-2\sqrt3)a(1-a/N)
\ge(2-\sqrt3)a>a/4.
$$

The last strict inequality follows from $3<49/16$, equivalently
$\sqrt3<7/4$. This implies (NDR.27).

For an effective choice, enumerate all labeled simple graphs with a fixed
balanced bipartition of $V$, test four-regularity, and test
$4|\partial A|\ge|A|$ for every $A$ with $1\le|A|\le N/2$.
These are finite integer tests. Existence from the preceding proof ensures
termination; no numerical spectral decision is needed. A crude bound is
$2^{\binom N2}$ candidates and $2^N$ subset tests per candidate, each with
at most $N^2$ edge inspections. This bounds a separate public computation,
not an efficient graph generator or an actual source acquisition. $\square$

**Definition 6.2 (native graph fiber at fixed depth five).** Fix the
effective graph $G_N$ and a public ordering of its bipartition. Assign each
vertex's four incident edges bijectively to its ports $LL,LR,RL,RR$.
Give every edge $e$ a label $s_e\in\{0,1,2,3,4\}$. At its endpoint in
the first bipartition place $u_{s_e}$ in that port; at the other endpoint
place $u_{\tau(s_e)}$. Assemble the four modules by (NDR.26) to obtain
$x_v\in S_5$. Let $B_G\subseteq S_5^N$ contain the tuples from all edge
label assignments. Labels are mathematical parameters of a source family,
not operational inputs supplied to a reader.

**Proposition 6.3 (exact size and full native admissibility).**

$$
|B_G|=5^{2N},
\tag{NDR.28}
$$

and $B_G$ is jointly admissible for all targets in $W_5$, with every finite
experiment word allowed. A target $wLL$ in an edge's module can only have
the opposite endpoint as its donor block on the full $B_G$.

**Proof.** All five module trees are distinct and $\tau$ is a bijection.
The tuple of actual module states mathematically recovers every edge
label, proving injectivity and (NDR.28). Targets strictly above the module
frontier are constantly branch. Every remaining target is $wq$ with
$|w|=2$ and $q\in W_3$. Apply (NDR.23) in its module. Its mate is the
opposite endpoint's port for the same edge; querying that port followed
by $RL$ is one allowed depth-five experiment. All other nonconstant
targets use the specified own-module experiment. The factors give every
later $k$ by (NDR.4).

For the donor assertion, vary only the edge label at the tested port.
An experiment above a module is constant. An experiment in any unrelated
module depends on a different label, which can be held fixed, and cannot
recover the varying target. A query in the target's own module fails by
Lemma 4.2. A word enters at most one module, including an arbitrarily long
word. The only remaining possible block is the opposite endpoint.
Independence of edge parameters is used to prove this statement about the
constructed family; no independence assumption is made about replacement
sets or general competitors. $\square$

The forced-donor property excludes a bounded-component enclosure of
$B_G$. Theorem 7.2 bounds its intersection with every bounded-component
replacement, including different equations and additional rows outside
$B_G$.

## 7. Exponential obstruction to bounded original-block repair

**Lemma 7.1 (shared-variable entropy count).** Let $F$ be a finite set
of variables, and let $(F_C)_C$ be subsets in which every variable occurs
exactly twice. For any nonempty finite relation $Y$ on those variables,
if $|\pi_{F_C}Y|\le4^{|F_C|}$ for every $C$, then $|Y|\le4^{|F|}$.
No independence is assumed.

**Proof.** Put the uniform law on $Y$ and order the variables of $F$.
The chain rule and conditioning monotonicity give

$$
\begin{aligned}
\sum_C H(Y_{F_C})
&=\sum_C\sum_{e\in F_C}
  H(Y_e\mid Y_{F_C\cap\{\text{variables before }e\}})\\
&\ge\sum_C\sum_{e\in F_C}
  H(Y_e\mid Y_{\{\text{variables before }e\}})
=2H(Y_F).
\end{aligned}
$$

On the other hand $H(Y_{F_C})\le\log_2|\pi_{F_C}Y|
\le |F_C|\log_2 4$. Sum and use $\sum_C|F_C|=2|F|$.
Uniformity gives $\log_2|Y|\le |F|\log_2 4$. This is the finite
twice-covered instance of Shearer's entropy inequality, attributed to
Chung–Graham–Frankl–Shearer [CGFS]; the proof here states all the needed
finite hypotheses. Empty coordinate lists cause no difficulty. $\square$

**Theorem 7.2 (all-replacement expander cut bound).** For every integer
$j\ge0$, $N=8\cdot2^j$, every integer $1\le b\le N/2$, and every nonempty $b$-component
admissible $H\subseteq S_5^N$,

$$
\boxed{|H\cap B_G|\le5^{2N}(4/5)^{N/8}.}
\tag{NDR.29}
$$

The quantifier includes arbitrary rewiring, correlated components,
different partitions for different $H$, and $H$ extending outside $B_G$.

**Proof.** Choose any witness system realizing the component bound for
$H$, and let $\Pi$ be its component partition. By Lemma 5.2, each
$A_C=\pi_C(H)$ is admissible and
$H\subseteq R=\prod_{C\in\Pi}A_C$. This product is an analytical
enlargement of the given set, not an assumed factorization of it.

Let $F$ be the graph edges crossing between parts of $\Pi$, and set
$c=|F|$. Each part has size at most $N/2$, so (NDR.27) gives

$$
2c=\sum_{C\in\Pi}|\partial C|
\ge\tfrac14\sum_C|C|=N/4,
\qquad c\ge N/8.
\tag{NDR.30}
$$

Fix the labels of all $2N-c$ edges internal to parts. There are exactly
$5^{2N-c}$ such choices. In each part $C$, restrict $A_C$ to the actual
four-port scaffold, to modules in $P$, and to those fixed internal edge
modules. Let $r_C=|\partial C|$ be its number of crossing incidences.
The induced relation $T_C$ on its remaining $r_C$ modules is jointly
admissible in $P^{r_C}$ by Lemma 5.3, so $|T_C|\le4^{r_C}$.
It may be empty, in which case this internal assignment accepts nothing.
No assumption that $A_C$ was originally confined to these scaffolds is
used: restriction only removes its other rows and preserves its equations.

For this fixed internal assignment let $Y$ be the crossing-edge label
assignments whose full tuple belongs to $R\cap B_G$. Its projection to
$\partial C$ maps injectively into $T_C$: on each crossing incidence the
module state is $u_{s_e}$ or $u_{\tau(s_e)}$, both bijective functions of
that edge label. Hence $|\pi_{\partial C}Y|\le4^{r_C}$. Every crossing
edge has exactly two endpoints in different parts, so its variable is in
exactly two of the sets $\partial C$. Lemma 7.1 gives $|Y|\le4^c$,
including arbitrary correlations among the crossing labels. Empty $Y$
also satisfies this bound.

Sum over the internal choices and use injectivity from Proposition 6.3:

$$
\begin{aligned}
|H\cap B_G|&\le|R\cap B_G|\le5^{2N-c}4^c\\
&=5^{2N}(4/5)^c
\le5^{2N}(4/5)^{N/8}.
\end{aligned}
$$

The witnesses and partition used here were those of the arbitrary
replacement $H$, not those defining $B_G$. The proof does not fix crossing
labels, demand exact product subfibers, or require $H\subseteq B_G$.
$\square$

**Corollary 7.3 (integral and fractional repair costs).** Any fractional
cover of $B_G$ by $b$-component admissible subsets of $S_5^N$, with
$b\le N/2$, has total weight at least

$$
(5/4)^{N/8}.
\tag{NDR.31}
$$

Every integral such cover has at least $\lceil(5/4)^{N/8}\rceil$
members. Overlaps and replacement sets extending outside the test fiber
are allowed. The unrestricted fiber $B_G$ itself is one admissible set.

**Proof.** Give $B_G$ uniform probability mass. Theorem 7.2 says every
replacement has mass at most $(4/5)^{N/8}$. Multiply its pointwise covering
inequalities by this probability law and sum. If its coefficients are
$c_H$, then $1\le(4/5)^{N/8}\sum_Hc_H$. The integral ceiling follows.
$\square$

**Corollary 7.4 (the precise completeness mechanism excluded).** At fixed
native depth five there is no uniform assertion that every admissible
fiber on $N$ original blocks can be covered by $2^{o(N)}$ admissible
replacements whose donor components have size bounded independently of
$N$. The same obstruction holds if that size bound is $b_N\le N/2$.
The worst-case per-fiber normalized logarithmic cost for this mechanism
is at least $\tfrac18\log_2(5/4)$ bits per original block.

**Proof.** Apply Corollary 7.3 along $N=8\cdot2^j$. For a fixed cutoff
$b$, eventually $N\ge2b$, and the logarithm of the required number divided
by $N$ is at least the stated positive constant. A cutoff
$b=b(\epsilon)$ chosen before $N$ cannot make this uniform loss vanish
as $\epsilon\to0$: arbitrarily large such $N$ remain. $\square$

Corollary 7.4 excludes uniform subexponential per-fiber repair at the fixed
original-block interface. Noncomputability or impossibility of effective
approximation of the native rate does not follow from that obstruction.

## 8. Paid attainment on the complete original source family

**Theorem 8.1 (one lawful attained fiber, all original targets and counts).**
Let $N=8\cdot2^j=2^h$, $h=j+3$, and $D=h+5$. There is a correct
procedure on the entire unchanged $\mathcal F_D$ satisfying Assumption
1.2 with one attained fiber exactly the sources obtained by placing
$B_G$ on a perfect height-$h$ right-subtree scaffold. Every other source
has a distinct singleton code. With

$$
f_0=2,\qquad f_{d+1}=2+f_d^2,
\tag{NDR.32}
$$

its complete attained alphabet has exactly

$$
f_D-5^{2N}+1
\tag{NDR.33}
$$

values. Preparation uses, on every source,

$$
T=2^{D+1}-1,\qquad Q_{\rm addr}=D+1,\qquad
A_{\rm letters}=D\,2^{D+1}+1.
\tag{NDR.34}
$$

The reader uses at most one fresh original-root Read of length at most
$D$, chosen before any supplied $k$; all subsequent counts are answered
without Reads.

**Proof.** List the frontier addresses of a perfect height-$h$ scaffold
as $a_v$, $v\in V$, so $|a_v|=h$. Insert the actual tree $x_v\in S_5$
there, giving $v_x$, and set $t_x=\langle\alpha,v_x\rangle$.
Its right-subtree height is at most $h+5=D$. These actual sources belong
to $\mathcal F_D$ and are distinct for distinct $x\in B_G$. Denote
their family by $\mathcal B_G$; it has $5^{2N}$ members.

Before any request, submit every literal $Rw$ with $|w|\le D$ on the
actual stationary source, including absent words. Since $h(v)\le D$,
these replies reconstruct the entire finite ordered right subtree,
including terminal labels. The fixed scan has
$\sum_{l=0}^D2^l=2^{D+1}-1$ calls, maximum length $D+1$, and
$\sum_{l=0}^D(l+1)2^l=D2^{D+1}+1$ submitted letters. The source
is neither changed nor copied by this acquisition.

Membership in $\mathcal B_G$ is now a finite local computation from this
paid description: test the fixed scaffolds, identify each of its five
possible module trees, and test each edge's $\tau$ relation. No unknown
source identity or tuple was given as an input. Export code $0$ exactly
on this family; give every other acquired tree its own index in a fixed
public ordering. There are exactly $f_D$ right subtrees of height at most
$D$ by ordered pairing and (NDR.32). Merging precisely $5^{2N}$ of
their names gives (NDR.33). Every specified code is attained.

Use a fixed-width representation of the complete name. The public scan,
buffer allocation and a padded finite computation schedule may be fixed
from $D$ alone. All other acquired descriptions, membership workspaces,
selectors and source-dependent control or timing records are isolated by
the separately paid service. Every accessible surviving distinction must
be a function of the name and public data; any failure of that isolation
would fail Assumption 1.2 rather than justify an uncounted field.

After a target is supplied, a singleton name identifies its acquired
source through the installed source-independent table. Compute its
factor by (NDR.3) with zero Reads. On name $0$, a target ending strictly
above the module frontier is constantly branch. Every remaining target
is uniquely

$$
p=Ra_vwq,\qquad |a_v|=h,\quad |w|=2,\quad q\in W_3,
\qquad |p|\le1+h+2+2=D.
\tag{NDR.35}
$$

For $q=\varepsilon$ the factor is $(0,0)$ and no Read is needed.
For $q=LL$, read the actual original-root literal
$Ra_{v'}w'RL$, where $(v',w')$ is this edge's other endpoint port,
and apply (NDR.22). For every other $q$, use its own-module literal
$Ra_vwa$, with $a$ as in (NDR.23), and its displayed decoder.
All choices use only the name, $D,p$ and public graph/port tables;
their lengths are at most $D$. They precede the reply and any supplied
count, and there is only one actual source-bearing query.

Every scaffold and module occurrence used here is originally present on
every source with name $0$. Homomorphic substitution transports it for
every $k$, so

$$
r_{\rho^kt_x}(Ra_vwq)=r_{\rho^k u_s}(q)
=\operatorname{Pred}(\Gamma_q(u_s),k).
\tag{NDR.36}
$$

This establishes all authentic counts, including initially absent
requests. No subtree is an operational input, no source is reset, no
artificial root is queried, and no prior transcript is accessible.
$\square$

**Proposition 8.2 (resource and replacement correspondence).** The code in
Theorem 8.1 is deliberately nonoptimal. Its sole optimized resource is
the complete attained alphabet (NDR.33). Its public graph search, source
enumeration, table installation, local membership computation, temporary
descriptions, final predictor and access services are finite separate
resources. The preparation bound (NDR.34) is a sufficient actual bound,
not an acquisition optimum. A predictor factor can be represented with
at most $\lceil\log_2(2D+1)\rceil+1$ bits, separately from the retained
name and authentic count representation.

If this common fiber is repaired using names whose restrictions at the
same $N$ original depth-five block occurrences are $b$-component
admissible, then those names must cover $B_G$. Therefore Corollary 7.3
applies, even when their restricted fibers include other tuples. This is
a consequence about repair at that interface, not a lower bound on how
many names an arbitrary optimal full-family encoder must devote to this
particular family.

**Proof.** The acquisition and reader construction gives the stated
resources. The factor bound follows from $0\le b\le2D$ and $c\in\{0,1\}$.
All finite enumerations are effective from public parameters; their
potentially enormous time and table sizes are not asserted free.
Restricting any proposed repair to the actual scaffold identifies its
cover members in $S_5^N$ without changing the code values. The specified
component condition is exactly Definition 5.1 there, so it is the cover
class in Corollary 7.3. $\square$

## 9. Reblocking and the limits of the obstruction

**Proposition 9.1 (a faithful finer cut defeats this example's component
obstruction).** Split each vertex block into its four actual depth-three
modules and regroup those $4N$ module coordinates by graph edges. In
these coordinates $B_G$ is exactly a product of $2N$ copies of the
credited relation $B_*$. Its donor components for the complete module
menu can consequently have size two.

**Proof.** Each edge independently chooses its five possible paired
module states, and every module belongs to exactly one edge. Regrouping
is a permutation of this list of actual module occurrences, not a claim
that arbitrary correlated competitors factor. The definition of $B_G$
is precisely the product of these pair relations. Their readers use
(NDR.23), with each source-bearing query still the full literal at the
selected actual module occurrence. Module root locations and pairings
are public graph data, not navigation operations or new source ports.
Paid acquisition may use the already specified full-source scan.
$\square$

Thus Theorem 7.2 concerns bounded components on the original $S_5$
coordinates. It does not obstruct all changes of coordinates, all lawful
finer cuts, edge regrouping, unbounded-component methods with controlled
separators, or arbitrary global recoding. In particular this example
itself is simple after a finer cut. A universal reblocking theorem for
every native competitor, preserving the complete retained alphabet and
all literal operations with quantified loss, is a different unproved
claim. Proposition 9.1 proves it only for this family.

Nor does an exponential repair price for one intentionally nonoptimal
attained code show that optimal full-family covers must pay that price.
A global recoloring can use relationships between different old fibers
and need not replace each old fiber separately. Such a theorem is not
excluded by the intersection bound. The graph parameter $N$ counts
original blocks, not physical distance, elapsed time or the number of
available operations.

**Open problem 9.2 (the unchanged effective lower bridge).** Produce
certified all-competitor lower endpoints converging to the original
$\lambda$, with effective error, or establish an appropriate exact-rate
theorem. One sufficient bridge would be explicit uniform errors

$$
\sigma_d\ge \frac{\log_2K_d(n)}n-\eta_d(n),\qquad
\eta_d(n)\longrightarrow0,
\tag{NDR.37}
$$

effective in the stated parameters. Another would be a complete effective
lower-certificate hierarchy over the unrestricted templates of §2, with
a proved approximation error. Neither is supplied here. Finite type
computations in §3 compare finite quantities; NCE's sufficient weights
cover all cycles but have no established completeness theorem.

By Corollary 7.4, finite component enumeration cannot be made complete by
uniform subexponential per-fiber repair at the fixed original-block
interface. Lawful changes of variables that retain shared relations and
global certificates are alternative possible mechanisms; all-competitor
coverage and vanishing loss remain required. Finite vocabulary, binary
closure, graph existence and finite LP decidability alone do not establish
those properties.

**Open problem 9.3 (finite memory and the wider programme).** The general
exact $M_1(D)$, the credited unresolved $M_1(3)\in\{3,4\}$, sharp
$\lambda$, and the broader minimal-relations/internal-observer mutual
recovery programme remain open. The exact recovery relation used here is

$$
(E(t),D,p,\text{at most one paid native reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{NDR.38}
$$

The inverse recovers this temporal factor, not the full original source,
an unknown age, hidden history, authentication, or physical space and
time. The unchanged interval is (NDR.9). FMR's exact finite optima and
gluing give computable decreasing upper approximants to $\lambda$.
Effective two-sided convergence, a complete lower hierarchy and
closed-form exactness remain distinct claims, none proved by this volume.
No native noncomputability conclusion follows either.

## 10. Mathematical conventions and cited hypotheses

**Convention 10.1 (source notation and hypotheses).** Repository citations
refer to revision `22f02d429d40d97f7c83a81d0481826ebadeb511`.
In [GenealogicalFiberTransport][D5G], the source is the free ordered magma
on Boolean leaves, with `true` for alpha and `false` for beta, and
`substitution` is the lifted map sending these to beta and
pair(beta,alpha). In [ActualTreeReadoutAcquisition][D5A], addresses are
finite Boolean lists: false means $L$, true means $R$, and
`Reply`/`readout` give all four replies at every finite literal.
Its recognition problem is a different endpoint.
In [NativeDepthPatterns][D5N], `original_present_transport` assumes
`subtree a u = some t`; the fixed actual occurrences in §8 meet precisely
that presence hypothesis. `original_prefix_locality` assumes agreement
of original replies through the requested word length and concludes
all-count reply agreement. Neither hypothesis supplies a subtree input
or a free navigation operation.

The theorem `target_family_minimal_quotient` in
[TargetFamilyMinimalQuotient][D5T] assumes passive factorization of every
target through one readout and gives its joint-kernel quotient. That
zero-later-Read endpoint does not characterize which single native reply
can repair a fiber. The theorem
`compact_observation_factorization` in [CompactObservationFactorization][D5C]
assumes a nonempty compact topological source, finite discrete observation
levels, continuous surjective compatible observation maps whose fibers
form a topological basis, and a continuous finite readout. Its action
conclusion also assumes finitely many continuous actions and a bounded
word window. It supplies finite-level existence, not effective native
acquisition, one-probe memory rate or a lower convergence modulus.

AAR §§12, 13 and 16 already supply the exact all-count factors, fixed-menu
passive codes and native acquisition results. [NBP, Assumption 14.1 and
Theorem 14.4][NBP] supply a different paid common-start two-phase
predecessor interface with a stationary register and a code-only access
cut. Its full-row and terminal-latch hypotheses are not imported as a new
late-target theorem. Neither source physically derives isolation or
authentication.

**Convention 10.2 (attribution of the mathematical ingredients).**
The five-state motif, its paired decoder and its paid-fiber discipline
are credited to NCM §6. The all-joint cap in Lemma 4.3 is a specialization
of NCE Theorem 2.2, whose original rate bound remains credited. FMR
supplies canonicalization, cover attainment, native gluing, harmonic
rounding and regularized limits. MSS supplies the graph existence
theorem. The twice-covered count is a standard entropy projection
inequality, with the exact finite proof included.

Theorems 2.2 and 2.4 give the exact decoder-template and binary-closure
interface; Theorem 3.2 and Proposition 3.3 give its finite type/mass
relations. Theorem 7.2 combines actual-module conditioning, expansion and
shared-label counting to obtain (NDR.29), with the full-family attainment
of Theorem 8.1. These deductions use the cited ingredients with the
hypotheses and boundaries stated in their proofs.

**Convention 10.3 (literature correspondences and applicability).** The
following primary citations specify the hypotheses for the corresponding
relations and the missing hypotheses for their application to the native
task.

| Primary source | Exact correspondence and boundary |
| --- | --- |
| Adam W. Marcus, Daniel A. Spielman and Nikhil Srivastava, *Interlacing Families I: Bipartite Ramanujan Graphs of All Degrees*, Theorems 5.3 and 5.5, [arXiv:1304.4132][MSS] | Existence of a signing with new eigenvalues bounded by $2\sqrt{d-1}$ and iterative bipartite Ramanujan two-lifts. Starting from $K_{4,4}$ gives the exact orders in Lemma 6.1. Its rational cut-test selection is effective; an efficient graph-generation bound is not assumed. |
| F. R. K. Chung, R. L. Graham, P. Frankl and J. B. Shearer, *Some intersection theorems for ordered sets and graphs*, J. Combin. Theory A **43**, 23–37, [DOI:10.1016/0097-3165(86)90019-1][CGFS] | The overlapping-projection entropy principle attributed to Shearer. Lemma 7.1 gives the exact twice-covered finite-alphabet instance, including arbitrary correlations. |
| Mokshay Madiman and Prasad Tetali, *Information Inequalities for Joint Distributions, with Interpretations and Applications*, Proposition I and §IV, [arXiv:0901.0044v2][MT] | For arbitrary jointly distributed discrete variables, joint entropy is at most the sum of subset entropies divided by their minimum covering degrees. Degree two gives exactly the inequality in Lemma 7.1. This is Shearer's lemma; it requires no independence of edge labels after conditioning. |
| Martin Dyer and David Richerby, *An Effective Dichotomy for the Counting Constraint Satisfaction Problem*, finite-domain constraint-language setup, [arXiv:1003.3879v4][DR] | A finite language on a finite domain constrains arbitrarily large finite variable sets. §2 gives the actual native binary language. Finite-instance decidability or a complexity dichotomy is not effective approximation of an all-size regularized optimum. |
| Tomasz Gogacz and Szymon Toruńczyk, *Entropy bounds for conjunctive queries with functional dependencies*, Theorem 1 and Corollary 1, [arXiv:1512.01808v1][GT] | A fixed schema's size exponent is characterized by the almost-entropic cone; submodularity gives an outer relaxation. A native witness gives $H(g_q(X_i)\mid r_a(X_j))=0$ on a common law. Here the schema, donors and length vary while the native maps and alphabets stay fixed. Their variable-database achievability does not prove completeness or a uniform error for this task. |
| Jeroen Zuiddam, *The asymptotic spectrum of graphs and the Shannon capacity*, Theorem 1.1 and Definition 2.1, [arXiv:1807.00169v2][Z] | Duality requires the graph semiring, disjoint union, strong product and cohomomorphism preorder. A native fiber is a constraint relation, not a pair-confusability graph. A cardinality-preserving semiring/product/preorder correspondence and an effectively exhaustive native spectrum remain unproved. |
| David de Boer, Pjotr Buys and Jeroen Zuiddam, *The asymptotic spectrum distance, graph limits, and the Shannon capacity*, §§1–3, [arXiv:2404.16763v2][DBZ] | A distance defined using the full graph spectrum and convergence/continuity results for fraction graphs. An identification of the native task with those graphs and an effective spectrum-distance estimate remain unproved. Compact or dual existence alone supplies no native numerical modulus. |
| Nicolas Charpenay, Maël Le Treust and Aline Roumy, *On the Linearization of Optimal Rates for Independent Zero-Error Source and Channel Problems*, §§II–III, [arXiv:2407.02281v2][CLR] | Specified zero-error source/channel graph products and independence assumptions. Separate attainable marginal optima do not establish joint feasibility for correlated native fibers. The coordinate-type argument in §3 assumes no such product identification. |
| Shmuel Friedland, Per Håkan Lundow and Klas Markström, *The 1-vertex transfer matrix and accurate estimation of channel capacity*, Theorems 2.1 and 4.1, [arXiv:math-ph/0603001v2][FLM] | Transfer estimates use specified lattice constraints and symmetry or a friendly-colour hypothesis. The finite native language imposes no such geometry, bounded window or width. The unbounded donor quantifier is not removed by a finite transfer ansatz. |
| Anna Gál and Peter Bro Miltersen, *The Cell Probe Complexity of Succinct Data Structures*, [BRICS RS-03-44][GM] | Preserved input plus an index gives the systematic-storage analogy. Native probes instead see a grammar-constrained constructor array, and the complete attained code, paid acquisition and all-count targets must be preserved. The systematic bit-probe results are not native rate theorems. |
| Sumegha Garg, Songhua He, Yuanzhi Li, Periklis A. Papakonstantinou and Xin Yang, *Systematic Data Structure Lower Bounds via the Query-with-Sketch Model*, Definition 2.1, Lemma 2.5 and Theorem 1.1, [arXiv:2609.18024v1][GHLPY] | A sketch is supplied before probes of preserved input; their lifting theorem requires quantitative conditional answer min-entropy after every allowed partial assignment, with its stated good-input conditions. $E$ and a native reply match sketch/probe timing, but those entropy premises remain unproved for the native constrained reply array. Separate late targets cannot be replaced by one free vector-output request. |
| Holger Boche and Christian Deppe, *Computability of the Zero-Error capacity with Kolmogorov Oracle*, Theorem 12 and Remark 38, [arXiv:2001.11442v3][BD] | A capacity/Fekete characterization alone is distinct from effective computation. General examples or results about channel families are not a reduction proving noncomputability of this fixed native rate. |
| Theorems 2.2, 2.4, 3.2 and 7.2, and their actual-source realization in §8 | The finite all-competitor carrier and exponential bounded-original-block repair obstruction. Their stated hypotheses and conclusions leave the lower modulus (NDR.37) unresolved. |

## 11. Finite consequences of the native interfaces

**Corollary 11.1 (one-coordinate motif size).** Among the 31 nonempty
subsets of $P$, the maximum size of a one-coordinate jointly admissible
set is four. On the full $P$, none of the 127 words of length at most
six determines the $LL$ factor; in fact no finite word does. The factor
decoders on $B_*$ in Lemma 4.2 give the substitution readouts for both
coordinates, all seven targets and every $k\ge0$.

**Proof.** There are $2^5-1=31$ nonempty subsets. Lemma 4.2 excludes
$P$ itself. On $P\setminus\{u_0\}$ the reply at $RL$ takes the four
distinct values absent, alpha, beta and branch, by (NDR.20). It therefore
determines every target factor on this four-element set. There are
$\sum_{l=0}^6 2^l=127$ words in the stated finite range, all included
in the arbitrary-word exclusion of Lemma 4.2. The all-count assertion
is (NDR.4) applied to that lemma's exact factor decoders. $\square$

**Proposition 11.2 (three-block paired-module relation).** Let the vertices
of a triangle be $0,1,2$, with the cyclic orientation
$0\to1\to2\to0$. Independently assign a label $s_e\in\{0,\ldots,4\}$
to each of its three edges. At each vertex use the four-module form
(NDR.26): put $u_{s_e}$ at port $LL$ for its outgoing edge,
$u_{\tau(s_e)}$ at port $LR$ for its incoming edge, and $u_0$ at each
of the other two ports. The resulting relation in $S_5^3$ has exactly
$125$ tuples and is jointly admissible for all $93=3|W_5|$
coordinate-target pairs. Each of its six nonconstant edge-port $LL$
targets has exactly the opposite endpoint as its possible donor block,
even when all finite native words are allowed.

**Proof.** Each module state recovers its edge label, so the parametrization
is injective and has $5^3=125$ images. Targets above the module frontier
are constantly branch, and targets in either fixed module are constant
factors. In an edge module, use the paired witnesses of Lemma 4.2 at
the corresponding actual port. They are parent words in $W_5$, since
the port has length two and the suffix has length at most two. Thus all
$3(1+2+4+8+16)=93$ parent coordinate-target pairs have witnesses.
For each edge-port $LL$ target, vary that edge label while keeping the
other two fixed. An experiment in an unrelated module is constant under
this variation; an experiment in the target module cannot determine its
$LL$ factor by Lemma 4.2. Every finite word enters at most one module.
The mate's $RL$ reply does determine the factor, so precisely the other
endpoint block can be its donor. $\square$

**Proposition 11.3 (base graph and original-root specialization).** For
$G=K_{4,4}$, the minimum of $|\partial A|/|A|$ over its 162 nonempty
vertex subsets of size at most four is two. At the associated
$N=8,D=8$ original-root interface of Theorem 8.1, all $5^{16}$ edge
assignments yield distinct sources in $\mathcal F_8$. For each one,
the specified reader returns the correct prediction on all 255 permitted
targets and every authentic $k\ge0$, with at most one fresh Read of
length at most eight. The source-blind preparation on every
$t\in\mathcal F_8$ uses exactly 511 Reads and 4097 submitted letters,
with maximum address length nine.

**Proof.** A subset containing $l$ vertices in one bipartition and $r$
in the other, with $a=l+r>0$, has
$|\partial A|=4a-2lr$. Since $lr\le a^2/4$, for $a\le4$ its ratio
is at least $4-a/2\ge2$. Equality holds for $l=r=2$. The number of
subsets is $\binom81+\binom82+\binom83+\binom84=162$.
There are sixteen edges, and $h=3$, so the remaining assertions follow
from Proposition 6.3 and Theorem 8.1 with
$|\mathcal P_8|=\sum_{l=0}^7 2^l=255$,
$2^9-1=511$ and $8\cdot2^9+1=4097$.
The exact sums in that theorem hold for every depth, and its factor
identity (NDR.36) holds for every count. $\square$

[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NCM]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[NBP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[D5G]: ../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[D5A]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[D5N]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5T]: ../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean
[D5C]: ../../../D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.lean
[MSS]: https://arxiv.org/html/1304.4132
[CGFS]: https://doi.org/10.1016/0097-3165(86)90019-1
[MT]: https://arxiv.org/html/0901.0044v2
[DR]: https://arxiv.org/html/1003.3879v4
[GT]: https://arxiv.org/html/1512.01808v1
[Z]: https://arxiv.org/html/1807.00169v2
[DBZ]: https://arxiv.org/html/2404.16763v2
[CLR]: https://arxiv.org/html/2407.02281v2
[FLM]: https://arxiv.org/html/math-ph/0603001v2
[GM]: https://www.brics.dk/RS/03/44/index.html
[GHLPY]: https://arxiv.org/html/2609.18024v1
[BD]: https://arxiv.org/html/2001.11442v3

## 追加锚（本行以下为增补区）

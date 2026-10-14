# Recursive relational observation: native fractional covers and the late-target memory rate

## 1. The unchanged stationary task and its predictive factor

**Convention 1.1 (scope and mathematical suppliers).** This volume concerns
ordinary mathematics for the native operations at public revision
`73671b9d9b6dd4de26089c3699ca0bfcb72f2315`. It is reference input, without
Lean kernel certification. Published text and append anchors are immutable;
extensions belong after the terminal append anchor. The task is exactly
[Late Target One Read Memory, Definitions 1.2–1.4](RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_ONE_READ_MEMORY.md),
abbreviated LTR. Its full-family bounds, initial cases and attained
off-target example are suppliers, rather than new results here. The
numerical sharp rate, general exact finite optimum and broader
minimal-relations programme remain open.

**Definition 1.2 (actual trees, every-word observation and time).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,
\qquad h(\langle x,y\rangle)=1+\max(h(x),h(y)).
$$

Pairing is ordered. Every finite word in $L,R$, including
$\varepsilon$, is a legal original-root literal. Write $r_u(w)$ for
its reply: alpha or beta at a leaf, branch at a pair, and absent
beyond a leaf. Define

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

For each public integer $D\ge1$, retain precisely

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},
\qquad
W_D=\{q:|q|\le D-1\},
\qquad
\mathcal P_D=\{Rq:q\in W_D\}.
\tag{FMR.1}
$$

Thus the family includes all variable shapes. One actual initial source
$t$ remains stationary through preparation and later acquisition.
The iterates $\rho^kt$ specify the prediction target, not updates to
that register. There is no subtree, equality, identity, age, reset,
copying, navigation or free-advice port.

**Assumption 1.3 (complete paid export and late entry).** Preparation is
one deterministic effective procedure with common source-independent
initialization, public $D$ and common installed tables. It does not know
the later request. Every acquired source distinction comes from charged
literal Reads, and preparation terminates on every source. It exports
one finite code $E(t)$. All accessible surviving source dependence is
part of that code, including selectors, control, operands, buffers,
lengths, allocation, handles, counters and accessible timing distinctions.
Any other surviving field is a fixed function of the code and public
data. A separately supplied paid handoff isolates all other preparation
material and supplies lawful reader entry. Earlier transcripts and
acquired descriptions are inaccessible. Isolation, export, entry,
source continuity and authentication are declared services; they are
not inferred physical operations or free erasure.

Only after export is a public source-independent $p\in\mathcal P_D$
supplied. A common deterministic effective reader, given $E(t),D,p$
and the installed tables, makes at most one fresh Read of that same
stationary $t$, at any finite word chosen from those inputs. Zero-Read
branches are permitted. It then exports a final predictor $Z$. For
every subsequently supplied authentic integer $k\ge0$, with no further
Reads, correctness means

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad\text{for every }t\in\mathcal F_D, p\in\mathcal P_D, k\ge0.
\tag{FMR.2}
$$

Neither a supplied $k$ nor a source-dependent request may guide that
one query. Define the unchanged objective

$$
m_D=M_1(D)=\min |E[\mathcal F_D]|.
\tag{FMR.3}
$$

Only this complete attained alphabet is optimized. Preparation cost,
installed codebooks, temporary and post-request workspace, final
predictor size, address length, submitted letters, count representation,
handoff, authentication and physical time are separate resources.

**Convention 1.4 (the reused all-count factor).** Write
$s(q)=\#L(q)+2\#R(q)$ and $e(\alpha)=0,e(\beta)=1$. Use exactly the
factor $\Gamma_q(u)=(b,c)$ of
[Adaptive Acquired Reference Frontier, Definition 12.2, Theorem 12.3 and Proposition 13.3](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md),
abbreviated AAR. At an original branch endpoint it is $(0,0)$. If the
first original leaf along $q$ has label $\ell$ at $a$, with $q=ar$,
then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{FMR.4}
$$

The supplied decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1, k=b-1,\\
\alpha,&c=1, k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{FMR.5}
$$

On attained factors $c=1$ implies $b\ge2$. The supplied theorem gives
$r_{\rho^ku}(q)=\operatorname{Pred}(\Gamma_q(u),k)$ for every $k$.
Conversely the trajectory recovers $b$ as its first branch count and
$c$ from the presence of an alpha stage. Equality of factors is exactly
equality of complete trajectories, not equality of first-leaf descriptors.
For the actual paired source,

$$
\Gamma_{Rq}(\langle\alpha,v\rangle)=\Gamma_q(v),
\qquad r_{\rho^k\langle\alpha,v\rangle}(Rq)=r_{\rho^kv}(q),
\qquad b\le2D.
\tag{FMR.6}
$$

**Source correspondence 1.5 (native carriers and existing endpoints).**
In [GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
`Source` is `FreeMagma Bool` and `substitution` is the magma
homomorphism above; `true` labels alpha and `false` labels beta.
In [ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean),
`Address` is a Boolean list, with false for $L$ and true for $R$;
`Reply` and `readout` give all four replies and all finite legal words.
Its recognition objective is different from (FMR.2).
[NativeDepthPatterns](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean)
supplies `original_present_transport` only at actually present original
subtrees and `original_prefix_locality` for all-count dependence on
the original boundary. AAR §§12, 13 and 16 supply the exact predictive
quotient, known-singleton acquisition and known-menu acquisition.
Their requests are declared before acquisition. The zero-later-Read
full-menu endpoint is already among those suppliers. None is renamed
as a late-request memory theorem.

## 2. Global canonical normalization with every experiment retained

**Definition 2.1 (canonical actual representatives).** Put
$C=\langle\alpha,\alpha\rangle$ and

$$
S_1=\{\alpha,\beta,C\},\qquad
S_{D+1}=\{\alpha,\beta\}\ \sqcup
\{\langle x,y\rangle:x,y\in S_D\},\qquad N_D=|S_D|.
\tag{FMR.7}
$$

All elements are actual trees of height at most $D$. For $h(v)\le D$,
let $\pi_D(v)$ keep every reached constructor through depth $D-1$,
replacing a branch reached at depth $D-1$ by $C$. Thus $\pi_D(v)\in S_D$,
and $\pi_D$ fixes $S_D$. This is AAR Theorem 16.3's canonical
completion for the full prefix menu $W_D$.

**Lemma 2.2 (canonical every-word simulation).** For every such $v$,
every $q\in W_D$ and every finite relative word $w$,

$$
\Gamma_q(\pi_D(v))=\Gamma_q(v),
\tag{FMR.8}
$$

and

$$
r_{\pi_D(v)}(w)=
\begin{cases}
r_v(w),&|w|\le D-1,\\
\alpha,&|w|=D, r_v(w^-)=\mathsf{branch},\\
\mathsf{absent},&|w|=D, r_v(w^-)\ne\mathsf{branch},\\
\mathsf{absent},&|w|>D,
\end{cases}
\tag{FMR.9}
$$

where $w^-$ removes the last letter. Each canonical reply therefore
requires at most one actual Read at a word of $W_D$, or no Read.
For the outer wrapper the replies at $\varepsilon$, $L$, and strict
extensions of $L$ are respectively branch, alpha and absent.

Proof. The completion preserves every constructor on $W_D$, so it
preserves each first blocking leaf and label, or branch endpoint,
needed by (FMR.4). This gives (FMR.8). At depth $D$ its only present
vertices are the added alpha children of cutoff branches. Such a
child is present exactly when its parent at depth $D-1$ was branch.
There are no deeper present vertices. This proves (FMR.9), including
all words beyond the target menu. The outer wrapper cases follow
directly from the native definition. $\square$

**Theorem 2.3 (alphabet-preserving global replacement).** The original
minimum $m_D$ equals the minimum on the canonical actual sources
$\{\langle\alpha,x\rangle:x\in S_D\}$ with later probes restricted
to $Rq$, $q\in W_D$, together with zero Reads. From any original
encoder $E$ one can construct an effective encoder

$$
E^\circ(\langle\alpha,v\rangle)
 =E(\langle\alpha,\pi_D(v)\rangle),
\qquad
|E^\circ[\mathcal F_D]|\le |E[\mathcal F_D]|.
\tag{FMR.10}
$$

It acquires its source dependence using at most

$$
T_D\le2^D-1,\qquad Q_D\le D,
\qquad A_D\le(D-1)2^D+1
\tag{FMR.11}
$$

actual preparation Reads, peak submitted length and submitted letters,
respectively. These are sufficient bounds, not preparation optima.

Proof. Actually submit every $Rq$, $q\in W_D$, on the stationary
source, including words that return absent. The acquired finite table
determines $\pi_D(v)$. A common installed table contains the original
encoder's output on each canonical actual source. It can be generated
effectively by simulating its terminating preparation on those finitely
many explicit trees, computing their replies locally. This installation
uses no unknown actual source and is a separate resource. Output only
the selected complete code. The isolation assumption removes access to
the acquired table, selection workspace and every other distinction.
Canonical representatives belong to the original family, proving the
range inequality.

Given a late request, simulate the original reader on its canonical
source. Its chosen arbitrary literal is either an outer constant,
a preserved boundary word, an immediate exit, or a strict extension
of an exit. Lemma 2.2 supplies its exact reply using at most one actual
boundary Read. The word choice and translation use only the complete
code, $D,p$ and common tables; no $k$ is available. A zero-Read original
branch remains a zero-Read branch. The original resulting predictor
has the canonical trajectory, and (FMR.8) makes that the actual required
trajectory for every subsequent $k$.

Conversely, a canonical reader with boundary probes works on the
actual family after that same acquisition: boundary replies agree
and all target factors agree. The two optimum inequalities follow.
There are $2^D-1$ submitted words, maximum length $D$, and
$\sum_{j=0}^{D-1}(j+1)2^j=(D-1)2^D+1$ submitted letters. $\square$

The theorem replaces the whole encoder by $E\circ\pi_D$. It does not
assert that a fixed correlated fiber is invariant under completion,
that its child projections are legal fibers, or that queries can be
restricted to prefixes of the selected target. All off-target words
inside $W_D$ remain available.

**Definition 2.4 (explicit native admissible fibers).** Let
$g_q(x)=\Gamma_q(x)$ and $R_a(x)=r_x(a)$ on $S_D$, for $q,a\in W_D$.
Include a formal constant experiment $\bot$, representing zero Reads.
A nonempty $H\subseteq S_D$ is admissible when

$$
\forall q\in W_D\ \exists a\in W_D\cup\{\bot\}\ 
\forall x,y\in H,\quad
R_a(x)=R_a(y)\ \Longrightarrow\ g_q(x)=g_q(y).
\tag{FMR.12}
$$

For $a=\bot$ the reply is constant. Let $\mathcal H_D$ be all these
admissible subsets. This is an explicit finite family defined solely
by native constructor replies and (FMR.4); it does not quantify over
unknown encoders. It is downward closed on nonempty subsets, and every
singleton belongs to it. The chosen experiment may depend on both
$H$ and $q$, and may be off-target.

**Theorem 2.5 (exact native integral-cover correspondence).** The minimum
number of members of $\mathcal H_D$ covering $S_D$ is $m_D$. Every
such cover has an effective actual preparation obeying (FMR.11) and
one common all-target, all-count reader.

Proof. Restrict any original complete code to the canonical actual
sources. Its fibers retain arbitrary correlations. For a fixed code
and request the decision to stop or the one submitted word is fixed.
Equal replies give identical final predictors and hence identical
factors. Lemma 2.2 replaces every arbitrary word by one boundary
experiment or a constant, so each restricted fiber satisfies (FMR.12).
They cover $S_D$ with at most the attained original alphabet size.

Conversely, order a cover and assign each $x$ to its first containing
member. Its actual fibers are subsets of admissible members. Install
one witnessing experiment for every cover member and target, and its
reply-to-factor table. Acquire $\pi_D(v)$ by (FMR.11) and export only
the first-containing-member index. After the request, perform its
prescribed actual boundary Read, or zero Reads, and output the factor.
Equations (FMR.5) and (FMR.8) give every required $k$. Thus the cover
becomes a paid deterministic complete code, without a free color
oracle. A minimum cover attains all its indices: an unused member
could be deleted. Finite enumeration of subsets, experiments and
covers makes these optima uniformly effective in public $D$; it
asserts no useful bound on installation or local work. $\square$

## 3. Native pairing and existence of the normalized rate

**Lemma 3.1 (literal interpretation at an actual occurrence).** Suppose
a subtree $u$ is actually present at the known original-root address
$a$. A constituent preparation or reader designed for the artificial
wrapper $\langle\alpha,u\rangle$ can be simulated as follows:

$$
\begin{array}{c|c}
\text{constituent literal}&\text{simulation}\\ \hline
\varepsilon&\mathsf{branch}\text{ by public computation}\\
L&\alpha\text{ by public computation}\\
Lw, w\ne\varepsilon&\mathsf{absent}\text{ by public computation}\\
Rw&\text{one actual literal Read at }aw.
\end{array}
\tag{FMR.13}
$$

The same interpretation applies to preparation calls and to a later
one-Read call. It does not change the actual source or give a subtree
as an operational input.

Proof. These are precisely the wrapper's four exhaustive literal cases.
All replies that depend on $u$ are obtained from the actual source at
the full word $aw$. Presence of the occurrence follows from previously
acquired branch ancestors or from a fixed scaffold promise, never from
a free navigation action. For temporal targets inside this occurrence,
pairing homomorphism, iterated along its present ancestors, transports
$\rho^ku$ there for every $k$. No transport from an absent address is
used. $\square$

**Theorem 3.2 (whole-family upper gluing).** For every $D\ge1$,

$$
m_{D+1}\le m_D^2+1.
\tag{FMR.14}
$$

The construction covers leaf roots and branch roots of every allowed
shape and has an effective paid preparation.

Proof. Actually Read $R$. If $v$ is a leaf, export one common leaf
marker for both labels. After any request, Read $R$ once and use its
label and the residual target in (FMR.4). Its label is not retained.
If $v=\langle x,y\rangle$, export the ordered pair of complete
attaining depth-$D$ constituent codes for $x$ and $y$, in an alphabet
disjoint from that marker. Lemma 3.1 implements constituent source
calls at actual prefixes $RL$ and $RR$. Their source-dependent
selectors and other surviving fields are already in their complete
codes. The parent branch marker and the ordered pair are completely
specified by the exported name. All $m_D^2$ pairs are jointly
attained because $x,y$ range independently over actual height-bounded
trees in this upper construction.

For a branch code and $p=R$, the trajectory is constantly branch,
using zero Reads. For $p=Rsq$, $s\in\{L,R\}$, the selected child
reader receives its code and target $Rq\in\mathcal P_D$. Translate
its one literal by Lemma 3.1. Constant wrapper probes need no actual
Read; all others need one. Transport at the actual child gives
correctness simultaneously for every $k$. Different potential targets
select their own single experiment; an execution receives just one.
The actual preparation can instead scan the full canonical boundary
at depth $D+1$ and compute this same code from the acquired data,
giving (FMR.11) with that depth. Thus no constituent colors are
supplied without acquisition. $\square$

**Theorem 3.3 (existence of the original full-family rate).** The limit

$$
\lambda=\lim_{D\to\infty}2^{-D}\log_2m_D
\tag{FMR.15}
$$

exists. More precisely $2^{-D}\log_2(m_D+1)$ is nonincreasing and
has the same limit. Fixed-width naming $\lceil\log_2m_D\rceil$
has the same normalized limit.

Proof. Since $m_D\ge1$, (FMR.14) gives

$$
m_{D+1}+1\le m_D^2+2\le(m_D+1)^2.
$$

The shifted normalized logarithms therefore decrease and are bounded
below by zero. Their difference from the requested sequence is at
most $2^{-D}$. The fixed-width rounding difference is also at most
$2^{-D}$. These observations prove all assertions. The composition
hypothesis is supplied by the actual native construction in Theorem
3.2, not by an assumed graph product or a reverse product inequality.
$\square$

## 4. Fractional native covers, all-competitor duals and vanishing loss

**Definition 4.1 (the finite native fractional cover).** Define the
rational finite linear program

$$
z_D=\min\left\{
\sum_{H\in\mathcal H_D}w_H:
w_H\ge0,\quad
\sum_{H\ni x}w_H\ge1\quad(x\in S_D)
\right\}.
\tag{FMR.16}
$$

Its dual is

$$
z_D=\max\left\{
\sum_{x\in S_D}y_x:
y_x\ge0,\quad
\sum_{x\in H}y_x\le1\quad(H\in\mathcal H_D)
\right\}.
\tag{FMR.17}
$$

Both have attained rational optima by finite linear programming
duality: singleton covers make the primal feasible, and its objective
can be restricted to at most $N_D$; singleton dual constraints put
each $y_x$ in $[0,1]$. Their finite rational constraint matrices
therefore admit optimal rational vertices. No source distribution is
assumed by these nonnegative dual weights.

**Proposition 4.2 (what every dual certifies).** For any dual-feasible
$y$ and any correct original preparation and one-Read reader,

$$
|E[\mathcal F_D]|\ge\sum_{x\in S_D}y_x.
\tag{FMR.18}
$$

Proof. On the canonical actual sources, every nonempty restricted
code fiber is in $\mathcal H_D$ by Theorem 2.5. Its dual mass is at
most one. These same fibers partition $S_D$, so their number is at
least the total mass. Their number is no larger than the complete
attained original alphabet. The argument permits arbitrary correlations,
off-target or arbitrarily long words, and zero-Read branches, since
their native reduction was proved before forming $\mathcal H_D$.
$\square$

**Lemma 4.3 (fractional native gluing).** For every $D\ge1$,

$$
z_{D+1}\le z_D^2+1.
\tag{FMR.19}
$$

Proof. For $H,J\in\mathcal H_D$ the actual branch set
$\langle H,J\rangle=\{\langle x,y\rangle:x\in H,y\in J\}$
is admissible in $S_{D+1}$. Its root target is constant branch;
a target $sq$ uses the $s$-child's witnessing experiment, with the
literal prefix $s$ attached. A constant witness remains zero-Read.
These are original-root literals after the outer $R$ is attached.
The two-leaf set $\{\alpha,\beta\}$ is also admissible: Read its root
once and compute every requested factor from its label.

Given a fractional depth-$D$ cover, assign the branch set
$\langle H,J\rangle$ weight $w_Hw_J$, adding weights if sets coincide,
and the two-leaf set weight one. A branch $\langle x,y\rangle$ receives
coverage $(\sum_{H\ni x}w_H)(\sum_{J\ni y}w_J)\ge1$, and each leaf
receives coverage one. The total weight is $z_D^2+1$ for an optimal
cover. This constructs allowable fibers; it imposes no product
restriction on competing fibers. $\square$

**Lemma 4.4 (constructive integral comparison).** Let
$H_N=\sum_{j=1}^N1/j$. Then

$$
z_D\le m_D\le H_{N_D}z_D,
\qquad
N_1=3,\quad N_{D+1}=2+N_D^2.
\tag{FMR.20}
$$

For any supplied rational fractional cover of weight $x$, the same
argument gives an effectively acquired code with at most $H_{N_D}x$
attained values, interpreted as an integer bound.

Proof. An integral cover is a fractional cover. For the reverse
comparison enumerate admissible sets and repeatedly choose a set
containing the most currently uncovered vertices, resolving ties by
a fixed public order. Charge each of its $r$ newly covered vertices
$1/r$. Total charge is the number of chosen sets.

Fix an admissible set $J$. If $j$ of its vertices remain uncovered
when a greedy choice is made, that choice covers at least $j$
vertices, since choosing $J$ was available. If it covers $k$ vertices
of $J$ at that step, their total charge is at most $k/j$, which is
at most $\sum_{i=j-k+1}^j1/i$. Summing over the steps gives total
charge on $J$ at most $H_{|J|}\le H_{N_D}$. For any fractional
cover, multiply this inequality by each weight and sum. Each vertex
has total covering weight at least one, so the total charge is at
most $H_{N_D}\sum_Jw_J$.

Thus greedy constructs the stated cover. Theorem 2.5 implements its
first-containing-set index by paid actual boundary acquisition and
the common native reader. All enumeration and greedy choices depend
only on public finite tables, not on the unknown actual source.
$\square$

**Theorem 4.5 (the exact fractional structural rate).** For the unchanged
full-family task,

$$
\boxed{\displaystyle
\lambda=\inf_{D\ge1}2^{-D}\log_2(z_D+1).}
\tag{FMR.21}
$$

The displayed upper endpoints are nonincreasing. Moreover

$$
0\le2^{-D}(\log_2m_D-\log_2z_D)
\le2^{-D}\log_2\bigl(1+(\ln2)2^D\bigr)
\longrightarrow0.
\tag{FMR.22}
$$

Proof. The recurrence for $N_D$ implies
$N_{D+1}+1=N_D^2+3\le(N_D+1)^2$, so
$N_D+1\le2^{2^D}$. Since $H_N\le1+\ln N$, (FMR.20) gives
(FMR.22). Its right side tends to zero: its numerator grows at
most linearly in $D$, while its denominator is $2^D$.
Consequently $2^{-D}\log_2z_D$ has the same limit as
$2^{-D}\log_2m_D$. Also $z_D\ge1$, so shifting $z_D$ by one
changes the normalized logarithm by at most $2^{-D}$.
Finally (FMR.19) gives
$z_{D+1}+1\le z_D^2+2\le(z_D+1)^2$.
Thus the shifted fractional endpoints decrease to $\lambda$, proving
their infimum formula. $\square$

The characterization uses native reply kernels, actual canonical
sources, effective paid attainment, proved gluing and a vanishing
normalized integrality loss. Generic partition enumeration alone
does not supply these correspondences. At a fixed depth (FMR.17)
is an all-competitor lower certificate for $m_D$. Its normalized
value is not automatically a lower bound for $\lambda$. Equation
(FMR.21) supplies upper approximations, without a certified numerical
convergence modulus or a shrinking computable two-sided interval.

## 5. An exact fractional seed and a strictly smaller constructive upper rate

**Theorem 5.1 (the depth-two native fractional value).** One has

$$
z_1=1,\qquad z_2=\frac{25}{17}.
\tag{FMR.23}
$$

To describe the depth-two certificate, let $A=\alpha$, $B=\beta$,
$C=\langle\alpha,\alpha\rangle$, and let
$\mathcal G=\{g_{xy}=\langle x,y\rangle:x,y\in\{A,B,C\}\}$.
The maximal admissible subsets of $S_2=\{\alpha,\beta\}\sqcup\mathcal G$
are exactly

$$
H_\alpha=\{\alpha\}\cup\mathcal G,
\qquad H_\beta=\{\beta\}\cup\mathcal G,
\qquad T_{xy}=\{\alpha,\beta,g_{xy}\}\quad(x,y\in\{A,B,C\}).
\tag{FMR.24}
$$

Proof. For depth one a root Read determines every root factor, so
the entire $S_1$ is admissible and $z_1=1$. At depth two put
$\gamma(A)=(2,1)$, $\gamma(B)=(1,0)$, $\gamma(C)=(0,0)$.
The nonroot target factors are

$$
\begin{array}{c|cc}
u&\Gamma_L(u)&\Gamma_R(u)\\ \hline
\alpha&(3,0)&(4,1)\\
\beta &(2,0)&(3,1)\\
g_{xy}&\gamma(x)&\gamma(y).
\end{array}
\tag{FMR.25}
$$

Within each column the two root-leaf factors and the three possible
child factors are distinct. On $H_\alpha$ or $H_\beta$, a child-target
Read at that child returns absent exactly on the unique possible
root leaf; its label is fixed by the cover member. Any other reply
is the target's own constructor. A root target uses a root Read.
On $T_{xy}$ a root Read distinguishes all three possible trees, so
all targets are decodable.

Conversely suppose an admissible set contains both root leaves.
At either child target their factors differ, but every nonroot
experiment returns absent on both. Hence that target's witness
must be the root experiment. All branch members receive its same
branch reply, and must therefore agree in their left target factors
and in their right target factors. The injectivity of $\gamma$ on
$\{A,B,C\}$ permits at most one $g_{xy}$. A set not containing both
leaves is contained in $H_\alpha$ or $H_\beta$. This proves the
maximal-set classification; Lemma 2.2 already covers every longer
native experiment.

Give $H_\alpha,H_\beta$ weight $8/17$ each and all nine $T_{xy}$
weight $1/17$ each. Every leaf has coverage $(8+9)/17=1$ and
every branch has coverage $(8+8+1)/17=1$. Total primal weight is
$25/17$. For the dual, give each root leaf weight $8/17$ and
each branch weight $1/17$. Each of the eleven maximal sets has
mass one, and hence all admissible sets have mass at most one.
The dual total is also $25/17$, proving equality. $\square$

**Theorem 5.2 (paid full-family construction from the fractional seed).**
Define positive rational numbers by

$$
x_2=25/17,\qquad x_{D+1}=x_D^2+1\quad(D\ge2).
\tag{FMR.26}
$$

For every $D\ge2$ there is an effective whole-family preparation
and common reader satisfying the original contract, with

$$
m_D\le H_{N_D}x_D.
\tag{FMR.27}
$$

These codes obey (FMR.11), and their late submitted word has length
at most $D$. Consequently

$$
\frac{\log_2(7/5)}4\le\lambda
\le L_{\mathrm{seed}}
:=\lim_{D\to\infty}2^{-D}\log_2x_D
<0.216605159<\frac14.
\tag{FMR.28}
$$

The left inequality and the former upper $1/4$ are reused from LTR;
the strict smaller upper comes from the present construction.

Proof. Start with the eleven rationally weighted native sets of
Theorem 5.1. Iteratively use Lemma 4.3, keeping their explicit
product sets, the two-leaf set and their rational weights. This
gives a finite admissible fractional cover of weight $x_D$ at every
depth. Lemma 4.4 rounds it deterministically and Theorem 2.5 acquires
the resulting complete code on every actual source. Boundary probes
have original-root length at most $D$ and need at most one Read.
Neither the fractional weights nor codebook installation provide
source dependence for free.

For the scalar recurrence,

$$
2^{-D-1}\log_2x_{D+1}-2^{-D}\log_2x_D
=2^{-D-1}\log_2(1+x_D^{-2}).
\tag{FMR.29}
$$

The increments are nonnegative and have a convergent geometric
majorant, so $L_{\mathrm{seed}}$ exists. Alternatively the shifted
sequence $2^{-D}\log_2(x_D+1)$ decreases to that same limit.
The harmonic term in (FMR.27) has vanishing normalized logarithm
by (FMR.22), giving $\lambda\le L_{\mathrm{seed}}$.
LTR Theorem 4.4 gives, on one simultaneously realized actual family
and against every complete code and arbitrary one-Read reader,

$$
m_D\ge\left\lceil(7/5)^{2^{D-2}}\right\rceil\quad(D\ge2).
\tag{FMR.30}
$$

Taking the limit supplies the lower bound in (FMR.28); no weaker
gadget bound is substituted.

For an explicit strict upper certificate, the rational recurrence gives

$$
x_7=\frac{525485427082016387838879317076050951153210066522}
{2367911594760467245844106297320951247361},
\qquad
L_{\mathrm{seed}}\le\frac{\log_2(x_7+1)}{128}.
\tag{FMR.31}
$$

Here is a rational way to certify the decimal inequality, avoiding
a floating-point premise. For $0\le z<1$ put

$$
S_m(z)=2\sum_{j=0}^{m-1}\frac{z^{2j+1}}{2j+1},
\qquad
R_m(z)=\frac{2z^{2m+1}}{(2m+1)(1-z^2)}.
\tag{FMR.32}
$$

The power series obtained by integrating
$2/(1-z^2)=2\sum_{j\ge0}z^{2j}$ gives

$$
S_m(z)\le\ln\frac{1+z}{1-z}\le S_m(z)+R_m(z).
\tag{FMR.33}
$$

The remainder bound follows by replacing every later denominator
by $2m+1$ and summing the geometric series. Set
$u=(x_7+1)/2^{27}$, so $1<u<2$, and $z=(u-1)/(u+1)$.
Substitution into the following entirely rational inequality gives

$$
\frac1{128}\left(27+
\frac{S_{16}(z)+R_{16}(z)}{S_{16}(1/3)}\right)
<\frac{216605159}{10^9}.
\tag{FMR.34}
$$

All numbers in (FMR.34) are given rationally in (FMR.31)–(FMR.32),
so it can also be verified by cross-multiplication of positive
integers. Since the numerator bounds $\ln u$ above and the
denominator bounds $\ln2$ below, (FMR.33) proves the strict bound
claimed in (FMR.28). This finite rational certificate only evaluates
the upper construction; it is not an optimality certificate for
$\lambda$. $\square$

**Source correspondence 5.3 (exact initial cases and different scales).**
LTR Theorem 5.1 gives $m_1=1,m_2=2$, and Corollary 6.4 gives
$3\le m_3\le4$. In particular $z_2=25/17<m_2$: fractional
covering is not an exact finite integral optimum. For $D=1$ the
attaining constant export uses zero preparation Reads, and the sole
late target $R$ is answered by one Read at $R$. Branch roots have
the constant branch trajectory, and the two leaf roots have their
distinct supplied root trajectories. Formula (FMR.28) improves an
alphabet-rate coefficient, rather than merely restating
$\log_2m_D=\Theta(2^D)$ or declaring the exact rate evaluated.

## 6. Joint blocks that preserve arbitrary retained correlations

**Definition 6.1 (natural ownership of experiments, without independent
codes).** For fixed $d\ge1$ and $n\ge1$, the joint universe is $S_d^n$.
Its targets and experiments are

$$
F_{i,q}(x)=\Gamma_q(x_i),\qquad
R_{j,w}(x)=r_{x_j}(w),
\quad i,j\in\{1,\ldots,n\},\quad q,w\in W_d,
\tag{FMR.35}
$$

together with a constant experiment $\bot$. A nonempty
$B\subseteq S_d^n$ is jointly admissible if, for every $(i,q)$,
some single $(j,w)$ or $\bot$ has

$$
\forall x,y\in B,\quad
R_{j,w}(x)=R_{j,w}(y)
\ \Longrightarrow\ F_{i,q}(x)=F_{i,q}(y).
\tag{FMR.36}
$$

The index $j$ need not equal $i$, and the set $B$ need not be a
product. Let $K_d(n)$ be the minimum number of such sets covering
$S_d^n$, and set $K_d(0)=1$.

The coordinate notation does not supply several free source ports.
When actual blocks occur at public prefix-free original addresses
$Ra_1,\ldots,Ra_n$ of one stationary tree, (FMR.35) is implemented
by the single original-root literal $Ra_jw$. A virtual artificial
wrapper is handled by Lemma 3.1. The tuple is a mathematical
description of jointly realized actual blocks, not a copying action.

**Lemma 6.2 (native meaning and effective attainment of $K_d(n)$).**
$K_d(n)$ is the minimum complete attained code alphabet for the
joint block task, and $K_d(1)=m_d$. The same statement holds if
arbitrary finite words within a block are allowed.

Proof. On a fixed complete code fiber and target, the sole chosen
experiment is fixed. Equality of its replies must imply equality
of the required factor, exactly (FMR.36). Conversely a cover can
be disjointed by first membership; install one witness experiment
and its reply decoder for every cover member and target. This is
the same native table argument as Theorem 2.5, now retaining all
coordinates of each joint fiber. Lemma 2.2 eliminates arbitrary
long block words through at most one boundary experiment in that
same block. It does not move a query into the target block.

For actual attainment, acquire every block's canonical boundary by
actual words $Ra_iw$, $w\in W_d$, compute the tuple and export its
one joint cover index. All source dependence is paid and isolated
as in Assumption 1.3. If every $|a_i|\le H$, this takes at most

$$
\begin{aligned}
T&\le n(2^d-1),\qquad Q\le H+d,\\
A&\le n\bigl((H+1)(2^d-1)+(d-2)2^d+2\bigr).
\end{aligned}
\tag{FMR.37}
$$

Indeed, the prefix contributes at most $H+1$ letters per call,
and the suffix lengths sum to
$\sum_{j=0}^{d-1}j2^j=(d-2)2^d+2$. The same literal lengths
bound the late Read. For one block Theorems 2.3 and 2.5 identify
the optimum with $m_d$. $\square$

**Theorem 6.3 (native joint gluing, restriction and full-family cutting).**
For all positive $d,n,m$ and all $h\ge0$,

$$
K_d(n+m)\le K_d(n)K_d(m),
\qquad K_d(2n)\le K_{d+1}(n).
\tag{FMR.38}
$$

Let $U_0=1$ and $U_{h+1}=1+U_h^2$. Then

$$
\boxed{\quad
K_d(2^h)\le m_{d+h}\le U_hK_d(2^h).
\quad}
\tag{FMR.39}
$$

Every upper in these statements has a paid common-start actual
preparation and a common all-target, all-count reader.

Proof of concatenation. Export the ordered pair of attaining complete
codes for the two coordinate groups. A request belongs to one group,
and invokes only that group's one-Read reader. Its query may be
off-target within that group. Products of its admissible cover
members are therefore admissible for the joint task. Actual
preparation Reads at the given occurrences acquire both codes;
there is no assumption that competing codes factor.

Proof of restriction. In every depth-$(d+1)$ coordinate restrict
the actual tree to $\langle x_{2i-1},x_{2i}\rangle$ with
$x_j\in S_d$ independently and simultaneously. Restrict the
original complete code to this actual slice, without changing any
fiber. Its root queries are constant branch; any nonempty boundary
query enters exactly one child, and becomes that child's literal.
A child target $q\in W_d$ is the parent target $Lq$ or $Rq$ in
$W_{d+1}$. Thus every restricted joint fiber satisfies (FMR.36)
on all $2n$ children. No projection of a fiber onto one child
is asserted. This proves the second inequality in (FMR.38).

Proof of the full-family lower. In the actual $v$ fix a perfect
binary scaffold of height $h$, and fill its $2^h$ frontier positions
with all tuples from $S_d^{2^h}$. These simultaneous trees have
height at most $d+h$, hence belong to the original family after
the outer pairing. A normalized full-family query either ends
strictly above the frontier and has constant branch reply, or
enters one block with a suffix in $W_d$. Arbitrary longer words
are already covered by Theorem 2.3 and Lemma 2.2. Every block
target becomes a permitted original target $Raq$. Restricting
the same complete code and reader therefore gives a joint-block
competitor on this one actual slice. Its alphabet is at least
$K_d(2^h)$.

Proof of the full-family upper. For arbitrary variable-shaped $v$,
retain its unlabelled top shape through the first $h$ levels. A
leaf encountered before depth $h$ contributes one shape, regardless
of its label; a branch contributes an ordered pair of shallower
shapes. The shape count is exactly $U_h$. This information locates
all shallow leaves and all actual slots at depth $h$, but retains
no shallow leaf labels. Order all $2^h$ potential depth-$h$ slots.
At an actual slot insert the canonical $S_d$ representative of
its subtree; at a slot blocked by an earlier leaf insert the
public dummy tree alpha. Retain the unlabelled shape and one
attaining joint $K_d(2^h)$ code for this entire tuple.

After a target is supplied, there are three cases. If it ends
at a branch strictly above the cut, its trajectory is constantly
branch. If it meets a shallow leaf, the retained shape locates
that leaf; one actual Read at its original-root address gives
the label, and (FMR.4) gives the target factor even if the target
was initially absent. Otherwise it enters an actual depth-$h$
slot, and the reader invokes the joint-block rule for that slot
and residual target. That rule may query a different slot. If
the queried slot is actual, translate its boundary probe to its
full original-root literal. If it is dummy, compute alpha at
its root and absent at every nonempty word, using no actual Read.
The retained top shape determines which case applies. A dummy
does not supply a source-bearing reply or a second experiment.
The total is still at most one actual Read.

All branches use only the complete exported pair, public data and
the late target. Acquire the full depth-$(d+h)$ canonical boundary
once and compute this pair from its actual replies. This obeys
(FMR.11); actual slots and shallow leaves are not inferred from
an inaccessible transcript after handoff. Equations (FMR.4)–(FMR.6)
prove correctness for every subsequent $k$. This covers all leaf
roots, branch roots and degenerate cut shapes, and proves (FMR.39).
$\square$

**Theorem 6.4 (joint-block rate and geometric depth error).** The limits

$$
\sigma_d=\lim_{n\to\infty}\frac{\log_2K_d(n)}n
=\inf_{n\ge1}\frac{\log_2K_d(n)}n,
\qquad
\phi=\lim_{h\to\infty}2^{-h}\log_2U_h
\tag{FMR.40}
$$

exist, with $0\le\phi\le1$. For the unchanged original rate,

$$
\boxed{\displaystyle
\lambda=\sup_{d\ge1}\frac{\sigma_d}{2^d},\qquad
0\le\lambda-\frac{\sigma_d}{2^d}\le\frac\phi{2^d}.}
\tag{FMR.41}
$$

The lower structural endpoints $2^{-d}\sigma_d$ are nondecreasing.

Proof. The first native inequality in (FMR.38) makes
$a_n=\log_2K_d(n)$ subadditive. For a fixed positive $m$ write
$n=jm+r$, $0\le r<m$, and use $a_n\le ja_m+a_r$.
Dividing by $n$ gives $\limsup a_n/n\le a_m/m$.
Taking the infimum over $m$, while every $a_n/n$ is at least
that infimum, proves the first limit and its equality to the
infimum. This proves the relevant subadditive limit directly
after deriving its native hypothesis.

For $U_h$, normalized logarithms increase, because
$U_{h+1}\ge U_h^2$. They are bounded above by one, since induction
using $U_{h+1}\le2U_h^2$ gives
$U_h\le2^{2^h-1}$. Thus $\phi$ exists. The exact increment is
$2^{-h-1}\log_2(1+U_h^{-2})$, so the tail after $h=H$ is at most
$2^{-H}\log_2(1+U_H^{-2})$.

Take logarithms of (FMR.39), divide by $2^{d+h}$ and let
$h\to\infty$. The middle term tends to $\lambda$ by Theorem
3.3; the other terms converge by (FMR.40), even along block
lengths $2^h$. Therefore

$$
\frac{\sigma_d}{2^d}\le\lambda
\le\frac{\sigma_d+\phi}{2^d}.
\tag{FMR.42}
$$

The restriction $K_d(2n)\le K_{d+1}(n)$, divided logarithmically
by $n$ and sent to the limit, gives $2\sigma_d\le\sigma_{d+1}$.
The endpoints increase, and (FMR.42) makes their gap from
$\lambda$ tend to zero. This proves (FMR.41). $\square$

The characterization preserves arbitrary joint retained-code fibers.
It does not identify $\sigma_d$ with $\log_2z_d$: product fractional
covers give $\sigma_d\le\log_2z_d$, but correlated joint fibers
are additional legal competitors. Indeed, a product of admissible
single-block sets is jointly admissible by querying the target's
own coordinate. Products of their fractional weights cover $S_d^n$
with weight $z_d^n$. The greedy argument on $N_d^n$ vertices gives
$K_d(n)\le H_{N_d^n}z_d^n$; since
$n^{-1}\log_2H_{N_d^n}\to0$, the asserted inequality follows.
In particular

$$
\lambda\le2^{-d}\left(\phi+
\frac{\log_2K_d(n)}n\right)
\tag{FMR.43}
$$

is a valid finite-block upper bound. A finite $K_d(n)$ is an upper
bound for the infimum $\sigma_d$, not its lower certificate.
The geometric error in (FMR.41) concerns a regularized endpoint;
it does not by itself give a computable shrinking numerical interval.

## 7. A published correlated fiber and the transformations it excludes

**Source correspondence 7.1 (the attained off-target supplier).** Reuse
LTR Theorem 7.1 with

$$
\begin{aligned}
(x_0,x_1,x_2,x_3)&=(\alpha,\beta,
 \langle\alpha,\alpha\rangle,\langle\beta,\alpha\rangle),\\
(y_0,y_1,y_2,y_3)&=(\alpha,\langle\alpha,\alpha\rangle,
 \langle\beta,\alpha\rangle,
 \langle\langle\alpha,\alpha\rangle,\alpha\rangle),\\
t_i&=\langle\alpha,\langle x_i,y_i\rangle\rangle\in\mathcal F_3.
\end{aligned}
\tag{FMR.44}
$$

That theorem supplies a paid whole-family encoder with exactly these
four sources as one attained fiber. Their $RRL$ replies are absent,
alpha, beta and branch, respectively, so this one query identifies
the row and serves every permitted target and every subsequent $k$.
At $p=RLL$ their factors are the four distinct values
$(3,0),(2,0),(2,1),(1,0)$. Every prefix of that target merges
two distinct factors. These facts and whole-family attainment are
reused; they are not counted as independent new constructions.

**Corollary 7.2 (same-fiber child projection is invalid).** A jointly
admissible branch fiber need not have an admissible child projection.
An ordinary incompatibility graph on pairs of canonical sources
also cannot characterize native admissibility.

Proof. Project (FMR.44) onto the left child set
$X=\{x_0,x_1,x_2,x_3\}\subset S_2$. Its target $L$ has the same
four distinct factors. Its exhaustive nonconstant native experiments
are

$$
\begin{array}{c|cccc}
\varepsilon&\alpha&\beta&\mathsf{branch}&\mathsf{branch}\\
L&\mathsf{absent}&\mathsf{absent}&\alpha&\beta\\
R&\mathsf{absent}&\mathsf{absent}&\alpha&\alpha.
\end{array}
\tag{FMR.45}
$$

All words of length at least two are absent. None of these experiments
separates the four factors, so $X$ is not admissible. The parent
fiber is admissible by the published off-target query.

For the graph assertion, any two distinct canonical representatives
differ at some boundary constructor: the full $W_D$ reply table
uniquely determines its $S_D$ representative. A Read at a differing
word distinguishes the two sources, and therefore suffices for
every selected target on that two-element set. Thus all pairs are
admissible, whereas the four-element $X$ is not. Pairwise
incompatibility gives an edgeless graph and loses this higher-arity
obstruction. $\square$

The allowed transformations have precise scopes. Global normalization
in Theorem 2.3 changes the whole encoder with no alphabet increase.
Restriction in Theorem 6.3 keeps actual correlated fibers on a jointly
realized slice and interprets every legal query there. Upper gluing
constructs particular product fibers without constraining competitors.
None of these statements authorizes replacing an existing joint fiber
by independent child codes or replacing its query by a target prefix.

**Source correspondence 7.3 (a retained predictive collision).** AAR
Proposition 13.3 supplies another necessary distinction: at $p=RLL$,
$\langle\alpha,\beta\rangle$ and
$\langle\alpha,\langle\alpha,\alpha\rangle\rangle$ have different
blocking positions but the same factor $(3,0)$. All definitions here
use equality of $\Gamma$, rather than identifying it with the first
leaf descriptor. The canonical normalization preserves the boundary
needed to simulate experiments; it need not be the minimal passive
predictive quotient.

## 8. Resource bounds, primary correspondence and remaining recovery

**Proposition 8.1 (resource meaning of the constructions).** Every
finite cover code, fractional-rounding code and whole-family
joint-block code above can use the actual acquisition bounds
(FMR.11). Its retained source-dependent fields can be represented by
one fixed-width name for its complete attained alphabet. A late
Read, when needed, has length at most $D$ and submits at most $D$
letters. The final predictor may be the attained pair $(b,c)$ with
$0\le b\le2D$, $c\in\{0,1\}$.

Proof. In each case the code is an effective function of the actual
canonical boundary, acquired by the fixed literal scan. Use fixed
public ordering, names and output extent. All live fields at export
are the name and public functions of it; the paid service isolates
the boundary table, enumeration state, reply buffers and all other
preparation dependence. The post-request table computes its selected
boundary word solely from that name and the target. After its actual
reply, (FMR.12) or (FMR.36) determines the factor, and (FMR.5)
answers all subsequent authentic counts. A simple fixed-width
representation of $(b,c)$ uses at most
$\lceil\log_2(2D+1)\rceil+1$ bits, apart from public parameters.
The exact depth-one optimum has the stronger zero-preparation
special case already supplied by LTR. $\square$

Installed covers can be very large. Their generation, membership
search, witness tables and rational optimization are separate from
the complete attained alphabet. Initial control and workspace,
literal buffering, post-request workspace, the final predictor,
authentication and count representation, paid handoff and physical
time are also separate. No bound on their joint physical efficiency
or on optimal preparation Read cost follows from the memory rate.
Common tables are source-independent and provide only reply decoders
and experiment choices; they never reveal which actual tree is present.

**Source correspondence 8.2 (two-phase and topological boundaries).**
[Native Birth Provenance, Assumption 14.1 and Theorem 14.4](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md)
supplies the paid common-start, complete-latch, stationary handoff
discipline for its known-row predecessor problem. Its authenticated
one-image family and fixed whole-predecessor output differ from
the full bounded family and late target here. Its service assumptions
are reused as assumptions, not as physical constructions. Likewise
[TargetFamilyMinimalQuotient](../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean),
`target_family_minimal_quotient`, gives the passive joint-kernel
universal property, without a native one-probe acquisition geometry.
[CompactObservationFactorization](../../../D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.lean),
`compact_observation_factorization`, assumes a nonempty compact
space, compatible continuous surjective finite discrete observations
forming a fiber basis, and continuous finite readouts. It supplies
a finite observation level, also for bounded action words under
continuous actions. It supplies no effective acquisition depth,
retained-memory rate, or rate convergence modulus for this task.
Reading these declarations does not certify a new Lean application.

**Source correspondence 8.3 (primary models and limits of transfer).**
The following primary texts locate the mature methods and the
interface differences. The native proofs above do not import their
problem-specific numerical lower bounds or graph-product identities.

| Primary source | Parameter correspondence and exact boundary |
| --- | --- |
| Anna Gál and Peter Bro Miltersen, *The Cell Probe Complexity of Succinct Data Structures*, BRICS RS-03-44, abstract and initial model, [primary report](https://www.brics.dk/RS/03/44/BRICS-RS-03-44.pdf) | Systematic storage has form $x\cdot\phi^{\ast}(x)$, preserving the input and adding an index. Here the stationary boundary reply array is preserved and $E$ is retained advice. Our normalized array has $2^D-1$ four-valued positions, constrained by actual tree syntax. The index is wholly available to the late reader; one native constructor reply is the only charged later probe. Their bit-probe accounting, input families and query functions do not give a native tree lower bound. |
| Sumegha Garg, Songhua He, Yuanzhi Li, Periklis A. Papakonstantinou and Xin Yang, *Systematic Data Structure Lower Bounds via the Query-with-Sketch Model*, [arXiv:2609.18024](https://arxiv.org/abs/2609.18024), Definition 2.1 | The sketch precedes coordinate probes; a deterministic transition chooses its next coordinate from sketch and replies. For each requested function $x\mapsto\Gamma_q(x)$, our retained code corresponds to the sketch and the native boundary Read to one coordinate probe, with one common sketch for all late $q$. Their general coordinate arrays and matrix-powering objectives differ; our sketch must be actually acquired before the request, and its objective is an attained alphabet. No distributional or min-entropy theorem is transferred. |
| Nicolas Charpenay, Maël Le Treust and Aline Roumy, *On the Additivity of Optimal Rates for Independent Zero-Error Source and Channel Problems*, [arXiv:2407.02281](https://arxiv.org/abs/2407.02281), introduction and graph-product discussion | Their zero-error rates distinguish graph products, source distributions and regularized limits; the paper explicitly uses subadditivity before a Fekete limit. Here the reply experiment itself depends on the code and late target, and all pairs can be admissible despite higher-arity obstructions. Neither an AND product nor their independence or entropy hypotheses identify our native hypergraph. The actual gluing and the elementary limit proof are therefore supplied in §§3 and 6. |

Finite fractional covering, finite LP duality and harmonic greedy
rounding are established mathematical tools. Their native input
family, every-word simulation, paid attainment and depth error are
proved here. These are repository-derived ordinary results, without
a worldwide-originality claim. In particular an arbitrary
communication reply cannot replace a constructor reply: (FMR.9),
(FMR.13), (FMR.36) and (FMR.45) specify which replies are available
on the same actual source and how they are obtained.

**Theorem 8.4 (the selected mutual-recovery content).** Under the paid
handoff, source-continuity and authentication assumptions, the
constructions realize

$$
(E(t),D,p,\text{at most one actual native reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow
\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{FMR.46}
$$

Proof. The first arrow is the native cover reader, whose query is
chosen only after $p$ and before any supplied $k$. The two inverse
maps are the reused factor/trajectory correspondence in Convention
1.4. Its first branch count and alpha-stage flag determine the
finite predictive pair, and the pair reconstructs all counts.
$\square$

The inverse arrow recovers that selected temporal factor, not the
whole source, the complete retained code, an earlier hidden history,
or physical spacetime. Initially absent targets are included through
their actual blocking leaves, without a free operation at a born
address. The factor alone cannot certify authentic $k$ or continuity
of the register. Those remain the original independent services.

**Open problem 8.5 (sharp evaluation and the general finite optimum).**
Determine the numerical value of $\lambda$ in (FMR.21), or obtain
matching constructive and all-competitor lower bounds. Also determine
$m_D$ for general finite $D$, including the still unresolved value
$m_3\in\{3,4\}$. The fractional seed rate is an upper construction,
not a claimed optimum. A missing lower structure must control every
jointly admissible correlated fiber, including target-dependent
off-target queries, rather than multiplying individually attainable
child optima. An improved upper would require another effective
whole-family native construction. Neither obligation is removed by
existence of the limit or by a generic finite cover formulation.

**Open problem 8.6 (finite certified numerical convergence).** Find
effective lower certificates approaching $\lambda$. The fractional
infimum in (FMR.21) gives decreasing computable upper endpoints;
its finite-depth dual does not automatically transport to a lower
endpoint at growing depth. The joint-block supremum in (FMR.41)
has geometric depth error, but $\sigma_d$ is itself an infinite
infimum over block lengths. For example a proved bound

$$
\sigma_d\ge n^{-1}\log_2K_d(n)-\eta_d(n),
\qquad \eta_d(n)\longrightarrow0,
\tag{FMR.47}
$$

with an effective certified error, or a convergent family of
all-correlated-fiber dual witnesses, would address this gap.
No such estimate is assumed here; no undecidability or
noncomputability conclusion follows from its absence.

**Open problem 8.7 (the broader recovery programme).** The mathematical
boundary/trajectory relation in (FMR.46) is one selected interface.
Recovering other expressions of space, time, boundary and memory
requires explicit relations, compatible operations and resource
correspondences beyond it. The all-source, all-late-target, all-word
and all-authentic-count quantifiers of the original objective remain
unchanged; this volume supplies a structural advance within that
programme, not its completion.

## 追加锚（本行以下为增补区）

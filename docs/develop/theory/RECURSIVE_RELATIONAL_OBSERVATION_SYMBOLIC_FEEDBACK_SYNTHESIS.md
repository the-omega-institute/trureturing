# Symbolic feedback synthesis for complete acquired native rows

> This generic-v1 volume is reference input. It contains ordinary proofs,
> without a Lean-kernel verification claim. Integrated text is retained;
> corrections and additions follow the final append anchor.

## 1. Entire sources and the joint question

**Definition 1.1 (native domain).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle s,t\rangle&=\langle\rho s,\rho t\rangle,\\
T_n&=\rho^n\alpha\quad(n\in\mathbb N).
\end{aligned}
\tag{SFS.1}
$$

Sources are all nonempty finite free ordered trees. There is no common size,
depth or rank bound. The operation $\rho$ is interpreted by these equations,
not a free unary constructor. Repeated occurrences of one variable share its
entire value. Addresses are finite words in $L,R$, with root $\varepsilon$.
The four-valued reply $r_u(p)$ is $\alpha,\beta,\mathsf{branch}$ or
$\mathsf{absent}$; strict descendants of a leaf are absent. Put

$$
u\equiv_h v\quad\Longleftrightarrow\quad
\forall |p|\le h\quad r_u(p)=r_v(p).
\tag{SFS.2}
$$

Depth is inclusive. For a finite prefix-free cut $A$, its complete original
row $R_A(u)$ retains its ordered reached subset, the entire concrete exterior
with precisely those reached subtrees replaced by numbered holes, and the
complete equality partition of their whole subtrees. Equal repeated subtrees
retain separate hole occurrences. Empty and root cuts are allowed.

**Definition 1.2 (complete acquired input).** Fix
$I=(P,R,H_0,H_{\rm rel},Q,N)$ as in [ARH, Definitions 1.1–1.2][ARH].
The complete old $P$-row $R$ is attained. A literal $(a,p,c)$ means
$r_{\rho^a u}(p)=c$. A signed record $(a,p,b,q,\bowtie)$ means

$$
p\in\operatorname{Pos}(\rho^a u),\qquad
q\in\operatorname{Pos}(\rho^b u),\qquad
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q,
\quad\bowtie\in\{=,\ne\}.
\tag{SFS.3}
$$

Absence invalidates either sign. Lists retain repetitions. All records within
one realization concern its same original source and their stated actual
epochs. Define the entire fiber and full original target strata by

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\},
\qquad D_r=\{u\in D:R_Q(u)=r\}.
\tag{SFS.4}
$$

Every old/off-task inequality, exterior, reached set and partition remains
imposed. Let $B$ be any supplied finite set of distinct attained complete
$Q$-rows, $|B|\ge2$. The joint question is

$$
J_B(h)\quad\Longleftrightarrow\quad
\exists(u_r)_{r\in B}\in\prod_{r\in B}D_r\quad
\forall r,s\in B\quad u_r\equiv_h u_s.
\tag{SFS.5}
$$

These are alternative finite originals for one common producer contract,
sharing one original prefix. Separate pairwise witnesses do not suffice.
One source is never assigned incompatible labels. Rows outside $B$ stay in $D$.

**Assumption 1.3 (paid acquisition and actual service).** Use [ARH, Assumption
1.3 and Proposition 2.1][ARH]. One public source-total paid producer acquires
the old row, literals and both-endpoint whole-subtree comparisons on the same
original-root register, then reaches an authentic common epoch $N$ at least
every record epoch. Conditional on the complete accessible-state cut, its
retained state has exactly fiber $D$, in both directions. All accessible
source-dependent descriptions, caches, lengths, traversal counts, control,
addresses, timing, permissions, archives and handles belong to that premise.
The cut is an access assumption, not a physical-erasure theorem.

Service starts at actual $\rho^N u$. Its source operations are paid
four-valued $\mathsf{Read}$, same-register serial forward
$\mathsf{ApplyRho}$ and absorbing halt. The mathematical coordinates,
hypothetical sources and inverse maps below supply no selector, rank,
equality, clock, reset, reroot, clone, old-version or limit-tree port.
Acquisition, preparation, local work, address length, updates, memory and
retention are separate charges. Sourcewise finite termination does not imply
a uniform finite number of new calls.

**Definition 1.4 (completion).** Let $\widehat{\mathcal T}$ contain all finite
or infinite full ordered binary trees with $\alpha,\beta$ leaves and the same
four replies. It is the closed valid-tree subspace of the countable product
of four-element reply sets, hence compact. It is complete for the prefix
metric $d(S,T)=2^{-\delta(S,T)}$, where $\delta$ is the first differing reply
depth. A finite tree is isolated by its prefix through maximum leaf depth.
Every valid finite prefix has a finite filling. The unique leafless tree is
$\Omega$.

Extend $\rho$ by its actual leaf replacements and pair law. Matching leaf
roots have identical entire finite images; matching branch roots reduce a
requested reply to children at one smaller depth. Induction on that depth
proves prefix nonexpansion of every fixed power, including born and absent
positions. Pairing gains one agreement depth. Finite native expressions are
therefore continuous. Bare $\rho$ is not assumed contracting.

## 2. Homogeneous feedback and exact functional representation

**Lemma 2.1 (completed native interfaces).** The extended $\rho$ is injective
on $\widehat{\mathcal T}$ and has unique preimage $\Omega$ at $\Omega$.
Infinite branches persist. If $X$ has a leaf and $\mu(X)$ is its least leaf
depth, then

$$
\mu(\rho^n X)\ge\mu(X)+\lfloor n/2\rfloor.
\tag{SFS.6}
$$

A fixed power has a leaf exactly when its input does. In particular
$n\ge2h+2$ implies $T_n\equiv_h\Omega$.

Proof. No image has an $\alpha$ root. A $\beta$-root image comes only from
$\alpha$. An image pair whose right child has $\alpha$ root comes only from
the input leaf $\beta$: an original pair would have its right child in the
image of $\rho$. Every other paired image has paired input, and equality
cancels to equality of child images. Induction on each requested original
prefix depth recovers equal inputs from equal outputs. This proves completed
injectivity without a free-unary assumption.

Both $\rho^2\alpha=\langle\beta,\alpha\rangle$ and
$\rho^2\beta=\langle\langle\beta,\alpha\rangle,\beta\rangle$ have minimum
leaf depth at least one. Original branches persist, each old leaf is replaced
by a nonempty finite tree, and every new leaf descends from an old leaf.
Two updates therefore increase least leaf depth by at least one; one update
never decreases it. Iteration proves (SFS.6). A persistent infinite branch
prevents a finite image. The leafless tree is fixed and injectivity gives its
unique preimage. Apply the depth bound to $\alpha$ for the last assertion.
These are the completion interfaces used in [PAC, Lemma 3.2][PAC] and
[FJC, Theorem 3.1][FJC]; [NLC, Lemma 3.1][NLC] supplies atomic depth.

**Definition 2.2 (one-residual homogeneous syntax).** A homogeneous $H(X)$
is a finite ordered pair expression with frontier occurrences $\rho^b X$,
fixed $b\ge0$, an explicit pair at its root, no ground and no second
residual. Put

$$
A_{a,H}\quad\Longleftrightarrow\quad H(\alpha)=T_a.
\tag{SFS.7}
$$

This is automatically decidable: evaluate $H(\alpha)$ in the normal atomic
codes of [ABC, Theorems 2.2–2.3][ABC], using smart pairing, and compare with
$[a]$. No atomic certificate is supplied as input.

**Theorem 2.3 (exhaustive completed homogeneous split).** For every fixed
$a,H$ as above and every $X\in\widehat{\mathcal T}$,

$$
\rho^a X=H(X)
\quad\Longleftrightarrow\quad
X=\Omega\ \lor\
\bigl(A_{a,H}\land\exists c\in\mathbb N\ X=T_c\bigr).
\tag{SFS.8}
$$

The finite solution set is the entire atomic orbit if $A_{a,H}$ holds,
and empty otherwise.

Proof. Use the native mass and clock of [URR, Definition 2.1][URR]:

$$
\begin{aligned}
\gamma(\rho^b t)&=\gamma(t),&\gamma(T_c)&=0,\\
\gamma(\langle s,t\rangle)&\ge\max(\gamma(s),\gamma(t)),\\
\gamma(\langle s,t\rangle)&=1+\gamma(s)+\gamma(t)
&&\text{if either child has positive mass},\\
\kappa(\rho^b t)&=\kappa(t)+b.
\end{aligned}
\tag{SFS.9}
$$

Mass zero is exactly the atomic orbit. If finite $X$ has mass $g>0$ and
$H$ has $m\ge2$ frontier occurrences, its mass is $(m-1)+mg>g$.
Thus a finite solution must be $T_c$. Homogeneity gives
$H(\rho^c\alpha)=\rho^c H(\alpha)$, and completed injectivity cancels
$\rho^c$, making equality equivalent to (SFS.7). This proves both finite
directions. The special finite recurrence
$\rho^2X=\langle\rho X,X\rangle$ is already the first conjunct of the
pinned D5 declaration source_transport_centralizer; it is not claimed anew.

Suppose $X$ is infinite and has a leaf. If every frontier exponent $b\ge a$,
distribution and injectivity reduce the equation to $X=H_-(X)$, subtracting
$a$ from every exponent. Each occurrence remains below a pair, so the
right side has strictly greater minimum leaf depth, a contradiction.

Otherwise choose a frontier address $p$ decorated by $b<a$ and set $e=a-b>0$.
The equation at $p$ gives the entire subtree $\rho^b X$. If $p$ crossed
an original leaf of $X$, the corresponding subtree in $\rho^aX$ would be
finite, whereas $\rho^bX$ is infinite. Hence $p$ is originally reached,
$Y=X|_p$ is infinite, and original subtree transport gives
$\rho^aY=\rho^bX$. Cancellation gives $X=\rho^eY$. Substitute this into
the original equation; homogeneity and cancellation show that $Y$ satisfies
the same feedback equation. Repeat with the same $p,e$. Then
$X=\rho^{ke}Y_k$ for every $k$. Each $Y_k$ has a leaf since $X$ does, and
(SFS.6) gives $\mu(X)\ge\lfloor ke/2\rfloor$ for all $k$, impossible.
Thus an infinite solution is leafless, hence $\Omega$. Conversely its
decorations and every pair of them equal $\Omega$. This completes both
completed-domain directions.

**Proposition 2.4 (rank-free exact conversion obstruction).** When
$A_{a,H}$ holds, the designated-coordinate set in (SFS.8) is not the
projection of a finite union of FJC rank-free functional systems, even with
finitely many auxiliary states. Such a system has at most one equation
$X_i=E_i$ per state, finite grounds, fixed nonnegative powers and ordered
pairs; other states are unrestricted. Projection must preserve the
designated coordinate.

Proof. Normalize one system by [FJC, Theorem 3.1][FJC]. Root-link paths
lead to grounds, free states, positive-shift cycles or pair-guarded
dependencies; zero-shift cycles collapse to free aliases. Positive cycles
force $\Omega$ by (SFS.6). A pair-guarded cycle cannot have finite values:
leaf count is nondecreasing under $\rho$, and a containing pair has a
nonempty sibling, giving strict decrease around the cycle. A coordinate
taking a finite value reaches neither kind of infinite cycle. Its
reconstruction is consequently a finite expression in grounds and genuinely
free states.

If a free state occurs, give it a finite positive-mass value and give every
other free state a finite value. The guarded solution construction extends
these assignments. The designated coordinate is finite and of positive
mass, since powers preserve that mass and containing pairs cannot remove it.
This contradicts containment in $\{T_c:c\in\mathbb N\}\cup\{\Omega\}$.
Otherwise the coordinate has one fixed finite ground value whenever finite.
Each component contributes at most one $T_c$, so a finite union cannot cover
all distinct $T_c$. This obstructs that exact representation only. It
obstructs neither a different stopping method nor an existential productive
contact certificate. The symbolic atomic parameter in §3 avoids this
specific representation restriction.

## 3. Automatic exact source reduction and completed branching

**Definition 3.1 (source charts).** An exact finite chart cover has form

$$
\begin{aligned}
D_r&=\bigcup_b\{\Theta_{r,b}(\mathbf n,\mathbf z):
 P_{r,b}(\mathbf n)\land\Delta_{r,b}(\mathbf n,\mathbf z)\},\\
\Delta_{r,b}&=\bigwedge_\ell A_\ell\ne A'_\ell,\\
A&::=g\mid T_{n_j+c}\mid\rho^e z_i\mid\langle A,A\rangle.
\end{aligned}
\tag{SFS.10}
$$

Source maps have the same grammar. Grounds, offsets and exponents are fixed
finite data and $P$ is Presburger. Before negatives the carrier is the full
Cartesian $\mathbb N^k\times\mathcal T^m$, with no residual positive equation,
image restriction, navigation filter or normality test left over.
Repeated names remain shared; different source copies are renamed apart.
Exactness requires both whole-source directions: every chart point satisfies
the entire $I$ and exactly row $r$, and every $u\in D_r$ is reconstructed
as that same source by some chart. A support section is not an exact chart.
Zero-dimensional products and empty conjunctions have their literal meanings.

**Proposition 3.2 (automatic chart extraction).** From $I,B$ one can
construct (SFS.10) with both source directions, without a supplied source
presentation. A direct constructor-substitution reduction can precede the
general NIC construction.

Proof. Fixed navigation admits finitely many original-prefix cases. Keep
every early leaf, actual reached frontier subtree and repeated source name.
Original branches persist under updates; entry into an early leaf is
evaluated in its explicit finite image. Absence rejects either sign; a
reached case retains its whole native comparison. For each row keep its
reached set, equality of its entire mask to the supplied exterior mask, and
every equality/disequality bit of its complete partition. Uncut residual
subtrees remain in that mask expression. This is [NSF, Lemma 5.1][NSF]
and [NIC, Theorem 4.3][NIC]. An actual source chooses its actual case and
frontiers; filling returns that same source. Conversely a satisfying case
filling has every guard, mask, partition bit and retained signed record.

For a direct reduction expose only nodes needed for navigation or literals.
A whole-subtree request stops at its reached endpoint without inspecting
that subtree. Split an unknown root only when a literal or proper descendant
request needs it. Fixed finite address lengths bound the number of splits.
Distribute powers, evaluate grounds, cancel pairs/common powers, and
substitute a positive bare-variable definition $x=E$ only when $x$ does not
occur in $E$. Retain its reconstruction. Parsing finite grounds is finite
constructor decomposition. Try the finitely many elimination orders;
substitution removes a variable and intermediate decomposition consumes
finite syntax. Use this direct cover only when all positive equations
become identities in every surviving case. Remaining residuals are then
unrestricted before the retained negatives.

If that direct test fails, NIC Theorems 3.2–3.3 give the whole-tuple positive
cover and pull every negative back literally in the native algebra. Its
minimum-offset residual sorts allow arbitrary finite native values: ambient
normality is omitted using NIC Lemma 3.1, while the converse uses the actual
normal blocks of the original assignment. This produces overlapping images,
not extra native solutions. NIC Proposition 3.5 and [PAC, §2][PAC] verify
the full Cartesian pre-negative domain. Substitute that entire assignment
into the original source context to obtain (SFS.10). All eliminations are
equivalences on the same original valuation; both source directions persist.
Nothing is replaced by a marker or a selected feasible support section.

**Definition 3.3 (rank modes).** Choose one chart per row and a
finite/divergent mode for every original rank coordinate, including unused
ones. Replace finite ranks by natural parameters $p_j$, and divergent
atomic outputs by $\Omega$. Do not evaluate $P$ at infinity: retain all
original ranks for the later finite arithmetic policy. Form equality of
each entire completed source map with one reference source map.

Completion syntax uses finite grounds, $T_{p_j+c}$, $\Omega$, decorated
tree variables and pairs. Fresh natural indices can be constrained by
affine equations; subtraction is expressed as $q+a=p_j+c$ with $q\ge0$,
never truncated subtraction. Scalar conditions form a Presburger guard
$\Gamma(\mathbf p)$. Source-copy coordinates are distinct until equations
identify them.

**Definition 3.4 (finite feedback reducer).** Use the following rules,
retaining reconstruction expressions for all original residuals.

1. Distribute powers, compose them, evaluate grounds, delete syntactic
   identities and cancel matching ordered pairs or common powers. Merge
   aliases. Substitute nonrecursive bare-variable definitions.
2. Compile variable-free comparisons, built from parameter atoms, grounds,
   pairs and $\Omega$, to exact Presburger guards using [PAC, Lemma 3.2][PAC].
   Its generalized-description normalization collapses consecutive finite
   atomic children and two $\Omega$ children; every other pair remains.
   Exhaust the finite symbolic shape/rank cases. False guards are clashes.
3. Replace $\Omega=\langle E,F\rangle$ by $E=\Omega,F=\Omega$, and
   $\rho^aX=\Omega$ by $X=\Omega$. Different powers of the same variable
   being equal force it to $\Omega$.
4. At $\rho^aX=H(X)$ of Definition 2.2, run (SFS.7). Replace it by
   $X=\Omega$, together with a second branch $X=T_c$, fresh $c\in\mathbb N$,
   exactly when that test is true. Substitute this value and remove $X$.
5. After these reductions try the finitely many orientations of remaining
   equations having a bare-variable endpoint. Accept only an orientation
   covering every equation with at most one definition per state. Other
   states are free. Recursive definitions are allowed. Unhandled comparisons
   or failed orientations are OUTSIDE, not clashes.

Use a fixed order on finite displayed syntax at normalization phases.
Recursively defined states are never unfolded during recognition. Every
semantic branch must be handled: one OUTSIDE branch makes its tuple/mode
ineligible even if other branches succeed. There is no finite occurs-check.
The finite source charts and their negatives stay intact; the reducer
operates only on their cross-source completed output equations.

**Lemma 3.5 (termination and exhaustive completed representation).** The
reducer terminates on every tuple/mode. If it has no OUTSIDE branch, it
produces finitely many cases $\tau$, each a guard and functional system

$$
\mathscr G_\tau(\mathbf p):\quad X_i=E_i(\mathbf p,\mathbf X),
\tag{SFS.11}
$$

with at most one definition per state, or a proved clash. Each original
residual has a finite reconstruction expression. For fixed original
finite-mode ranks, the completed common-output solution set is exactly the
union of these reconstructed guarded solution sets over their fresh finite
parameters. Both directions hold.

Proof. A substitution, alias merge or homogeneous split removes a tree
variable; no rule creates one. There are finitely many such steps per path.
Between them pair decomposition and normalization consume finite syntax.
An $\Omega$ decomposition removes a pair; cancellation removes powers.
Variable-free equality has finitely many symbolic normal-code cases and
enumerates no parameter values. Substitution can enlarge syntax, but occurs
only finitely often. Modes, semantic splits and final orientations are
finite. Hence recognition terminates, including OUTSIDE.

Distribution and ordered-pair cancellation are native identities. Lemma 2.1
justifies common-power cancellation and the $\Omega$ rules. A nonzero
same-variable period, iterated, contradicts (SFS.6) if a leaf exists; thus
$\Omega$ is its sole solution. PAC supplies exact variable-free equality.
Theorem 2.3 supplies both directions and all finite values of each feedback
split with its single unbounded natural parameter. Substitution restricts
and reconstructs solutions; orientation changes no equation. Induction
through these equivalences proves both directions. An actual completed
solution chooses its true scalar and feedback alternatives; reconstruction
of any guarded solution satisfies every original completed output equation.
No sign or finite partition is imposed on a completed point.

**Definition 3.6 (recognizable synthesis class).** Apply Proposition 3.2 and
the reducer to every chart tuple and mode. The input $(I,B)$ belongs to
$\mathcal C_{\rm fb}$ exactly when every branch is a proved clash or an
accepted functional case. This is a decidable syntactic class of complete
acquired inputs. No barrier list, contact or functional presentation is
supplied: all required objects are synthesized from the input. Membership
depends on the fixed finite extraction/reduction procedure. Failure means
only that this procedure has not settled the original question.

## 4. Parameter-symbolic finite-coordinate synthesis

**Theorem 4.1 (canonical solution and parameter rigidity).** Uniformly for
all natural $\mathbf p$ satisfying an accepted guard, one can construct a
canonical completed solution $\mathbf K_\tau(\mathbf p)$. For every
designated original residual one can decide syntactically whether its
canonical value is finite; this classification is parameter-independent.
In the finite case its value is a finite expression $f_i(\mathbf p)$ in
grounds, parameter atoms, fixed powers and pairs, and every solution of
that case has that exact value. Other canonical original coordinates are
infinite and have computable prefixes for every supplied $\mathbf p,h$.

Proof. Extend [FJC, Theorem 3.1][FJC] by treating finite parameter atoms as
finite terminals without expanding or bounding them. Normalize defining
roots to finite terminals, $\Omega$, pairs or root links $\rho^aX_j$.
The root-link graph has outdegree at most one. Follow its finite paths,
accumulating weights. A zero-weight cycle is free aliases; a positive
cycle forces $\Omega$ by (SFS.6). Substitute paths ending at grounds,
pairs or free states and keep every reconstruction expression.

Remaining defined states have explicit pair roots and all their state
occurrences lie below a pair. Assign arbitrary completed free-state values.
Simultaneous evaluation gains one prefix depth: any two $n$-fold iterates
agree through $n-1$, and successive iterates have that agreement. Completeness
and continuity give a fixed point; the same estimate proves uniqueness for
the assigned free values. Set free states to $\Omega$ for the canonical
solution. Reconstruct root links to obtain a solution of the original
system; restricting any solution gives the normalized system, proving
both representation directions.

A state is canonically finite precisely when its reachable occurrence graph
is acyclic and reaches neither a free state nor $\Omega$. Reverse-order
evaluation gives a finite expression in terminals, forced in every solution.
A reachable infinite terminal makes its predecessors canonically infinite
because powers and pairs preserve an infinite branch. A pair-guarded cycle
cannot have finite values by strict leaf-count decrease around that cycle;
its predecessors are infinite. Apply this test to each original-coordinate
reconstruction. Graph finiteness is independent of parameter values, even
when finite atoms coincide or an explicit pair becomes atomic. The finite
reconstruction is the same in every solution.

Compute infinite-coordinate prefixes by finitely many guarded iterations
and their reconstruction expressions. Terminals at chosen parameters are
actual computable finite trees. A canonically infinite coordinate depending
on a free state can be finite in a different solution; rigidity is claimed
only for canonically finite coordinates. No sign is assigned to the limit.

## 5. Symbolic barriers and one joint cofinal support

**Lemma 5.1 (symbolic negative projection).** Let $f$ be a symbolic finite
tuple of finite native values, $\mathbf n$ a natural-rank tuple, and $y$
an unrestricted Cartesian tuple of finite native trees. There is a
terminating compiler $U_y(A,B)(\mathbf n,f)$ to a conjunction of native
equalities without $y$, or true/false, such that

$$
U_y(A,B)(\mathbf n,f)
\quad\Longleftrightarrow\quad
\forall y\ A(\mathbf n,f,y)=B(\mathbf n,f,y).
\tag{SFS.12}
$$

For every finite list, including repetitions,

$$
\exists y\ \bigwedge_\ell A_\ell\ne B_\ell
\quad\Longleftrightarrow\quad
\bigwedge_\ell\neg U_y(A_\ell,B_\ell)(\mathbf n,f).
\tag{SFS.13}
$$

If $f_i=f_i(\mathbf p)$ are the finite expressions of Theorem 4.1, this
finite-barrier locus is effectively Presburger in $(\mathbf n,\mathbf p)$.

Proof. Normalize powers. If neither side contains $y$, return its native
equality; if exactly one does, return false. If both roots are pairs,
recurse on corresponding children and conjoin. Two decorated live variables
return true exactly when names and exponents coincide. A live-variable/pair
comparison returns false. These exhaust the grammar and decrease syntax size.

Fix actual finite $\mathbf n,f$ for the proof, making all live-free
expressions finite grounds. Unbounded live mass distinguishes a
live-containing expression from a ground. Distinct live names vary
independently; distinct powers of one name have distinct clocks. For a live
variable against a live-containing pair, assign every live variable the
same positive mass: the pair has at least one more than that mass. Native
pair injectivity verifies the recursive case. Thus (SFS.12) is exact,
including exceptional atomic-code collapses.

Necessity of (SFS.13) is immediate. For sufficiency none of the listed
equalities is universal at these fixed finite parameters. [URR, Theorem
3.1 and Corollary 3.2][URR] supplies one finite tuple avoiding all of
them together, and finite witness extraction after parameters are chosen.
Empty products/lists have their singleton/true meanings.

Substitute $f_i(\mathbf p)$. Remaining native comparisons involve only
finite pair expressions over parameter atoms. Bottom-up smart pairing
splits into finitely many arithmetic cases, collapsing $[q+1],[q]$ to
$[q+2]$. Normal-code equality is matching shape and corresponding ranks.
URR Corollary 3.2, or the finite part of PAC Lemma 3.2, gives the exact
Presburger formula without enumerating trees or parameter values. Positive
live-variable restrictions would invalidate this lemma; none are dropped.

**Definition 5.2 (whole case support).** Let $\mathbf p$ contain every
finite-mode original rank and all fresh finite parameters from completed
reduction. Let $\mathbf w$ contain the actual finite values of every
divergent original rank, including invisible ones. In each chart substitute
exactly its canonically finite original residuals $f_i(\mathbf p)$.
Leave all other original residuals unrestricted finite variables.
Lemma 5.1 computes the exact simultaneous feasibility predicate
$\Psi_{r,\tau}(\mathbf p,\mathbf w)$ for that entire negative list. Put

$$
\begin{aligned}
\Phi_\tau(\mathbf p,\mathbf w)
 &=\Gamma_\tau(\mathbf p)\land
 \bigwedge_{r\in B}
 \left(P_{r,b_r}(\mathbf n_r(\mathbf p,\mathbf w))
       \land\Psi_{r,\tau}(\mathbf p,\mathbf w)\right),\\
G_\tau
 &=\{\mathbf p:\forall M\in\mathbb N\ \exists\mathbf w\
       \Phi_\tau(\mathbf p,\mathbf w)\land
       \bigwedge_{j\ {\rm divergent}}w_j\ge M\}.
\end{aligned}
\tag{SFS.14}
$$

Here $\mathbf n_r$ restores that chart's original rank vector, keeping all
sharing and incidence. There is one joint support, not a product of cofinal
marginals. With no divergent coordinates, cofinality means feasibility of
the singleton empty tuple. With no finite parameters, $G_\tau$ is either
empty or its singleton empty tuple.

**Proposition 5.3 (deciding all finite parameters together).** Each
$G_\tau$ is effectively Presburger and semilinear, with decidable
emptiness. If nonempty, one can choose one fixed $\mathbf p_0\in G_\tau$
and produce, for each supplied $M$, one joint $\mathbf w$ satisfying
$\Phi_\tau$ and every lower bound.

Proof. Lemma 5.1 makes $\Phi_\tau$ Presburger and (SFS.14) uses only
first-order natural quantifiers and inequalities. [Ginsburg–Spanier,
Theorems 1.2–1.3][GS] supplies decision and effective semilinear conversion.
After nonemptiness is proved, enumerate natural tuples with decidable
membership to obtain $\mathbf p_0$. For each $M$, enumerate $\mathbf w$
and test its decidable finite formula; membership in $G_\tau$ ensures
termination. These searches begin only after their existence is proved.
Neither finite parameters nor their finite tree values are reselected
after seeing a depth.

**Theorem 5.4 (automatic source-faithful joint-prefix alternative).** For
every $(I,B)\in\mathcal C_{\rm fb}$,

$$
\forall h\in\mathbb N\ J_B(h)
\quad\Longleftrightarrow\quad
\exists\tau\ \exists\mathbf p\in G_\tau.
\tag{SFS.15}
$$

A terminating mathematical procedure returns either a function producing
actual finite witnesses to $J_B(h)$ for every requested $h$, or a finite
$H$ with $\neg J_B(H)$. Every witness satisfies the entire original input
and its exact full row. No barrier, contact or functional presentation is
supplied. OUTSIDE on other inputs settles neither alternative.

Proof. Suppose $\mathbf p_0\in G_\tau$. Construct the canonical completed
solution and original-coordinate reconstructions. Lemma 3.5 makes all
completed whole source outputs equal to one $W$. Keep finite original
residuals exactly $f_i(\mathbf p_0)$. For a supplied inclusive $h$, compute
the depth-$h$ prefix of every remaining canonical infinite coordinate,
retaining early leaves and absent descendants.

Choose one joint $\mathbf w$ in (SFS.14) with every divergent rank at
least $2h+2$. Each divergent atom then agrees through $h$ with $\Omega$.
At these same ranks and fixed finite values, $\Psi_{r,\tau}$ asserts
feasibility of the whole chart negative list. Apply [SLP, Lemma 2.1][SLP]
to its remaining coordinates and their computed infinite prefixes. Its
Cartesian hypothesis holds by Proposition 3.2; every finite coordinate
has already been fixed. Repetitions inside a source use one prefix and
filling. SLP gives one finite tuple satisfying all that source's negatives
together. Identifications across different completed source copies do
not require their finite fillings to coincide.

Evaluate each original source map. Prefix nonexpansion makes it agree
through $h$ with $W$. Chart soundness gives its entire old row, exterior,
every guard and sign, and exactly its target label. These finite sources
need not solve cross-source completed equations as exact finite equalities:
they satisfy their own signed source predicates exactly and share one
original prefix. Every operation terminates for supplied $h$. This proves
sufficiency and finite witness production.

Conversely suppose all $J_B(h)$ hold. Choose finite source tuples at
increasing depths and lift each as itself through the exact covers.
Some fixed chart tuple occurs at unbounded depths; keep that subsequence.
For finitely many ranks, extract successively so each is either constant
or tends to infinity. A bounded coordinate has a value occurring infinitely
often; an unbounded one has a subsequence exceeding every bound. Preserve
previous choices during extraction. This fixes one mode and its original
finite-mode parameters. Compactness gives a further convergent subsequence
of the finite residual product.

Finite-mode atoms stay constant, divergent atoms converge to $\Omega$,
and continuity plus increasing common prefixes makes completed source
outputs equal. Lemma 3.5 places this limit in an accepted case with some
fixed finite auxiliary parameters. In an atomic feedback alternative the
fresh parameter is the rank of its actual finite limit; an escaping atomic
rank instead belongs to the $\Omega$ alternative. Thus the entire chosen
$\mathbf p$ is fixed before every following lower bound.

By Theorem 4.1 every canonically finite original coordinate is rigid in
all solutions of this case, so its limit equals $f_i(\mathbf p)$. Finite
tree isolation makes these coordinates of the finite witness sequence
eventually equal those values exactly, all at one late index. Actual
divergent ranks exceed every prescribed $M$ at sufficiently late indices.
Each such original witness still satisfies all its $P$ and its entire
$\Delta$. It therefore witnesses $\Phi_\tau(\mathbf p,\mathbf w)$ with
every divergent entry at least $M$. This proves $\mathbf p\in G_\tau$.
No sign or partition was passed to a limit: necessity used only finite
isolation and actual finite witnesses.

There are finitely many cases and all $G_\tau$ are decidable. If one is
nonempty, the first construction returns YES. If all are empty, necessity
proves some depth fails. Start the existing NSF finite whole-source queries
$J_B(0),J_B(1),\ldots$, with one source variable per row, each complete
(SFS.4), its full label and all common-prefix replies. [NSF, Lemma 5.1
and Theorem 5.2][NSF] decide each query. The proved failure of the all-depth
statement ensures a first NO at a finite $H$. Depth enumeration alone would
not supply that guarantee. Monotonicity also excludes all greater depths.
Both outcomes are thus terminating and source-faithful.

**Remark 5.5 (quantifier and correlation boundaries).** The order is
$\exists\mathbf p\ \forall M\ \exists\mathbf w$, not
$\forall M\ \exists\mathbf p,\mathbf w$. For example $w\le p$ admits the
latter order with $w\ge M$ and not the former. Likewise
$\{(w_1,w_2):w_1=0\text{ or }w_2=0\}$ has cofinal marginals but no
jointly cofinal support. These elementary arithmetic distinctions explain
the retained incidence in (SFS.14); they assert no additional acquired
family or native impossibility theorem.

## 6. An entire acquired constructor-feedback consumer

**Definition 6.1 (seven-hole source).** Let $C[v_1,\ldots,v_7]$ be the
right-comb context defined by $C_1[v_1]=v_1$ and
$C_k[v_1,\ldots,v_k]=\langle v_1,C_{k-1}[v_2,\ldots,v_k]\rangle$,
using $C=C_7$. Its hole addresses are $p_i=R^{i-1}L$ for $1\le i\le6$
and $p_7=R^6$. Put

$$
\begin{aligned}
F(a)&=\rho^2a,&G(a)&=\langle\rho a,a\rangle,\\
H_a(y)&=\langle a,\langle\rho y,\alpha\rangle\rangle,\\
U(a,b,y,c)&=C[a,b,F(a),G(a),y,c,H_a(y)].
\end{aligned}
\tag{SFS.16}
$$

Let $\Delta(a,y)$ be all ten pairwise negatives between the entire values
$a,F(a),G(a),y,H_a(y)$. Take the root cut $P=\{\varepsilon\}$ and its
attained full one-hole old row, $Q=\{p_1,\ldots,p_7\}$, and $N=2$.
Retain epoch-zero branch literals at $R^j$ for $0\le j\le5$, at
$p_4,p_7,p_7R$, and the epoch-zero $\alpha$ literal at $p_7RR$.
The positive history is

$$
\begin{gathered}
(0,p_3,2,p_1,=),\quad(0,p_4L,1,p_1,=),\quad(0,p_4R,0,p_1,=),\\
(0,p_7L,0,p_1,=),\quad(0,p_7RL,1,p_5,=).
\end{gathered}
\tag{SFS.17}
$$

Retain all ten epoch-zero negative comparisons between distinct positions
of $\{p_1,p_3,p_4,p_5,p_7\}$. Every sign requires both endpoints reached.
There are no further constraints in this example; general inputs retain any
additional constraints they contain.

**Proposition 6.2 (entire fiber and both full-row directions).** The entire
acquired fiber is exactly

$$
D=\{U(a,b,y,c):a,b,y,c\in\mathcal T,\ \Delta(a,y)\}.
\tag{SFS.18}
$$

Two distinct attained complete rows have exterior $C$, reached set $Q$, and
partitions in the displayed hole numbering

$$
\begin{aligned}
\pi_0&=\{\{1\},\{2,3\},\{4\},\{5,6\},\{7\}\},\\
\pi_1&=\{\{1\},\{2,4\},\{3\},\{5\},\{6,7\}\}.
\end{aligned}
\tag{SFS.19}
$$

Their entire strata have exact Cartesian negative charts

$$
\begin{aligned}
D_0&=\{\Theta_0(a,y)=U(a,F(a),y,y):\Delta(a,y)\},\\
D_1&=\{\Theta_1(a,y)=U(a,G(a),y,H_a(y)):\Delta(a,y)\}.
\end{aligned}
\tag{SFS.20}
$$

Proof. The six outer branch literals force $C$. Call its actual first,
second, fifth and sixth hole values $a,b,y,c$. These holes are originally
reached and persist under updates. The branch literals at $p_4,p_7,p_7R$
make the listed children reached; $p_7RR$ is the displayed leaf.
The five positives, by same-original subtree transport, force hole 3
to be $F(a)$, hole 4 to have children $\rho a,a$, and hole 7 to have
children $a,\langle\rho y,\alpha\rangle$. The ten negatives are exactly
$\Delta$. Extraction therefore reconstructs that same original as (SFS.18).

Conversely each displayed finite $U$ has every literal, every equality
at its stated epoch, and both guards. Its $\Delta$ verifies every negative
and both guards. The old root row has its stipulated single reached hole
and one class. This proves both entire-fiber directions.

Within $D$ the five base values are distinct. Partition $\pi_0$ forces
exactly $b=F(a),c=y$; partition $\pi_1$ forces $b=G(a),c=H_a(y)$.
All other classes are distinct by $\Delta$. Filling proves one stratum
direction and extracting actual holes proves the other. This checks all
21 unordered pair bits, including equalities, with the full exterior and
all seven reached holes. Other attained rows remain in $D$. The direct
reduction in Proposition 3.2 gives these charts by constructor decomposition
and the acyclic positive substitutions, leaving no residual filter.

For attainment let $c_0=\alpha$, $c_{j+1}=\langle c_j,\alpha\rangle$.
Take $a=c_1$, $y=c_m$, $m\ge4$. The five masses are $1,1,3,m,m+3$.
The first two have clocks differing by two; all other pairs have distinct
masses. Thus $\Delta$ holds and both choices in (SFS.20) are actual finite
originals with the exact stated rows. ARH Proposition 2.1 supplies one
source-total paid producer for these fixed schedules at $N=2$, conditional
on Assumption 1.3. Every source in (SFS.18) yields that same successful
retained output and every source yielding it is in (SFS.18). This does not
certify a physical cut or refund acquisition.

**Theorem 6.3 (synthesized barriers and non-rational contact).** The pair
$B=\{r_0,r_1\}$ belongs to $\mathcal C_{\rm fb}$. Its synthesis produces
legal finite originals at every requested depth. Its unique common closure
point is

$$
W=C[\Omega,\Omega,\Omega,\Omega,K,K,K],\qquad
K=\langle\Omega,\langle\rho K,\alpha\rangle\rangle.
\tag{SFS.21}
$$

Both $K,W$ are non-rational native trees, having infinitely many distinct
rooted subtrees. Neither whole stratum has a finite exact atomic-output
anchor cover of AAB/PAC type.

Proof. Completed equality of the source maps compares holes 1 and 5,
forcing $a_0=a_1=a$, $y_0=y_1=y$. Holes 2 and 6 then force

$$
\rho^2a=\langle\rho a,a\rangle,\qquad y=H_a(y).
\tag{SFS.22}
$$

Conversely these equations make all seven holes equal and reconstruct equal
entire completed source outputs. Theorem 2.3 automatically splits the first
equation into $a=T_c$, $c\in\mathbb N$, or $a=\Omega$, since
$G(\alpha)=T_2$. In the finite branch $a$ is rigid. Its retained negative
$F(a)\ne G(a)$ fails for every $c$. Lemma 5.1 rejects that whole infinite
barrier family by one symbolic formula, without enumerating or supplying
the finite barriers.

In the infinite branch $a=\Omega$, and $y=H_\Omega(y)$ is pair-guarded.
Theorem 4.1 computes its unique fixed point $K$ and stabilized finite
prefixes. Both original canonical coordinates are infinite. The full
finite seed in Proposition 6.2 proves feasibility of all ten negatives,
so its rank-free support is true. Theorem 5.4 now constructs finite sources
in each entire stratum for every $h$: compute prefixes of $\Omega,K$,
apply SLP to each entire $\Delta$, and evaluate (SFS.20). All signs and
full partitions hold on these finite originals. Their cross-source feedback
need not hold as an exact finite equation.

Any common closure point retains $C$ and gives, by extraction at holes
1 and 5 and continuity, the same $a,y$ satisfying (SFS.22). Finite
$a=T_c$ is isolated, forcing nearby finite originals to have exactly that
$a$, in violation of the retained $F(a)\ne G(a)$. Thus $a=\Omega$.
Guarded uniqueness forces $y=K$, giving only $W$. The finite construction
already proves the reverse closure inclusion. No negative is asserted on $W$.

The equation gives $K|_{RL}=\rho K$, $K|_{RR}=\alpha$. The path $RL$
stays on original branch nodes under every iterate. Repeated subtree
transport gives $K|_{(RL)^j}=\rho^jK$ and

$$
K|_{(RL)^jRR}=\rho^j\alpha=T_j\qquad(j\ge0).
\tag{SFS.23}
$$

These are distinct finite subtrees, proving non-rationality of $K$ and
of its containing source $W$. [SPC, Theorem 4.2][SPC] already supplies
guarded non-rational contacts for its context family; the increment here
is automatic exhaustive finite feedback/barrier synthesis together with
that guarded continuation and entire signed sources.

Finally keep $a=c_1$ and let $y=c_m$, $m\ge4$, in both strata. Source
mass is unbounded because $y$ is an original subtree. A fixed template
over finite grounds, atomic tokens and finitely many pairs has mass at most
its ground masses plus its pair count, independently of its ranks:
$\gamma(T_n)=0$ and
$\gamma(\langle s,t\rangle)\le1+\gamma(s)+\gamma(t)$.
A finite union keeps a finite bound and cannot cover either entire stratum.
This proves absence of the atomic-output-anchor premise, not just absence
of one chosen presentation.

## 7. Certified-N consumers and the unchanged open programme

**Corollary 7.1 (selected obstruction and whole-image recovery).** Under
Assumption 1.3, YES for any selected $|B|\ge2$ excludes uniform
finite-new-read exact whole-row service on the entire $D$, including lawful
adaptive serial forward updates. Sourcewise finite recovery remains possible.
NO excludes only its selected joint $B$.

If the exact entire attained image $A=R_Q(D)$ is finite, every distinct pair
belongs to $\mathcal C_{\rm fb}$, and every pair returns NO, there is an
effective whole-row service at the actual certified $N$. Let $H$ be the
maximum pair exclusion depth, taking $H=0$ for a singleton image. An upper
bound is

$$
q\le2(2^{H+1}-1),\qquad a=0,\qquad
|p|\le H+\lceil N/2\rceil
\quad\text{for each submitted address }p.
\tag{SFS.24}
$$

Proof. YES supplies distinct-row common prefixes at every depth, so no
original depth determines the complete row. [ARH, (ARH.2.3)][ARH] equates
this with failure of a uniform finite-new-read static or serial service
under the stated common-state premises. Sourcewise recovery uses the actual
current-register historical decoder to traverse the original finite tree,
requesting children only after a branch reply. It terminates on each finite
source and computes its full row, without a resulting uniform call cap.

For the positive claim the exact finite-image list and original realizers
come from [NPL, Theorem 5.3][NPL], under its full-input hypotheses.
Every depth-$H$ prefix meets at most one row, since all distinct pairs have
been excluded. Decode all $2^{H+1}-1$ original replies through $H$ by actual
epoch-$N$ calls using the pinned DelayedOriginalReadout.original_decoder_service.
Each needs at most two reads of length at most $H+\lceil N/2\rceil$.
NSF's prefix-conditioned full-source query returns a candidate with that
acquired prefix; its full row is forced. A precomputed finite prefix table
is another consumer. This is [NSF, Theorem 6.1][NSF]. Only actual current
calls produce observations; local witnesses are not free source selection.
Total literal length is bounded by the call bound times the address bound.
Preparation, local work and memory remain separately charged.

Theorem 6.3 therefore excludes unassisted uniform finite-call recovery on
its entire acquired fiber at $N=2$, while retaining sourcewise finite
traversal. Under [SJM, Theorem 2.2][SJM] it gives only the selected two-row
lower bound for an extra complete-field alphabet, not an exact whole-image
memory minimum. A joint exclusion of three rows need not exclude any pair,
and a selected list need not be the entire image. Neither substitutes for
the positive pair hypothesis above.

**Open problem 7.2 (unrestricted source-faithful stopping).** For arbitrary
complete acquired signed-native input and finite attained $B$, decide between
finite joint exclusion and actual finite originals at every depth while
retaining the full original domain, target and action language. The missing
step is complete treatment of arbitrary mixed completed residual/constructor
equations after exact source reduction, including interacting definitions,
image/preimage restrictions and cases outside homogeneous splitting or a
one-definition-per-state orientation. OUTSIDE proves neither a counterexample
nor undecidability.

The unrestricted alternative and the wider programme of a minimal relational
structure with proved mutual-recovery conditions for spatial, temporal,
boundary and memory expressions remain open. This recognizable class is
an increment. Finite-depth feasibility, finite whole-row image, supplied
coordinate closure and supplied-certificate checking remain different existing
results; none alone proves synthesis or all-depth completeness. Proposition
2.4 obstructs one representation, not the original goal. No premise is taken
from pending terminal-overlap, coupled-rank, NCC/NGE or positive-domain drafts.

## 8. Sources, attribution and verification boundaries

**Definition 8.1 (supplier versions and production).** Every repository
supplier used here is read at immutable panel pin
fbccdb7e942aecb257cb70761488a7eef54a7374. Links below identify owning sources;
the pin fixes their mathematical versions. Later integration content supplies
no additional premise. This volume is ordinary mathematics, not a new Lean
verification, an executed solver or an external-priority claim.

| Source | Exact contribution and boundary |
| --- | --- |
| [ARH, §§1–3 and Lemma 19.2][ARH] | Complete same-original input, both guarded signs, paid source-total acquisition, complete cut, clock and static/serial original-prefix bridge. Physical access factoring remains a premise. |
| [ABC, Theorems 2.2–2.3][ABC]; [URR, §§2–3][URR] | Normal atomic codes, native mass/clock, simultaneous finite negative separation and exact Presburger projection. No sign-on-limit rule follows. |
| [NIC, Lemma 3.1, Theorems 3.2–3.3 and 4.3, Proposition 3.5][NIC]; [PAC, §2][PAC] | Exact finite source covers with Cartesian pre-negative residuals and reconstruction of every same original. A support section never replaces the image. |
| [NSF, Lemma 5.1, Theorems 5.2 and 6.1][NSF] | Fixed navigation, full-row queries, finite original witnesses, supplied-depth decisions and actual prefix consumer. These alone do not decide all depths. |
| [FJC, Theorems 3.1 and 4.2][FJC] | Root-link/guarded normalization, canonical finite rigidity and rank-free signed bridge. Here finite parameters remain symbolic and original joint ranks are retained. |
| [SLP, Lemma 2.1 and Corollary 3.2][SLP] | Simultaneous finite signed filling of independent infinite-coordinate prefixes after every finite coordinate is fixed. |
| [PAC, Lemma 3.2 and §4][PAC]; [AAB, §§2–4][AAB] | Symbolic atomic descriptions, joint cofinal arithmetic and exact whole-output-anchor scope. The anchor premise is absent in §6; arithmetic techniques are credited. |
| [SPC, Theorem 4.2][SPC]; [NLC, Lemma 3.1][NLC] | Guarded interpreted non-rational contact and atomic depth background, without this automatic finite-feedback synthesis. |
| [NPL, Theorem 5.3][NPL]; [SJM, Theorem 2.2][SJM] | Exact entire finite row image and minimum complete-field theorem, used only under their stated hypotheses. |
| [SourceTransportCentralizer][CENTRALIZER] | First conjunct of source_transport_centralizer classifies finite stability. Its public statement and local injectivity/orbit proof were inspected; reading supplies no new compilation evidence. |
| [NativeDepthPatterns][DEPTH] | Public original_present_transport, original_prefix_locality and depthEquiv; private fill_decompose/decompose_fill verify exact finite-prefix reconstruction. |
| [NativeCutFibers][CUT] | Public rowFiberEquiv/legal_values_row and private classValue_distinct, recover_fill, fill_injective retain the entire old row and actual source in both directions. |
| [NativeSymbolicRecutting][RECUT] | Public symbolic_recut_exact and private termAt_fill/exterior_commute retain reached holes, uncut exterior and every partition bit under their depth hypotheses. |
| [DelayedOriginalReadout][READOUT] | Public original_decoder_correct/original_decoder_service and private present_label_decode/original_query_bounds supply actual finite-N replies and read/address bounds, without an inverse runtime operation. |

**Definition 8.2 (primary literature and new-content status).** Ginsburg
and Spanier, *Semigroups, Presburger Formulas, and Languages*, Pacific
Journal of Mathematics 16 (1966), 285–296, [Theorems 1.2–1.3][GS],
is literature-attested for Presburger decision and effective semilinear
conversion. It is applied after native elimination into (SFS.14).

Comon and Lescanne, *Equational Problems and Disunification*, Journal of
Symbolic Computation 7 (1989), 371–425, DOI 10.1016/S0747-7171(89)80017-3,
[§6.2][CL], explicitly limits transfer of preceding free-tree results to
nontrivial equational theories. This is literature-attested background,
not an imported native interpreted-$\rho$ stopping theorem. The actual
leaf laws are checked directly in §2.

Milius and Moss, *The Category Theoretic Solution of Recursive Program
Schemes*, [arXiv:0904.2385v2, Theorems 7.5 and 7.15, §7.3][MM],
supplies literature-attested guarded interpreted-recursion background.
Its Elgot/completely iterative algebra and contracting metric hypotheses
matter. Theorem 4.1 verifies the required native guarded prefix construction
directly; it assumes no contraction of bare $\rho$ and transfers no
completeness for arbitrary nonfunctional equations.

The homogeneous completed split, exact representation obstruction, automatic
feedback reduction, parameter-symbolic rigidity and source-faithful signed
cofinal synthesis are repo-derived ordinary deductions. Their actual
consumer is Theorem 6.3 and Corollary 7.1. Normal coding, finite feasibility,
local signed lifting, guarded recursion and arithmetic cofinality are
credited suppliers. This bounded comparison makes no suspected-novel or
literature-wide originality claim.

No Lean verification, new solver execution or numerical experiment is
claimed. Structural, whitespace and local-reference checks validate document
delivery only. The physical complete-state cut, same-register continuity
and authentic epoch remain supplied premises. Open problem 7.2 is not settled
by any statement of this volume.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[FJC]: RECURSIVE_RELATIONAL_OBSERVATION_FUNCTIONAL_JOINT_CONTACT.md
[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md
[PAC]: RECURSIVE_RELATIONAL_OBSERVATION_PARAMETRIC_ATOMIC_CONTACT.md
[AAB]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_ACCUMULATION_BASIS.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[SJM]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_JOINT_MEMORY.md
[CENTRALIZER]: https://github.com/the-omega-institute/trureturing/blob/fbccdb7e942aecb257cb70761488a7eef54a7374/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[DEPTH]: https://github.com/the-omega-institute/trureturing/blob/fbccdb7e942aecb257cb70761488a7eef54a7374/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[CUT]: https://github.com/the-omega-institute/trureturing/blob/fbccdb7e942aecb257cb70761488a7eef54a7374/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[RECUT]: https://github.com/the-omega-institute/trureturing/blob/fbccdb7e942aecb257cb70761488a7eef54a7374/D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[READOUT]: https://github.com/the-omega-institute/trureturing/blob/fbccdb7e942aecb257cb70761488a7eef54a7374/D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[MM]: https://arxiv.org/pdf/0904.2385v2

## 追加锚（本行以下为增补区）

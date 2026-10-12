# Constructor cycles, joint atomic coordinates and complete original-row recovery

## 1. Sources, acquired constraints and the recognized question

**Assumption 1.1 (the original acquired fiber).** The source domain is

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{CAR.1}
$$

All trees are nonempty, finite, ordered and free. A physical address is any
finite word over $\{L,R\}$, including the empty word $\varepsilon$.
The literal reply $r_u(p)$ is $\alpha$, $\beta$, $\mathsf{branch}$ or
$\mathsf{absent}$. Write $u|_p$ only when $p$ is reached.

Use the complete acquired input of [ARH, Assumption 1.3][ARH]. Thus $P,Q$
are finite prefix-free original cuts; the old row $R_P(u)=R$ retains the
concrete exterior, reached holes and their complete whole-subtree equality
partition. There are finite literal and signed relation histories $H_0$
and $H_{\rm rel}$. A relation $e=(a,s,b,t,\bowtie)$ means

$$
\operatorname{Rel}_e(u)\iff
 s\in\operatorname{Pos}(\rho^a u)\ \land\
 t\in\operatorname{Pos}(\rho^b u)\ \land\
 (\rho^a u)|_s\ \bowtie\ (\rho^b u)|_t,
\qquad \bowtie\in\{=,\ne\}.
\tag{CAR.2}
$$

An absent endpoint invalidates either sign. The domain is the entire
nonempty fiber

$$
D=\{u:R_P(u)=R,\quad
 r_{\rho^a u}(p)=c\ ((a,p,c)\in H_0),\quad
 \operatorname{Rel}_e(u)\ (e\in H_{\rm rel})\}.
\tag{CAR.3}
$$

Every repeated old class, every different-class inequality, every off-task
constraint and every retained record remains imposed on this same source.
The complete accessible state is common precisely on $D$. Source-bearing
caches, addresses, lengths, counts, program control, timing, references,
permissions and archives are included in that state. The relations were
actually acquired before the cut. Their producer is subject to [ARH,
Proposition 2.1][ARH]; it may have unbounded worst acquisition cost despite
finite cost on each source. No producer is supplied without that cost or
without the stipulated complete cut.

The one actual register is at authenticated epoch $N$, at least every
recorded epoch. The target is the entire original $R_Q(u)$, including its
concrete exterior, reached original holes and complete equality partition.
Services are deterministic effective common programs, source-total on $D$,
using only physical $\mathsf{Read}$, same-register forward
$\mathsf{ApplyRho}$ and absorbing $\mathsf{Halt}$. There is no reset,
rerooting, cloning, unknown-subtree equality test, source-identity port or
uncharged source-dependent input. Read addresses and updates may depend
on replies. No common source size, depth, runtime or address bound is
assumed.

**Definition 1.2 (prices).** For a service $A$ and the same original source
$u$, let

$$
c_A(u)=(q_A(u),a_A(u),\ell_A(u)),\qquad
\ell_A(u)=\sum_{\text{actual reads }p}|p|.
\tag{CAR.4}
$$

Every actual $\mathsf{Read}$ call, including repetition and an absent
reply, contributes one to $q$. The coordinate $a$ counts only actual
post-entry $\mathsf{ApplyRho}$ calls; $\mathsf{Halt}$ contributes to neither
count. Define

$$
\begin{aligned}
b(A)&=(\sup_D q_A,\sup_D a_A,\sup_D\ell_A),\\
W_\lambda(A)&=\sup_{u\in D}
 (\lambda_q q_A(u)+\lambda_a a_A(u)+\lambda_\ell\ell_A(u)),
 \qquad \lambda\in\mathbb Q_{\ge0}^{3}.
\end{aligned}
\tag{CAR.5}
$$

The suprema in $b(A)$ need not have a common maximizer. The sum in
$W_\lambda$ always uses one source. Computation, installation, address
generation, storage, authentication, retention and physical time have
separate costs. Simulated events never constitute actual receipts.

**Definition 1.3 (supplied native coordinates).** Put $T_j=\rho^j\alpha$.
Use [ABC, Theorems 2.2–2.3][ABC]: every source has a unique normal atomic
code $B(u)$, whose primitive leaves $[j]$ expand to $T_j$. Its ordinary
binary constructor $F$ is retained except that native pairing uses

$$
J([j+1],[j])=[j+2],
\qquad J(X,Y)=F(X,Y)\text{ in every other case}.
\tag{CAR.6}
$$

Normality excludes the displayed collapsible pair everywhere. Forward
$\rho^a$ preserves the $F$ structure and adds $a$ to every primitive rank.
Expansion $E$ and $B$ are inverse on normal codes. In particular

$$
T_0=\alpha,\quad T_1=\beta,\quad
T_{j+2}=\langle T_{j+1},T_j\rangle,
\qquad \rho^a T_j=T_{j+a},
\tag{CAR.7}
$$

and $j\mapsto T_j$ is injective. These coordinates describe possible
sources; they are not accessible observer data.

The question treated below is a recognized part of [ARH, Definition
9.1][ARH]. Atomicity will be deduced from actual mandatory positive
constraints, rather than assumed for arbitrary sources. All remaining
signed constraints and all finite targets are then handled without a
synchronous-comparison restriction.

## 2. A native constructor-cycle certificate

**Definition 2.1 (constructor mass and occurrence edges).** Let
$\gamma(u)$ be the number of $F$ occurrences in $B(u)$. Thus
$\gamma(u)=0$ exactly when $u=T_j$ for some $j$, and
$\gamma(\rho^a u)=\gamma(u)$.

A normalized template is a finite expression built from concrete leaves,
ordered pairs and decorations $\rho^a(x)$, with powers distributed through
pairs as in [ARH, Definition 19.1][ARH]. Consider any conjunction of
mandatory positive equations between these templates. Cancel equal pair
heads to expose their two conjuncts. For each exposed equation that can
be oriented as

$$
\rho^a(x)=A,
\tag{CAR.8}
$$

put an edge $x\longrightarrow y$ for every occurrence $\rho^b(y)$ in
$A$. Mark the edge strict when that occurrence lies below at least one
pair constructor. When both orientations have a decorated-variable head,
include both. Duplicate edges cause no difficulty. Do not extract edges
from a disequality, an atom under a disjunction or negation, or a target
comparison whose truth has not been acquired.

A positive constructor cycle is a directed cycle containing a strict
edge. Its forward closure is the set of vertices reachable from any such
cycle, including its vertices.

**Theorem 2.2 (cycle-forced atomicity).** In every finite-tree solution of
the mandatory equations, all variables in the forward closure of positive
constructor cycles are atomic. The closure is effectively computable
from the finite equations. A cycle is not rejected as an occurs-check
failure.

Proof. Native pairing cannot hide a non-atomic child. If one child has
positive $\gamma$, the exceptional case of (CAR.6) cannot occur, and

$$
\gamma(\langle s,t\rangle)=1+\gamma(s)+\gamma(t).
\tag{CAR.9}
$$

If both children are atomic, the parent has mass zero or one, so its mass
is still at least each child mass. Along any descendant path, mass is
therefore nonincreasing. A proper descendant of positive mass has strictly
smaller mass than its ancestor: every pair above it is non-atomic and
contributes an additional $F$.

For an occurrence edge in (CAR.8), invariance under the decorations gives

$$
\gamma(x)\ge\gamma(y),
\quad\text{strictly if the edge is strict and }\gamma(y)>0.
\tag{CAR.10}
$$

On a directed cycle all these nonnegative integers must be equal. A
strict edge forces their common value to be zero. Every vertex downstream
then has mass at most zero. This proves the assertion simultaneously for
all solutions, with no bound on any tree. A finite directed graph has
finitely many strongly connected components. A strict edge whose endpoints
lie in one component lies on a directed cycle; mark those components and
take ordinary forward reachability. This computes exactly the indicated
closure. $\square$

**Proposition 2.3 (finite self-occurrence and a rejection boundary).**
The equation

$$
\rho(x)=\langle x,z\rangle
\tag{CAR.11}
$$

has finite solutions and forces both coordinates to be atomic. In
contrast, the equation $x=\langle x,z\rangle$ has no finite solution.
A bare equality $\rho^a(x)=\rho^b(y)$ alone does not force atomicity when
$a=b$.

Proof. Equation (CAR.11) gives a strict self-edge at $x$ and an edge to
$z$. Theorem 2.2 forces both. The actual assignment $(x,z)=(\beta,\alpha)$
is a solution by (CAR.1). More generally its complete scalar
classification is the supplied [ARH, Application 26.1][ARH26], not an
additional classification here. For the second equation leaf count gives
$\#\operatorname{leaves}(x)=\#\operatorname{leaves}(x)+
\#\operatorname{leaves}(z)$, which is impossible for nonempty trees.
For the last assertion choose $x=y=\langle\alpha,\alpha\rangle$;
this is non-atomic by (CAR.6), and the equation holds. $\square$

## 3. Complete observable charts and exact joint coordinates

**Definition 3.1 (finite certificate recognition).** An atomic-coverage
certificate is constructed from the retained input as follows.

Choose a sublist of the literal records and a sublist of the retained
positive relation records. Keep the entire old row, including all its
class inequalities. These choices define a *core* fiber containing $D$.
They are used only to derive a cover and atomicity; the final domain will
still be (CAR.3).

Apply either complete original-prefix cover of [ARH, Definition 19.3 and
Proposition 19.4][ARH] to this core, taking the auxiliary cut to be empty.
There are finitely many disjoint charts $\eta$. Each has a pure source
pattern $W_\eta(X_\eta)$, all core constraints, and a representative
original address for each frontier variable. The chart is determined
by finitely many original constructor questions and has a paid selector.

One may apply any finite schedule of the exact acyclic substitutions of
[ARH, Definition 20.2 and Proposition 20.3][ARH], without imposing its
synchronous residual eligibility test. Such a substitution requires a
mandatory positive equation $\rho^a(x)=A$, successful uniform factoring
$A=\rho^a(V)$, and no occurrence of $x$ in $V$. It substitutes in every
constraint and the source pattern. It removes one variable and retains
original representatives of the remaining variables. Stopping immediately
or after any permitted step is allowed.

Write the resulting source template as $F_\eta(Y_\eta)$. Use the graph of
Definition 2.1 on the remaining mandatory positive constraints. Require
its marked forward closure to contain every member of $Y_\eta$. Empty
$Y_\eta$ satisfies this condition. Charts rejected by an explicit sound
constant contradiction may be discarded. No unknown interpreted
constraint is treated as a contradiction.

The input is *cycle-covered* when some choice of core, complete cover and
substitution schedules meets this requirement on every surviving chart.
The recognizer searches these finite choices. Failure means that the
input is outside this family, not that recovery is impossible. The core
choice is common input data, never a choice based on the unknown source.

**Theorem 3.2 (termination, whole-fiber bijection and prefix directions).**
Cycle coverage is decidable. For a cycle-covered input there is an
effectively obtained finite list of coordinate domains

$$
S_\eta\subseteq\mathbb N^{Y_\eta},\qquad
\Theta_\eta(\mathbf n)=F_\eta[(T_{n_y})_{y\in Y_\eta}],
\tag{CAR.12}
$$

with finite dimensions and possibly infinite cardinalities. The map

$$
\coprod_\eta S_\eta\ \longrightarrow D,
\qquad (\eta,\mathbf n)\longmapsto\Theta_\eta(\mathbf n)
\tag{CAR.13}
$$

is a bijection. Its inverse on a concrete source selects its unique
original-prefix chart and reads the unique atomic indices at the remaining
original representatives. This inverse is effective on a supplied finite
source; it is not a free observer operation.

Write $u\equiv_h v$ when all original replies at $|p|<h$ agree. Put
$A_\eta=\max(\{0\}\cup\{|a_{\eta,y}|:y\in Y_\eta\})$. Then

$$
\begin{aligned}
(\forall y\ T_{n_y}\equiv_h T_{m_y})
 &\Longrightarrow
 \Theta_\eta(\mathbf n)\equiv_h\Theta_\eta(\mathbf m),\\
\Theta_\eta(\mathbf n)\equiv_{A_\eta+h}\Theta_\eta(\mathbf m)
 &\Longrightarrow
 (\forall y\ T_{n_y}\equiv_h T_{m_y}).
\end{aligned}
\tag{CAR.14}
$$

A finite computable original-prefix depth separates distinct surviving
charts. The chart selector uses actual current reads, with the two-read
historical decoder for each of its finitely many original questions.

Proof. The core choices are finite. Both cover constructions terminate
by the explicit split bound in ARH Definition 19.3. Each permitted
substitution removes a variable; its choices and factoring tests are
finite. Thus the complete search of schedules has finite depth and
branching. Pair cancellation, graph construction and reachability are
finite operations. This proves recognition termination independently of
a general cyclic unification decision.

The supplied cover and substitution propositions give a bijection from
finite assignments satisfying the core constraints to its entire source
fiber. Theorem 2.2 forces every remaining coordinate to be atomic in every
such assignment. Atomic index injectivity makes its tuple unique.

Define $S_\eta$ to impose the substituted core constraints together with
*every* original retained predicate, evaluated on $\Theta_\eta(\mathbf n)$
as in (CAR.2)–(CAR.3). An original $u\in D$ belongs to its unique core
chart and reconstructs all its finite coordinates, hence its unique index
tuple lies in $S_\eta$. Conversely a tuple in $S_\eta$ expands to a finite
source satisfying the exact old row and every retained predicate. In
particular no missing endpoint can satisfy a signed record. This proves
both inclusions and injectivity in (CAR.13). No source is replaced by an
independently selected marginal realization.

ARH Proposition 20.3 retains, at $a_{\eta,y}$, the original subtree
literally equal to the surviving coordinate $y$. Its Proposition 20.4
therefore applies with $y=T_{n_y}$ and proves both lines of (CAR.14).
Its argument only uses template prefix preservation and these literal
representatives, not synchronous residuals. The cover selector and the
finite separation depth are supplied by ARH Proposition 19.4 and remain
valid on the restricted sets $S_\eta$. $\square$

**Proposition 3.3 (arbitrary further signed information).** Once a core
certificate is available, arbitrary additional finite literal records,
signed guarded relations and finite prefix-free target cuts are permitted.
They require no additional atomicity or synchronous-comparison premise.
The representation (CAR.13) retains all these records jointly.

Proof. The previous core and its certificate remain among the finite
recognizer choices. Extra records only restrict $S_\eta$ and the target
cut does not occur in its construction. Theorem 3.2 imposes the records
in their original finite-tree meanings. Their effective interpretation,
including arbitrary whole-subtree comparisons, is proved next. $\square$

## 4. Arithmetic for all retained predicates and the entire row

**Lemma 4.1 (finite guarded arithmetic interpretation).** The following
objects are effectively expressible in first-order Presburger arithmetic
on the index coordinates:

1. each entire $S_\eta$;
2. existence, whole-subtree equality or disequality, and any of the four
   replies at arbitrary *fixed* finite epoch/address pairs;
3. equality of the complete rows
   $R_Q(\Theta_\eta(\mathbf n))$ and
   $R_Q(\Theta_\theta(\mathbf m))$, for any two charts;
4. equality of one such row with a supplied concrete finite row.

The interpretations use all natural-number indices without a rank bound.
Their predicates for a negative signed record include both endpoint guards.

Proof. Distribute all fixed powers in $F_\eta$. Its leaves become atomic
expressions $T_{n_y+c}$ or $T_c$, with nonnegative constant offsets. At
an additional epoch $a$ add $a$ to those indices. Ground parts are finite
pair templates over $T_0,T_1$; they need no unknown structure.

For a fixed address, follow the finite pair skeleton. At an atomic
expression $T_t$, split into the disjoint cases $t=0$, $t=1$ and $t\ge2$.
Only in the last case replace its children by $T_{t-1},T_{t-2}$ and consume
an edge. The first two cases block any further edge and yield absence.
Thus navigation is a finite case tree of depth bounded by the given
address length. Each case is guarded by linear equalities or inequalities,
and every reached expression has a nonnegative affine index. Negative
constants in intermediate affine notation are moved to the other side
of an inequality; there is no truncated-subtraction interpretation.
This gives exact existence, replies and reached finite templates.

Equality between any two such templates also has a finite arithmetic
interpretation. Normalize bottom-up using (CAR.6). At each pair of
primitive expressions $[r],[s]$, split into $r=s+1$ and $r\ne s+1$.
The former produces $[s+2]$, and the latter retains $F([r],[s])$.
Pairs with a nonprimitive child retain $F$. On each resulting arithmetic
case there is one fixed normal code shape with affine primitive ranks.
Two normal codes are equal precisely when these shapes agree and all
corresponding primitive ranks agree. ABC mutual recovery proves that
this is actual finite-tree equality, including equality between a
constructor expression and a decorated variable. Negate the resulting
whole equality formula for disequality; do not negate or omit its
independently required endpoint guards.

There are finitely many source terms and records. Conjoining the exact
old class inequalities, all substituted core conditions and all original
records gives item 1. Repeated classes use the same coordinates and
repeated records remain conjuncts, proving that this is a joint formula.

For the target, perform the same finite navigation along every original
$q\in Q$, at epoch zero. Each case fixes the reached subset and its
canonical address numbering. Expand atomic nodes only along the finite
requested paths. Replace each reached $Q$ subtree by a distinct numbered
hole marker and retain its whole-subtree expression separately. The
remaining exterior is a finite template of atomic expressions, concrete
pairs and those markers. Unvisited atomic pieces remain symbolic and
are not truncated.

Extend normal coding by treating hole markers as new, distinct leaves
that are never primitive ranks. A pair containing a marker cannot collapse
to an atomic block. The same inverse proof as ABC Theorem 2.2, with markers
fixed, shows that normalization by (CAR.6) is injective on the expanded
marked trees. Equality of the two exteriors is therefore the same finite
shape-and-rank comparison. Require equal reached address sets, equal
marked exteriors, and, for every pair of reached holes, equivalence of
the two whole-subtree equality predicates. These conditions are exactly
full-row equality. They preserve the entire partition, not just named
positive comparisons. Taking one side concrete gives item 4.

All case splits concern a fixed finite collection of expressions and
addresses. They do not split an unbounded unknown code or quantify over
ambient normal-code shapes. Empty $Q$ retains the entire source exterior;
$Q=\{\varepsilon\}$ gives a single-hole constant row. Blocked original
addresses never become target holes because navigation here is at epoch
zero. This proves all four items. $\square$

**Definition 4.2 (the arithmetic supplier).** Write
$\operatorname{Adm}_\eta(\mathbf n)$ for the formula of $S_\eta$, and
$\operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m)$ for the full-row
equality formula of Lemma 4.1. Finite chart quantification means a finite
disjunction or conjunction over their tags; the numeric tuples can have
different finite dimensions.

The decision supplier is Ginsburg–Spanier, *Semigroups, Presburger
Formulas, and Languages*, [Theorems 1.2–1.3][GS]: first-order Presburger
sentences over nonnegative integers are decidable, and their definable
sets are effectively semilinear. The present proof needs Theorem 1.2,
Boolean closure and quantification. After a true existential decision,
a witness tuple can also be obtained by enumerating natural tuples and
testing the fixed formula. This enumeration is used only after existence
has been decided positively. Theorem 1.3 additionally permits an exact
semilinear presentation of every $S_\eta$; no semilinearity theorem for
arbitrary native trees is asserted.

## 5. Effective bounded recovery and finite negative witnesses

**Lemma 5.1 (the exact atomic prefix relation).** For $i,j,h\in\mathbb N$,

$$
T_i\equiv_h T_j
\quad\Longleftrightarrow\quad
 i=j\ \lor\ (i\ge2h\ \land\ j\ge2h).
\tag{CAR.15}
$$

Proof. Equal indices give equal trees. Suppose $i<j$. At every address
of length less than $\lfloor i/2\rfloor$, the remaining index in both
trees is at least two: each edge subtracts at most two, and all those
edges have been traversed through branches. Thus both replies are branch
there. At $R^{\lfloor i/2\rfloor}$ the reply in $T_i$ is $\alpha$ when
$i$ is even and $\beta$ when $i$ is odd. The reply in $T_j$ differs:
its residual index is larger, giving $\beta$ or branch in the even case
and branch in the odd case. That address is reached in both trees by
(CAR.7). The first differing depth is therefore exactly
$\lfloor i/2\rfloor$, which is at least $h$ exactly when $i\ge2h$.
The case $j<i$ is symmetric. The root and $h=0$ are included. $\square$

**Theorem 5.2 (terminating necessary-and-sufficient full-row decision).**
For every nonempty cycle-covered fiber, a uniformly bounded-read legal
serial recovery service exists if and only if the following finitely
many Presburger sentences are all true:

$$
\exists h\ \forall\mathbf n\ \forall\mathbf m\quad
\left[
 \operatorname{Adm}_\eta(\mathbf n)\land
 \operatorname{Adm}_\eta(\mathbf m)\land
 \bigwedge_{y\in Y_\eta}
 \bigl(n_y=m_y\ \lor\ (n_y\ge2h\land m_y\ge2h)\bigr)
 \ \Longrightarrow\
 \operatorname{Same}_{\eta\eta}(\mathbf n,\mathbf m)
\right].
\tag{CAR.16}
$$

The criterion is decidable with effective positive and negative outcomes.
A positive outcome yields an entry-static source-total service, with
finite paid upper budgets and no new equality operation. A negative
outcome yields, for every requested original depth $d$, two actual finite
sources in the same entire $D$, agreeing at all $|p|\le d$ and having
different complete $Q$ rows. In particular a negative outcome excludes
every legal adaptive serial service with a uniform finite raw bound.

Proof. Sentences (CAR.16) belong to the arithmetic of Definition 4.2;
$h$ is quantified inside that decidable theory, not searched until a
negative timeout. If a sentence is true, extract a witnessing $h_\eta$.
If $S_\eta$ is empty its sentence is vacuous and $h_\eta=0$ suffices.

Let $b_{\rm sel}$ be a strict-depth prefix bound determining the chart,
and put

$$
b=\max\bigl(\{b_{\rm sel}\}\cup
 \{A_\eta+h_\eta:\eta\text{ a surviving chart}\}\bigr).
\tag{CAR.17}
$$

If two sources in $D$ agree below depth $b$, they have the same chart.
The second direction of (CAR.14) and (CAR.15) make their coordinate
pairs satisfy the antecedent of (CAR.16). Their complete rows are equal.
Thus (CAR.17) is a sufficient *original* prefix bound, including the
observable separation of the chart union.

Conversely, suppose an original prefix of strict depth $b$ determines
the full row on $D$. In any chart take $h=b$. The first direction of
(CAR.14), together with (CAR.15), makes the antecedent of (CAR.16) imply
agreement of the two original prefixes, so it implies equal rows.
Therefore each sentence is true. This proves both original-prefix
directions without a semantic chart oracle.

The operational equivalence between original-prefix determination and
bounded static or serial existence is [ARH, (2.3)][ARH]. Its domain
hypotheses are the common complete entry, finite sources, physical
locality, four replies and source-totality of Assumption 1.1, not a
literal-only feasibility premise. For an explicit positive service,
recover every original reply of length less than $b$ using [SLH,
Theorem 2.2][SLH] at the actual entry epoch $N$. Each original question
needs at most two actual current reads of length at most
$b-1+\lceil N/2\rceil$ when $b>0$. Hence one available upper bound is

$$
K_0=2(2^b-1),\qquad a=0,\qquad
L_0=K_0\max(0,b-1+\lceil N/2\rceil).
\tag{CAR.18}
$$

When $b=0$ there are no questions and $K_0=L_0=0$.
For each possible original-prefix reply vector, use Lemma 4.1 and
Definition 4.2 to decide whether some source in the entire chart union
has that vector. For a nonempty vector extract one finite coordinate
witness, expand it and calculate its whole $Q$ row. Formula (CAR.17)
makes the row independent of that witness. Install these finite outputs;
unreachable vectors may receive any output. The actual decoder replies
select the correct output and the service halts. The witnesses are used
in constructing a common table, not supplied as the actual source.
Only the actual current decoder reads are new receipts.

If a sentence (CAR.16) is false, select that chart. For any given $d$ set
$h=d+1$. Its negation supplies finite natural tuples satisfying the whole
antecedent but different full rows. This existential formula is decidable
and true, so its finite witness extraction terminates. Expand the tuples
by (CAR.12). The first implication of (CAR.14) proves agreement at every
$|p|\le d$; (CAR.13) and the failed row equality put both sources in the
same full $D$ with unequal target rows. No infinite-tree realization is
used. ARH (2.3) excludes a uniform-read serial service. $\square$

**Proposition 5.3 (finite image is only a consequence).** A positive
(CAR.16) permits effective construction of the finite image $R_Q(D)$.
Finiteness of this image is not a premise of the decision, and does not
conversely imply it.

Proof. The finite prefix table in Theorem 5.2 gives the image exactly;
all its nonempty entries have actual-source witnesses. Proposition 9.1
below gives a fiber with finite image and negative (CAR.16). $\square$

## 6. A global interface for every physical word

**Definition 6.1 (common skeleton depth and physical descriptors).**
For each chart, write its reconstructed source as a fixed finite full
binary pairing skeleton whose leaves are $T_{n_y+c}$ or $T_c$.
Ground leaves can always be $T_0,T_1$. This is an expansion template,
not necessarily the maximal normal skeleton. Let $H$ be the maximum
leaf-address length over these finitely many skeletons.

A physical descriptor is either a literal word $p$ with $|p|\le H$, or

$$
(z,t,l,e),\qquad |z|=H,\quad e\in\{L,R\},\quad l\ge1,
\quad l-1\le t-\omega(e)\le2(l-1),
\tag{CAR.19}
$$

where $\omega(L)=1$, $\omega(R)=2$. Its length is $|p|$ in the first
case and $H+l$ in the second. It represents the words $zs$ where $s$
has length $l$, weight $t=\#_L(s)+2\#_R(s)$ and last edge $e$.
There is no upper bound on $l$ or $t$.

**Theorem 6.2 (global realizability, replies and exact physical lengths).**
Every finite physical word has a descriptor. Every descriptor has an
effectively constructible realizing word of exactly its stated length.
There are Presburger predicates

$$
\operatorname{Reply}_{\eta,c}(\mathbf n,j,\delta),
\qquad c\in\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\},
\tag{CAR.20}
$$

for arbitrary epochs $j\ge0$, such that any realization $p$ of $\delta$
satisfies, simultaneously for every chart and all its admitted tuples,

$$
\operatorname{Reply}_{\eta,c}(\mathbf n,j,\delta)
\quad\Longleftrightarrow\quad
r_{\rho^j\Theta_\eta(\mathbf n)}(p)=c.
\tag{CAR.21}
$$

Thus one descriptor has one reply function on the *entire* chart union
at every actual epoch. Its realization does not depend on the chart,
source, index tuple or reply. The descriptor interface preserves sourcewise
read counts and physical lengths exactly when replacing a read by a
realizing word.

Proof. Short words are literal descriptors. For $|p|>H$, factor uniquely
$p=zs$ with $|z|=H$ and $|s|=l>0$; take its actual weight and last edge.
The first $l-1$ letters have weights between $l-1$ and $2(l-1)$, proving
(CAR.19). Conversely put

$$
r=t-\omega(e)-(l-1),\qquad
s=R^rL^{l-1-r}e.
\tag{CAR.22}
$$

The descriptor inequalities say $0\le r\le l-1$. This word has exactly
the prescribed length, weight and last edge, so $zs$ is a genuine physical
request of length $H+l$.

Short-word replies are computed by the finite navigation of Lemma 4.1,
with $j$ a variable added to each rank. Its case guards remain linear.
This includes the root, reached leaves, branches and absence at short
addresses, even at epochs zero and one.

For a long descriptor fix a chart. Following the fixed word $z$ through
its *skeleton*, one reaches a unique skeleton leaf at a prefix $a$ of $z$,
since every skeleton leaf has depth at most $H$. Write $z=ab$. Let $k$
be that leaf rank expression, either $n_y+c$ or $c$. This traversal is in
the finite template only; it does not assert that $z$ is reached in the
expanded physical tree. The physical suffix after $a$ is $bs$, is
nonempty, has weight $w(b)+t$, and ends in $e$.

The exact supplied atomic guard [ARH, (4.3)][ARH] gives

$$
\begin{aligned}
bs\in\operatorname{Pos}(T_{k+j})
 &\Longleftrightarrow
 k+j-w(b)-t\ge2-\omega(e),\\
T_{k+j}|_{bs}&=T_{k+j-w(b)-t}\quad\text{when reached}.
\end{aligned}
\tag{CAR.23}
$$

All preceding edge weights are positive. Consequently the final-parent
condition in (CAR.23) ensures every earlier parent was a branch; if it
fails, the request is absent, including failure before the end of $z$.
Let $v=k+j-w(b)-t$. The reply is absent when $v<2-\omega(e)$; otherwise
it is $\alpha$ for $v=0$, $\beta$ for $v=1$, and branch for $v\ge2$.
The existence guard is retained in the $v=0$ case: a word ending in $L$
can have residual zero and still be absent. These mutually exclusive
cases cover all possibilities, and are linear arithmetic formulas.

The same $z,t,l,e$ is used in every chart, although its leaf prefix $a$
and rank expression can differ. Formula (CAR.23) proves (CAR.21) separately
in each chart with the same realizing word (CAR.22). It holds for every
natural $j$ at once, not just for one chosen epoch. No hidden rank or
chart is used in realizing the word. Actual read count is one and its
length is precisely the descriptor length. $\square$

**Proposition 6.3 (why a bare suffix summary is insufficient).** Weight
and last edge alone do not determine a physical reply on arbitrary
non-atomic sources. The finite common prefix in Definition 6.1 is part
of the global interface.

Proof. The words $LRL$ and $RLL$ both have weight four and last edge $L$.
In

$$
u=\langle\langle\alpha,\langle\alpha,\alpha\rangle\rangle,
             \langle\langle\beta,\alpha\rangle,\alpha\rangle\rangle
$$

their replies are respectively $\alpha$ and $\beta$. This source is
non-atomic, since $LRL$ ends in $L$ and no atomic tree has an $\alpha$
reply at a word ending in $L$, by (CAR.23). Theorem 6.2 applies the suffix
summary only after a proved atomic skeleton leaf, and keeps the common
prefix needed to locate that leaf in every chart. $\square$

## 7. Exact effective serial feasibility

**Definition 7.1 (finite arithmetic reply trees).** Put

$$
M=\max(N,5),\qquad U=M-N.
\tag{CAR.24}
$$

A skeleton of read depth at most $k$ is a finite four-reply tree whose
vertices are reads or absorbing halts. A read vertex has an epoch
$j_v\in[N,M]$, nondecreasing along each path, and a descriptor $\delta_v$
of Definition 6.1. All its numeric descriptor parameters are selected
before universal source quantification. Chart identity and rank tuples
are not controller inputs. Before each read the controller performs the
actual nonnegative difference from its preceding epoch.

For a halt $t$, let $k_t$ count preceding reads, $j_t$ be the last read
epoch or $N$ at a root halt, and $L_t$ the sum of descriptor lengths.
Its actual path cost is

$$
(k_t,j_t-N,L_t).
\tag{CAR.25}
$$

Let $\operatorname{Path}_{\eta,t}(\mathbf n;\boldsymbol\delta)$ be the
conjunction of the appropriate reply predicates (CAR.20) along that
path. The exact correctness condition is

$$
\bigwedge_{\eta,\theta,t}\ \forall\mathbf n\ \forall\mathbf m\quad
\left[
\begin{array}{l}
\operatorname{Adm}_\eta(\mathbf n)\land
\operatorname{Adm}_\theta(\mathbf m)\land
\operatorname{Path}_{\eta,t}(\mathbf n;\boldsymbol\delta)\land
\operatorname{Path}_{\theta,t}(\mathbf m;\boldsymbol\delta)
\end{array}
\Longrightarrow
\operatorname{Same}_{\eta\theta}(\mathbf n,\mathbf m)
\right].
\tag{CAR.26}
$$

A leaf is reachable exactly when

$$
\operatorname{Reach}_t(\boldsymbol\delta)\iff
\bigvee_\eta\exists\mathbf n\,
 (\operatorname{Adm}_\eta(\mathbf n)\land
  \operatorname{Path}_{\eta,t}(\mathbf n;\boldsymbol\delta)).
\tag{CAR.27}
$$

Thus distinct charts may terminate together if their full rows coincide.
The target is not refined to chart identity, a prefix vector or an atomic
coordinate tuple.

**Theorem 7.2 (two paid comparator directions and terminating feasibility).**
For every cycle-covered nonempty input and integers $k,d,L\ge0$, both
questions below are decidable:

$$
\begin{aligned}
&\exists A\quad\sup_Dq_A\le k,\quad\sup_Da_A\le d;\\
&\exists A\quad b(A)\le(k,d,L).
\end{aligned}
\tag{CAR.28}
$$

The first question puts no bound on physical address lengths. Each true
answer yields a finite actual source-total service within the budgets.
These decisions compare with every legal adaptive serial competitor of
Assumption 1.1.

More generally, for any fixed read-depth bound and nonnegative rational
weights, a threshold on the same-source weighted costs of all reachable
paths is decidable, including zero weights and unbounded descriptor
lengths.

Proof. The all-source cap of [JRF, Theorem 3.1][JRF] applies without any
source-language premise. Its Lemma 2.2 preserves all four replies for
arbitrary physical words on every finite source. Thus, for every original
comparator $A$, the capped comparator satisfies on each same source

$$
q_{A^c}=q_A,\qquad a_{A^c}=\min(a_A,U),\qquad
\ell_{A^c}\le\ell_A.
\tag{CAR.29}
$$

It retains the original actions before the cap, including early epochs
zero through four and early halt. Simulated later events are local
control only. This is the joint nonexpansive supplier; the additive
address bound of [SCR, §§9–10][SCR] is not used as a substitute.

For necessity, take a comparator meeting either requested budget and
cap it. Remove actual updates after its last read on a halting branch,
retaining any needed simulated epoch in its local computation. This
cannot affect any later source reply, since there is no later read.
Unroll its reachable reply prefixes. There are at most
$1+4+\cdots+4^k$ such prefixes. At each reachable prefix, the deterministic
segment up to the next read or halt is fixed by the common acquired state
and the preceding replies; it is finite because at least one source
reaches it and the program is source-total there. Hence the unrolling
has fixed finite read words and monotone epochs in
$[N,N+\min(d,U)]$. Install an immediate halt on unreachable children.
No algorithm extracting reachability from arbitrary program text is
required for this existence implication.

Replace each word by its descriptor. Theorem 6.2 preserves its replies
on every chart at every epoch and its physical length exactly. Therefore
(CAR.26) holds and (CAR.25) is its same-source cost. For every reachable
leaf impose $k_t\le k$, $j_t-N\le d$, and, when required, $L_t\le L$.
All-comparator necessity follows without a source, rank or address cutoff.
Repetitions and absent calls are permitted vertices, and early halts
remain unpadded halts.

For decision, enumerate the finite tree shapes of depth at most $k$,
the finitely many epoch labels, and each descriptor type: a short literal
word, or a choice of $z,e$ for a long descriptor. Its unbounded $t,l$
are existential natural variables subject to (CAR.19). Conjoin (CAR.26)
and, for each leaf, the implication from (CAR.27) to its budget
inequalities. Every clause is Presburger by Lemma 4.1 and Theorem 6.2.
Quantify all descriptor variables outside the source quantifiers and
decide the finite disjunction. The length-unbounded question simply
omits the length inequalities; it is the same terminating arithmetic
decision, not an unbounded enumeration of word lengths.

For sufficiency, extract a satisfying descriptor tuple after a true
decision and realize its physical words by (CAR.22). At each reachable
leaf, extract a source tuple from (CAR.27), expand that finite source
and compute its complete $Q$ row. Formula (CAR.26) makes this the same
row for every source reaching the leaf, across all charts. Install that
finite output; unreachable leaves receive arbitrary outputs. Execute
the actual forward epoch differences and reads and then halt. Induction
on the received replies puts the actual source in its path formula and
at a reachable leaf. The output is correct and the path costs are exactly
(CAR.25). All runs are finite. This constructs the legal paid comparator
in the reverse direction.

For a rational threshold $z$, replace the budget inequalities by

$$
\operatorname{Reach}_t\ \Longrightarrow\
\lambda_q k_t+\lambda_a(j_t-N)+\lambda_\ell L_t\le z.
\tag{CAR.30}
$$

Clear denominators. The formula remains Presburger even if some weights
are zero and there is no length bound. The same two operational directions
prove its threshold meaning. $\square$

**Corollary 7.3 (exact costs and common-source witnesses).** For a finite
service constructed in Theorem 7.2, exact coordinatewise worst budgets
and every rational same-source weighted worst cost are computable.
Each finite maximum has an actual source witness. The maximizing sources
for different coordinates can differ.

Proof. Decide (CAR.27) for each of its finitely many leaves. Every
nonempty leaf has the fixed cost (CAR.25) and a finite source witness;
all sources follow one such leaf. Maximize coordinates separately for
$b$, or first sum the three coordinates on each leaf and then maximize
for $W_\lambda$. Nonemptiness of $D$ ensures a nonempty set of reachable
leaves. $\square$

## 8. Attained frontiers and weighted optima by matched reuse

**Theorem 8.1 (effective exact resource consequences).** On the recognized
family, Theorem 5.2 and Theorem 7.2 supply the decision interfaces needed
for the resource conclusions of JRF. In particular let

$$
\mathcal F=\{b\in\mathbb N^3:\exists A\ b(A)\le b\}.
\tag{CAR.31}
$$

If (CAR.16) fails, $\mathcal F$ is empty. If it holds, there is an
effectively computable nonempty finite set $\mathcal B$ with

$$
\mathcal F=\{b:\exists v\in\mathcal B\ v\le b\},
\qquad \mathcal B=\operatorname{Min}(\mathcal F).
\tag{CAR.32}
$$

Every $v\in\mathcal B$ is the exact worst-budget vector of a constructible
finite actual service. For every $\lambda\in\mathbb Q_{\ge0}^3$,
$\inf_A W_\lambda(A)$ is effectively computable in
$\mathbb Q_{\ge0}\cup\{\infty\}$ and is attained by a source-total actual
service. When (CAR.16) holds a finite reply tree attains it, including
all zero-weight cases.

These optimization conclusions reuse [JRF, §§3, 5 and 7][JRF] with the
newly proved logical and physical suppliers, rather than applying its
literal-history WS2S supplier to (CAR.3).

Proof. The source-independent ingredients of JRF are its cap (CAR.29),
its cleanup Lemma 3.2 and its finite cofinal argument. Cleanup gives the
sourcewise bound

$$
q\le\ell+s_N,\qquad s_N=\max(0,2-N),
\tag{CAR.33}
$$

by caching repeated actual epoch/address replies and omitting universally
branch root replies at epochs at least two. Those hypotheses are unchanged
here. The exact replacements for its domain-specific ingredients are:
(CAR.13) for entire-fiber realization, Lemma 4.1 for the full-row terminal
predicate, Theorem 5.2 for boundedness and a paid static supplier,
Theorem 6.2 for unbounded physical addresses and lengths, and Theorem 7.2
for exact feasible skeletons and same-source reachability. Both positive
and negative directions of every replacement have been proved on (CAR.3).

For completeness, the finite stopping calculation from JRF is as follows.
When (CAR.16) holds take $(K_0,0,L_0)$ from (CAR.18) and set

$$
K=\max(K_0,L_0+s_N).
\tag{CAR.34}
$$

The argument of JRF Lemma 5.2 now applies: every finite-worst-budget
comparator is weakly dominated in those worst budgets by a finite service
with read budget at most $K$ and update budget at most $U$. Indeed cap
and clean first. If its worst raw cost exceeds $K$, (CAR.33) makes its
worst length exceed $L_0$, while its worst raw cost exceeds $K_0$; the
static supplier dominates its three suprema. Otherwise its finite raw
bound permits the exact finite unrolling of Theorem 7.2. The static
replacement in this argument compares coordinate suprema, not individual
source profiles.

For each of the finitely many $(k,d)\in[0,K]\times[0,U]$, first decide
the length-unbounded question in (CAR.28). Discard a false pair. For a
true pair extract a service and its finite worst length $L^{\rm wit}$.
Test $0\le L\le L^{\rm wit}$ to find its least feasible length. Retain
these feasible triples and their witnesses, then remove dominated triples.
The cofinal argument proves (CAR.32). At a minimal feasible upper triple,
a witnessing service must attain every coordinate of the triple in its
worst vector, since a strictly smaller vector would itself be feasible.
Corollary 7.3 supplies the maxima and witnesses. False pairs never start
an unbounded witness search; this proves effective stopping, rather than
appealing to Dickson finiteness alone.

For weighted optimization use the same-source argument of JRF Theorem
7.1, not the finite Pareto list. When $\lambda_q+\lambda_\ell>0$ and
(CAR.16) holds, set

$$
B_0=\lambda_qK_0+\lambda_\ell L_0.
\tag{CAR.35}
$$

Cap and cleanup are sourcewise nonexpansive, hence nonexpansive for
$W_\lambda$. A comparator of weighted worst cost at most $B_0$ can be
restricted to read depth

$$
k_\lambda=
\begin{cases}
\lfloor B_0/\lambda_q\rfloor,&\lambda_q>0,\\
\lfloor B_0/\lambda_\ell\rfloor+s_N,&\lambda_q=0,\ \lambda_\ell>0.
\end{cases}
\tag{CAR.36}
$$

The second case uses (CAR.33). Epochs lie in $[N,M]$. Test (CAR.30) at
this depth over the finite lattice of rational thresholds from zero to
$B_0$, with a common denominator of the three weights. Every finite
run has a cost in this lattice; a bounded nonempty subset has a maximum
in the same lattice. The first true threshold therefore equals the
infimum, and Theorem 7.2 constructs a service attaining it. This proof
also covers $B_0=0$. A zero length weight leaves the descriptor lengths
unbounded in the arithmetic formula and causes no termination problem.

For all remaining cases, use the supplied pointwise-total static
whole-original-tree traversal: the historical literal decoder reads the
original root, recursively reads children only after an original branch,
and stops at original leaves. Each actual original source is finite,
so this terminates, computes its entire row and uses zero actual updates.
If $\lambda_q=\lambda_\ell=0$, it attains price zero; in the bounded case
the finite static supplier does so as well. If (CAR.16) fails, ARH (2.3)
forces infinite worst raw cost for every correct service, and (CAR.33)
forces infinite worst length. Thus any positive raw or length weight
has value $\infty$, attained as a supremum by the static traversal.
No individual run is infinite. Finally boundedness failure excludes
all finite triples in (CAR.31). $\square$

**Corollary 8.2 (extended budgets).** Allowing infinite coordinates in an
upper budget, the feasible set in the bounded case is the upward closure
of the same $\mathcal B$. In the unbounded case it is exactly

$$
\{(\infty,d,\infty):d\in\mathbb N\cup\{\infty\}\},
\tag{CAR.37}
$$

with the minimal extended vector $(\infty,0,\infty)$ attained by the
static whole-source traversal.

Proof. This is the argument of JRF Corollary 5.5 with the matched suppliers
in Theorem 8.1. A finite raw bound gives a finite reachable reply tree and
therefore finite worst lengths and deterministic update segments. A finite
length bound gives a finite raw bound after cap and cleanup. If both raw
and length bounds are infinite, the static supplier in the bounded case
fits any nonnegative update bound. In the unbounded case both indicated
coordinates must be infinite and the zero-update traversal attains the
remaining bound. $\square$

## 9. A coupled acquired-input obstruction and a paid positive restriction

**Proposition 9.1 (separate local constancy does not recover the joint row).**
Let the old source row have pattern

$$
u=\langle\langle x,\langle x,z\rangle\rangle,
               \langle y,\langle y,w\rangle\rangle\rangle,
\tag{CAR.38}
$$

at old cut

$$
P=\{LL,LRL,LRR,RL,RRL,RRR\}.
$$

Its complete old partition repeats $x$ at the first two indicated left
positions, repeats $y$ at its two right positions, and makes the four
classes $x,z,y,w$ pairwise different. Acquire the two positive relations
and the cross-sector negative relation

$$
(1,LL,0,LR,=),\qquad
(1,RL,0,RR,=),\qquad
(0,LL,0,RLLR,\ne).
\tag{CAR.39}
$$

Also acquire the literal branch replies at epoch zero at $LRRR$ and
$RRRR$. The entire resulting fiber is exactly

$$
\begin{gathered}
 u_{m,n}=\langle V_m,V_n\rangle,
 \qquad V_j=\langle T_{j+1},\langle T_{j+1},T_j\rangle\rangle,\\
 m,n\ge4,\qquad |m-n|\ge2,\qquad n\ne m+3.
\end{gathered}
\tag{CAR.40}
$$

This is cycle-covered, has two unbounded jointly constrained coordinates,
and has no required acquired whole-root/proper-descendant certificate.
For the original target

$$
Q=\{LL,LRL,LRR,RLLL,RLLR,RLR,RR\},
\tag{CAR.41}
$$

the entire output image is finite, each sector separately has a constant
local row, but the joint full row has no uniform finite-read recovery
service at any allowed entry epoch.

Proof. The positive records have reached endpoints and say precisely
$\rho(x)=\langle x,z\rangle$ and
$\rho(y)=\langle y,w\rangle$. Their scalar solutions are reused from
ARH Application 26.1, giving $x=T_{m+1},z=T_m$ and
$y=T_{n+1},w=T_n$ for unique $m,n\ge0$. In the cycle graph there are
strict self-edges at $x,y$ and outgoing edges to $z,w$, so it covers all
four coordinates. No additional skeleton promise has been made.

The two literal branch records inspect the right children of $T_m,T_n$.
By the atomic guard, branch there is exactly $m,n\ge4$. The four old
classes are pairwise different exactly when the two adjacent-index sets
$\{m,m+1\}$ and $\{n,n+1\}$ are disjoint, namely $|m-n|\ge2$.
The last record in (CAR.39) compares $T_{m+1}$ with $T_{n-2}$ at reached
endpoints, and hence is exactly $n\ne m+3$. This proves both inclusions
in (CAR.40), including the full old partition and all three records.
The extra negative record is a genuine coupling of the two local sectors.
ARH Proposition 2.1 supplies the paid finite sourcewise acquisition of
these records under the complete-state condition.

Every address in (CAR.41) is reached. Its ordered hole values are

$$
T_{m+1},\ T_{m+1},\ T_m,\
T_{n-1},\ T_{n-2},\ T_{n-1},\ T_{n+2}.
\tag{CAR.42}
$$

The last identity uses $\langle T_{n+1},T_n\rangle=T_{n+2}$.
The marked exterior consists only of the fixed pair structure above
these seven holes. Within the left three holes the first two are equal
and the third is different. Within the right four holes the first and
third are equal and the other two indices are distinct. Thus each local
row is constant, while the joint row additionally requires cross-sector
equalities. There are only finitely many partitions of seven holes,
so its image is finite.

For arbitrary $d$, choose $m\ge\max(4,2(d+1))$. Both
$u_{m,m+2}$ and $u_{m,m+4}$ lie in (CAR.40). Their left sectors agree.
The corresponding atomic indices in their right sectors are at least
$2(d+1)$, so (CAR.15) and template prefix preservation give agreement
of the two whole original trees at every $|p|\le d$.
In the first source, the first and fourth holes in (CAR.42) are equal;
in the second they are not. Their full rows differ. These are finite
same-fiber witnesses for every requested depth, so ARH (2.3) rules out
bounded raw recovery at every allowed $N$. This also proves the final
assertion of Proposition 5.3. $\square$

**Proposition 9.2 (an infinite coupled fiber with a one-read consumer).**
Add to Proposition 9.1 the epoch-zero literal record

$$
(0,LRRRRL,\mathsf{absent}),
\tag{CAR.43}
$$

and take authentic entry $N=1$. The entire fiber is now (CAR.40) with
$m\in\{4,5\}$. Its target has exactly two full rows, and one actual read
at the physical address $R^7$ at epoch one recovers the full row:
$\mathsf{absent}$ or $\alpha$ selects the row with the cross-sector
equalities, and $\beta$ or branch selects the row without them. This
has exact costs $(q,a,\ell)=(1,0,7)$ on every source and optimal raw
cost one. No equality call or coordinate read is used.

Proof. The added address is the old $z$ address $LRR$ followed by $RRL$.
In $T_m$, that nonempty suffix is reached exactly when
$m\ge w(RR)+2=6$. Its absence, together with $m\ge4$, gives precisely
$m=4$ or $m=5$.

Combining $n\ge4$, $|m-n|\ge2$ and $n\ne m+3$ gives

$$
n=m+2\quad\text{or}\quad n\ge m+4.
\tag{CAR.44}
$$

In (CAR.42), the first case equates left holes 1 and 2 with right holes
4 and 6, and left hole 3 with right hole 5. In the second case all
cross-sector equalities are false. The local equalities and the concrete
exterior remain fixed, so these are exactly two full rows. Both occur,
for example at $(m,n)=(4,6)$ and $(4,8)$.

The actual address $R^7$ enters $w$ after its prefix $RRR$, leaving
suffix $R^4$. At epoch one this reads $T_{n+1}$ with suffix weight eight
and last edge $R$. It is absent for $n=6$, gives $\alpha$ for $n=7$,
$\beta$ for $n=8$, and branch for $n\ge9$. All admitted $n$ are at least
six. Under (CAR.44), $n=6,7$ is exactly the first case and $n\ge8$ is
exactly the second. The stated one-read controller therefore has the
claimed output and paid costs, including absence as a useful actual
reply. A zero-read controller has the same common input on these two
outputs; deterministic updates supply no replies. It cannot output
both rows correctly. Hence the raw optimum is one. $\square$

## 10. Exact supplier boundaries and the unforced structural gap

**Proposition 10.1 (scope of the arithmetic extension).** The new
inferences are the native mass certificate of Theorem 2.2, its whole-fiber
combination with observable charts, the quantified prefix decision for
joint atomic coordinates, and the global physical-word interface feeding
exact serial feasibility. The optimization in §8 is a consequence of
those interfaces and the existing all-source operational arguments.
The following supplier identifications hold at their stated hypotheses.

| Supplier | Use and mathematical boundary |
| --- | --- |
| [ABC §§2–6][ABC] | Native $B/E$ bijection, smart pairing, rank shift and paid coordinate correspondence on all finite trees; these alone do not decide an unrestricted signed fiber. |
| [ARH §§19–25][ARH] | Complete original-prefix charts, paid selector, sound acyclic substitution and both prefix directions. The present recognizer uses no synchronous residual assumption after its atomicity certificate. |
| [ARH §26][ARH26] | Exact scalar feedback and root-exchanged single-orbit application. The scalar factors in §9 are reused; the entire coupled signed fiber and its joint row are treated here. |
| [AOF][AOF] | Acquired whole-root/proper-descendant certificate resources. Its entry-static nonexpansive normalization is not assumed for the local multi-coordinate fibers here. |
| [JRF §§2–3, 5, 7][JRF] | All-source epoch-five cap, cleanup and cofinal/weighted optimization arguments. Its literal-only WS2S and boundedness supplier is replaced by §§4–7, with both original-source and paid comparator directions. |
| [SCR §§9–10][SCR] | Epoch-four universal raw transport has an additive address bound; it supplies no joint nonexpansive replacement for (CAR.29). |
| [Ginsburg–Spanier, Theorems 1.2–1.3][GS] | Decision and effective semilinearity for the explicit finite-dimensional arithmetic formulas, including quantified $h$, unbounded word descriptors and jointly quantified source tuples. |

Proof. The first two rows have their parameter correspondence in
Definitions 1.3 and 3.1 and Theorem 3.2. All coordinate variables are
actual original subtrees before indexing, and (CAR.13) proves both domain
inclusions. Proposition 9.1 explicitly separates its scalar classification
from the new joint constraints. AOF assumes a retained positive whole-root
certificate, absent from that construction; no AOF theorem is needed to
infer its resource properties. Equation (CAR.29) uses the all-source JRF
cap exactly at $M=\max(N,5)$, preserving early actions. Theorem 6.2 and
(CAR.26)–(CAR.30) provide the new domain and action formulas required by
its subsequent arguments. Definition 4.2 and formulas (CAR.16), (CAR.19)
show that the arithmetic supplier receives only first-order natural
addition, order, constants and quantifiers. No arbitrary-tree predicate
is passed to it without the proved interpretation. $\square$

**Definition 10.2 (other representations and the remaining obligation).**
The native source identification in
[SourceTransportCentralizer, `source_transport_centralizer`][CENTRALIZER]
is $\alpha=\mathtt{of\ true}$, $\beta=\mathtt{of\ false}$ and pairing
$\mathtt{FreeMagma.mul}$. Its stability classification and injectivity
are compatible with the atomic supply. Its local orbit and classification
arguments do not supply a solver for arbitrary coupled signed equations.
[SourceTreeEncoding, `source_code_equiv`][ENCODING] is a bijection for
finite natural-leaf trees and hereditary-finite codes; it does not supply
the physical descriptor or quantified prefix criterion above.

The pinned mathlib [free magma][FREE] and [first-order syntax][SYNTAX]
provide free constructors and substitution syntax. They do not change
the interpretation (CAR.1). The paid acquisition and actual-trace
interfaces in [ActualTreeReadoutAcquisition][ACQUISITION] and
[ActualExactTraceCompiler][TRACE] retain their separate hypotheses. The
former defines `paid` by distinct addresses for its `Positive` task. The
latter’s `strategy_exact_run` assumes a positive bound, `Allowed N U`, and
coarse policy factorization. Neither replaces the raw-call cost (CAR.4)
or the whole-fiber comparator argument of Theorem 7.2. None gives the
observer free ranks or a new subtree-equality action.

Kuncak–Rinard, [*On the Theory of Structural Subtyping*, §§6.1–6.4][KR],
works in its specified term-power language. [TPO, Theorem 4.1 and
Corollaries 4.2 and 4.4][TPO] exclude the proposed uniform native
normal-domain/canonicalization supplier in that exact language. The
finite arithmetic case normalization in Lemma 4.1 instead has a fixed
finite template and finitely many rank coordinates. It asserts no
normal-domain definition over unbounded ambient code shapes.

Marshall–Meadows–Narendran, [*On Unification Modulo One-Sided
Distributivity: Algorithms, Variants and Asymmetry*, §5][MMN], treats its
single-homomorphism equational presentation. Native (CAR.1) additionally
interprets the constants and admits the finite self-occurrence in
Proposition 2.3. No occurrence-cycle rejection or decision is imported
from that presentation without an exact native interpretation.

For inputs where no complete certificate forces the remaining structures
to be atomic, the unrestricted [ARH, Definition 9.1 and Definition
24.3][ARH] obligation remains: decide full-original-row prefix boundedness
on arbitrary entire nonempty signed fibers, provide effective negative
stopping by finite original-source witnesses, and supply a matching
global physical-address feasibility interface for those fibers. The
structural $B/E$ correspondence alone does not bound their non-atomic
skeletons. The common $H$ used in Theorem 6.2 has then not been obtained,
and the finite-dimensional arithmetic proof above does not apply.
Recognition failure proves neither non-recovery nor undecidability.
These are statements about the fixed finite-tree mathematical model;
no physical realization or global novelty assertion is included.

[ABC]: https://github.com/the-omega-institute/trureturing/blob/5acc53740f311d7a854d03f793e4079aa626fe5c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[ARH]: https://github.com/the-omega-institute/trureturing/blob/ce58f3e6607e4269821891c7ba7e7dad5e8066f9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ARH26]: https://github.com/the-omega-institute/trureturing/blob/6b846a580ce10d8a9c6a436b31ba9d938be59ede/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[AOF]: https://github.com/the-omega-institute/trureturing/blob/fee3e2b8ff28d5048af2e03cfd83ef522a30365b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[JRF]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[SCR]: https://github.com/the-omega-institute/trureturing/blob/ebeec0b680e9584d1749fe60fefb98ee1044300a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md
[SLH]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[TPO]: https://github.com/the-omega-institute/trureturing/blob/2216a3b4560b7a34d477f18e0746b049a4f7dc5f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[CENTRALIZER]: https://github.com/the-omega-institute/trureturing/blob/6ccf950326969685b4e6b3edca27447f8b706b44/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[ENCODING]: https://github.com/the-omega-institute/trureturing/blob/6ccf950326969685b4e6b3edca27447f8b706b44/D5/S0/History/Spacetime/SourceTreeEncoding.lean
[ACQUISITION]: https://github.com/the-omega-institute/trureturing/blob/6ccf950326969685b4e6b3edca27447f8b706b44/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[TRACE]: https://github.com/the-omega-institute/trureturing/blob/6ccf950326969685b4e6b3edca27447f8b706b44/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.lean
[FREE]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Free.lean
[SYNTAX]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/ModelTheory/Syntax.lean
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[KR]: https://arxiv.org/html/cs/0408015v1
[MMN]: https://arxiv.org/html/1503.06687v2

## 追加锚（本行以下为增补区）

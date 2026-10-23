# Native regular-frontier selection and exact original-source relations

The results below are ordinary mathematical proofs, not Lean kernel
certification. The new relation combines a public regular selector with
an actually acquired complete native tree, while keeping the invocation
source, validation epoch and subsequent Return offset distinct. Its finite
presentation retains unbounded languages of actual original subtrees.
A finite presentation of this relation does not make the whole source
fiber an ordinary regular tree language.

## 1. Native sources, supplied rows and the selected boundary

**Definition 1.1 (sources and epochs).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\end{aligned}
\tag{NRF.1}
$$

All trees are nonempty, finite, ordered and fully bracketed. Equality is
literal constructor equality. Positions are finite words over $L,R$;
$\varepsilon$ is the root. Write $v|_p$ only when $p$ is present.
There is no bound on source size, height, position length or epoch.
The source $u$ is the actual register contents at source-independent
invocation. The integer $n\ge0$ counts genuine updates through the
specified validation event, and $j\ge0$ counts genuine updates strictly
after validation through the separate outer Return. Thus the two
register contents are $\rho^n u$ and $\rho^{n+j}u$.

**Definition 1.2 (supplied complete row).** For a finite prefix-free cut
$P$, reuse the complete literal row

$$
R_P(v)=(C_P(v),\pi_P(v)),\qquad
p\sim_{\pi_P(v)}q\ \Longleftrightarrow\ v|_p=v|_q
\quad(p,q\in P\cap\operatorname{Pos}(v)).
\tag{NRF.2}
$$

The exterior $C_P(v)$ replaces each reached cut subtree by its
addressed hole, retaining every other constructor and concrete leaf.
A requested but unreached cut position has its concrete strict-prefix
blocking leaf in the exterior. The partition is complete: different
classes assert disequality. It contains no additional comparisons of
hidden values with concrete exterior subtrees.

This is the record of [NUE, Definition 1.1][NUE], identified with canonical
class syntax by [ActualCutPartitionDecoder, `canonicalRow_record_iff`][ROW].
For a valid proposed row $(C,\pi)$, one actual tree $z_c$ is shared by
all holes of class $c$, and values of different classes are distinct.
The exact filling equivalence, including its inverse on a supplied
source, is [NUE, Proposition 1.3][NUE] and
[NativeCutFibers, `rowFiberEquiv`][CUT]. Its private `recover_fill`,
`fill_injective` and `classValue_distinct` establish the same entire
fiber; they are not extra hypotheses about independent holes.

**Definition 1.3 (regular selection).** Fix a public finite nonempty
state set $Q$, states $q_\alpha,q_\beta\in Q$, a total function
$\delta:Q^2\to Q$ and $F\subseteq Q$. Write
$A=(Q,q_\alpha,q_\beta,\delta,F)$ and

$$
q_A(\alpha)=q_\alpha,\qquad q_A(\beta)=q_\beta,\qquad
q_A(\langle x,y\rangle)=\delta(q_A(x),q_A(y)).
\tag{NRF.3}
$$

For $v\in\mathcal T$ let $P_A(v)$ contain precisely the positions $p$
with $q_A(v|_p)\in F$ and $q_A(v|_a)\notin F$ at every strict ancestor
$a$ of $p$. The output is

$$
\mathcal O_A(v)=\bigl(P_A(v),R_{P_A(v)}(v)\bigr).
\tag{NRF.4}
$$

This is a finite cut, possibly empty or the root singleton. It includes
no blocked requested positions. Its cardinality and address lengths
need not be bounded uniformly over $v$.

**Definition 1.4 (finite syntax validation).** A proposed boundary is
$b=(P,C,\pi)$. It is *row-valid* when it satisfies [NUE, Definition 1.2][NUE]:
$P$ is a finite prefix-free set; $C$ is a nonempty finite full ordered
context; every hole has its true address, occurs once and belongs to
$P$; every omitted member of $P$ is blocked by a concrete strict-prefix
leaf; and $\pi$ is an equivalence relation on exactly the reached holes.
It is *selection-valid* when additionally the hole set of $C$ equals
$P$. Class names can be canonically ordered by least hole address.
These are finite syntactic checks, not realizability promises.

Malformed input denotes an empty selected relation. A row-valid input
with blocked requested positions also denotes an empty selected
relation, although its bare-row relation can be nonempty. An empty
selected cut has ground $C$ and the empty partition. A root cut has
one root hole and its singleton partition.

**Definition 1.5 (two relations).** For row-valid $b$ put

$$
H_b(u,n)\ \Longleftrightarrow\ R_P(\rho^n u)=(C,\pi),\qquad
E_b(u,n)\ \Longleftrightarrow\ \mathcal O_A(\rho^n u)=b.
\tag{NRF.5}
$$

For non-row-valid data both are false; for row-valid but
non-selection-valid data $E_b$ is false. Always $E_b\subseteq H_b$.
Neither definition supplies an epoch to the observer.

The supplied row-only result [NUE, Theorem 2.2][NUE] preserves each
original $u$ when reducing equality to a fixed row. The signed results
[NCE, Theorems 4.2 and 5.1][NCE] instead give exact existential epoch
support and may replace source witnesses. The fixed-numeral feasibility
interface [NSF, Theorem 5.2][NSF] does not itself include arbitrary
regular selector guards. The extra condition and its effective
all-source treatment are the subject here.

## 2. The exact local selector condition

**Definition 2.1 (exterior state guard).** Suppose $b$ is
selection-valid and let $B$ be the classes of $\pi$. For
$s\in Q^B$, evaluate $C$ bottom-up, using $s_{[p]}$ at hole $p$,
the two actual leaf states at concrete leaves, and $\delta$ at pairs.
Denote the resulting state at node $a$ by $\widehat q_{C,s}(a)$. Set

$$
\chi_A(C,s)\ \Longleftrightarrow\
\left(\bigwedge_{p\in P}s_{[p]}\in F\right)
\land
\left(\bigwedge_{a\in\operatorname{Pos}(C)\setminus P}
                 \widehat q_{C,s}(a)\notin F\right).
\tag{NRF.6}
$$

The second conjunction includes every concrete leaf and every exterior
node in a branch that contains no hole. No state below a hole is tested.

**Theorem 2.2 (selected filling equivalence).** For every
selection-valid $b$ and every $v\in\mathcal T$,

$$
\mathcal O_A(v)=b
\quad\Longleftrightarrow\quad
\exists(z_c)_{c\in B}\in\mathcal T^B:\quad
v=C[\mathbf z],\quad
\bigwedge_{c\ne d}z_c\ne z_d,\quad
\chi_A\bigl(C,(q_A(z_c))_{c\in B}\bigr).
\tag{NRF.7}
$$

The valuation, when it exists, is unique for fixed $v$.

Proof. The complete-row supplier in Definition 1.2 gives the source
reconstruction, sharing, distinctness and inverse valuation. If the
selector returns $P$, every hole accepts. Every exterior node rejects:
an accepting exterior node with no accepting strict ancestor would
itself have been selected, while an accepting strict ancestor would
already have stopped the traversal. Bottom-up evaluation on $C$ with
the actual hole states is exactly the state evaluation on $v$ at those
nodes. This proves necessity.

Conversely, traverse $C$ from the root. At each exterior pair the guard
rejects and permits descent to both children. At each concrete leaf it
rejects without producing a hole. At a hole it accepts and stops.
Therefore precisely the addressed holes $P$ are selected, independently
of accepting descendants inside their fillers. The supplied filling
correspondence gives every equality and every disequality of $\pi$.
The empty valuation and the single root hole obey the same argument.
$\square$

**Proposition 2.3 (necessary distinctions in the guard).** Hole
acceptance alone, rejection only at strict hole ancestors, and equality
of automaton states each fail to characterize the selected complete row.

Proof. If $F=Q$, every nonempty source selects its root, even when the
two child states also accept. If $A$ accepts exactly $\alpha$, the
bare row $P=\varnothing,C=\alpha$ has no hole ancestors but cannot
be an output: its concrete root leaf accepts. For an automaton giving
both leaves the same accepting state and rejecting pairs,
$\langle\alpha,\alpha\rangle$ and $\langle\alpha,\beta\rangle$
select the same two addresses and have the same hole-state tuple,
but their complete partitions differ. $\square$

## 3. Actual acquisition and the original-source correspondence

**Assumption 3.1 (paid native capture and complete accessibility).**
Use the one-register history and Read port of [CNA, Definitions 1.1–1.4][CNA]
and [CWS, Definition 1.1][CWS]. A Read submits its entire finite
literal address and returns $\alpha,\beta$, branch or absent.
The only writer action is the global $\rho$ on the same authentic
register. There is no reset, rerooting, source identity test, snapshot,
clock, equality port, size bound or source-dependent initial advice.
Updates may occur between observer events, including local computation.

Use the existing full-capture instance $\mathrm{RA}(\varnothing)$ of
[CWS, Definition 2.4 and Theorems 3.3–3.4][CWS]. At its designated final
guard Read $v$, every returning legal history has acquired the complete
finite tree $U_v$. Termination holds under unknown finite total writer
interference and observer progress. The full tree is paid acquired data.
The supplier's return to its caller and the outer Return are separate.

The outer producer computes (NRF.4) from those acquired bytes, then
performs the complete canonical handoff of [CAB, Definition 1.3][CAB].
The accessible final data are exactly the public selector and declared
public parameters, and canonical $b$. All source-dependent temporary
values, actual state annotations, guards, operands, counters, retry
history, earlier outputs, control residue and allocation distinctions
are cleared, retracted or excluded from accessibility as stipulated
there. Output identities are fixed and extents depend only on output
bytes. Any additionally accessible field changes the observation and
must be included. This is an accessibility assumption, not physical
erasure. No permission to inspect the live register is created by a
mathematical decoder.

**Theorem 3.2 (both directions at invocation, validation and Return).**
Under Assumption 3.1 the projection of all legal returning producer
histories with boundary $b$ onto their invocation source, actual update
counts and Return register is exactly

$$
\mathscr R_b=
\{(u,n,j,\rho^{n+j}u):u\in\mathcal T,\ n,j\in\mathbb N,
                                      \ E_b(u,n)\}.
\tag{NRF.8}
$$

Every member has a real producing history with those identical $u,n,j$
and the entire boundary $b$. The producer terminates under the
supplier's finite-interference and observer-progress assumptions.

Proof. On any returning legal history, capture safety gives precisely
$U_v=\rho^n u$, where $n$ includes all updates before and during all
attempts. The producer evaluates the selector and exact literal
partition on this acquired tree. Theorem 2.2 identifies its whole
output, and complete handoff leaves exactly that boundary. The
subsequent $j$ genuine updates give $\rho^{n+j}u$ at outer Return.
This safety direction does not assume a paused writer, nor finite
interference on histories that do not return.

For the reverse direction fix any $u,n,j$ satisfying $E_b(u,n)$.
After invocation, schedule exactly $n$ updates before the first
observer Read. Schedule no updates during one successful full capture;
its finite stationary execution validates $\rho^n u$. The local
selector computation therefore gives $b$. Schedule exactly $j$ updates
after validation and before outer Return, for example after the finite
local preparation. Complete the specified handoff and Return. This is
a legal schedule of the actual producer, preserving the original $u$
and both actual counts. The paused portion is an existential witness
schedule, not a suspension primitive available to the program and not
the proof of universal safety.

For liveness, the supplied capture terminates under finite interference
and observer progress. Its returned tree is finite. State evaluation,
cut construction, literal comparisons, canonical row formation and
cleanup are finite computations on that tree. Observer progress
therefore completes them and outer Return.

For comparison, replace selection by taking the complete row at the
fixed public cut $P$ after the same full capture, and perform the
same canonical handoff. The identical forward and reverse arguments
give its actual projection
$\{(u,n,j,\rho^{n+j}u):H_b(u,n),\ j\ge0\}$, including
row-valid blocked cuts. Thus the bare relation used below also has
an actual producing interpretation; it is not only a relaxed
predicate on trees. $\square$

**Definition 3.3 (recovery domain).** A passive target of invocation,
validation or Return is recoverable at an attainable boundary exactly
when it is constant on the corresponding coordinates of $\mathscr R_b$.
This is the existing fiber-constancy criterion
[TargetRecoveryCriterion, `target_recovery_criterion`][REC], restricted
to the attained image when necessary. It is not a decision theorem for
arbitrary targets. Legal continuations must also preserve their actual
permissions and operands; constancy of a value does not grant a port.
The relation (NRF.8) describes possible histories through their stated
coordinates, not the discarded event-by-event transcript.

## 4. Sourcewise periodicity for each fixed boundary

**Definition 4.1 (leaf-state orbit and epoch cells).** Define

$$
(a_0,b_0)=(q_\alpha,q_\beta),\qquad
(a_{k+1},b_{k+1})=(b_k,\delta(b_k,a_k)).
\tag{NRF.9}
$$

Following this orbit in the finite set $Q^2$ until its first repeat
computes $\mu\ge0$ and $\lambda\ge1$ with
$\mu+\lambda\le |Q|^2$ and
$(a_{k+\lambda},b_{k+\lambda})=(a_k,b_k)$ for $k\ge\mu$.
For row-valid $b$ put

$$
\begin{aligned}
D&=\max(\{0\}\cup\{|p|:p\in P\}),\\
b_{\rm row}&=
 \begin{cases}
  2(d+1),&C\text{ has a concrete leaf, of least such depth }d,\\
  2D,&C\text{ has no concrete leaf},
 \end{cases}\\
B_0&=\max(2D,b_{\rm row}),\qquad T=B_0+\mu,\\
\kappa(n)&=
 \begin{cases}n,&n<T,\\T+((n-T)\bmod\lambda),&n\ge T.
 \end{cases}
\end{aligned}
\tag{NRF.10}
$$

Let $J=\{0,\ldots,T+\lambda-1\}$ and

$$
I_r=\{r\}\quad(r<T),\qquad
I_r=r+\lambda\mathbb N\quad(T\le r<T+\lambda).
\tag{NRF.11}
$$

These disjoint sets partition $\mathbb N$, with $\kappa(n)=r$ exactly
when $n\in I_r$. No minimality is asserted.

**Theorem 4.2 (uniform reduction preserving the identical original).**
For every row-valid proposed $b$, every $u\in\mathcal T$ and every
$n\ge0$,

$$
H_b(u,n)\longleftrightarrow H_b(u,\kappa(n)),\qquad
E_b(u,n)\longleftrightarrow E_b(u,\kappa(n)).
\tag{NRF.12}
$$

In particular, equality to each fixed selected boundary has a computable
sourcewise eventually periodic law, uniform over all original sources.

Proof. The assertion for $H_b$ follows directly from [NUE, Theorem 2.2][NUE]:
its threshold is $b_{\rm row}$, and $T\ge b_{\rm row}$. Below $T$
there is no change. If selection validity fails, $E_b$ is always false.
Assume it holds.

Structural induction on any fixed finite $x$ gives

$$
q_A(\rho^k x)=\operatorname{eval}_{a_k,b_k,\delta}(x).
\tag{NRF.13}
$$

Indeed the two leaves give (NRF.9), and pairing is preserved by $\rho$.
Consequently equal orbit pairs give equal states for every finite $x$,
not merely for the two atomic orbits.

If $C$ has a concrete leaf at depth $d$, the supplied branch saturation
[NSF, Lemma 9.2][NSF] makes its row impossible for every $u$ and all
$n\ge2(d+1)$. Both tail predicates are false. This includes every
no-hole row and every empty-cut output.

Otherwise all leaves of $C$ are holes, and $P$ is its complete finite
leaf frontier. At epoch $B_0\ge2D$, all strict prefixes of its holes
are branches for every $u$. All holes exist, including those not
present at invocation. Set $w=\rho^{B_0}u$ solely within this proof.
The reached-position transport of [NativeDepthPatterns,
`original_present_transport`][DEPTH] gives

$$
(\rho^{B_0+k}u)|_p=\rho^k(w|_p)\qquad(p\in P,k\ge0).
\tag{NRF.14}
$$

For $n\ge T$, both $n-B_0$ and $\kappa(n)-B_0$ are at least $\mu$
and are congruent modulo $\lambda$. Equations (NRF.9), (NRF.13) and
(NRF.14) give the same state at every hole at these two epochs.
Evaluation of the fixed exterior gives the same state at all its
nodes, hence the same $\chi_A$. The entire row equality is already
preserved by NUE; equivalently injectivity preserves and reflects all
hole equalities and disequalities in (NRF.14). Theorem 2.2 now gives
the selected equivalence. No transport was used backwards through a
position's birth. The auxiliary $w$ has not replaced invocation $u$.
$\square$

**Proposition 4.3 (the reduced object and two failed shortcuts).** The
law is not a bound on actual time, does not generally have period one,
and does not make the whole output sequence eventually periodic.

Proof. The root-hole bare row holds at every epoch. For the rightmost
leaf automaton with $Q=\{0,1\}$, $q_\alpha=0,q_\beta=1$,
$\delta(x,y)=y,F=\{1\}$, (NRF.9) alternates $(0,1)$ and $(1,0)$.
On the same source $\alpha$, the selected root row holds precisely
at odd epochs. A constant row-only cap loses this condition.
If $F=\varnothing$, every selected cut is empty and the output on
$\alpha$ contains the entire tree $\rho^n\alpha$. These trees are
pairwise distinct by [NSF, Lemma 9.2][NSF]. Their output sequence is
not eventually periodic, although equality to each fixed output
has the law just proved. $\square$

## 5. Original-source pruning and finite epoch geometry

**Definition 5.1 (original pruning patterns).** For the fixed context
$C$, define a finite family $\Gamma(C)$ recursively, with addresses
inherited from $C$:

$$
\begin{aligned}
\Gamma(\square_p)&=\{X_p\},\\
\Gamma(\alpha)=\Gamma(\beta)&=\{\alpha,\beta\},\\
\Gamma(\langle C_L,C_R\rangle)&=
 \{\alpha,\beta\}\ \cup\
 \{\langle S_L,S_R\rangle:S_L\in\Gamma(C_L),\ S_R\in\Gamma(C_R)\}.
\end{aligned}
\tag{NRF.15}
$$

Within a pattern, the variables $X_p$ are all distinct and occur once.
A variable occurs at an actually present original position that is a
hole of $C$. A pattern may instead stop at an original leaf above
several eventual holes. Its ground leaves describe original leaves,
not the concrete labels of the captured exterior.

**Lemma 5.2 (coverage by original pruning).** If $H_b(u,n)$ for any
$n$, there is a unique $S\in\Gamma(C)$ and a unique valuation
$x_p\in\mathcal T$ of its variables with $u=S[\mathbf x]$.
The pattern is determined by $u,C$ alone and is independent of $n$.
For a fixed pattern, filling is injective.

Proof. Compare $u$ with $C$ from the root. At a hole of $C$, retain
the actual entire original subtree as $X_p$. At an original leaf,
stop and retain its original label. At an original pair, $\rho^n$
retains that pair. Thus $C$ cannot have a concrete leaf there when
$H_b(u,n)$ holds; if $C$ is a pair, descend to both children. This
is exactly (NRF.15) and is forced at every step. Each variable value
is recovered from the original subtree at its stated address.
Conversely every valuation fills the same pattern, and these present
addresses recover its values. The alternatives leaf/pair/variable
are distinguished by this pruning rule, so different patterns do
not represent the same pruned original. $\square$

**Definition 5.3 (finite geometric evaluation at a numeral).** Fix
$S\in\Gamma(C)$ and a supplied numeral $r$. Expand each explicit
original leaf of $S$ by $\rho^r$, and replace its variable at $p$
by a formal opaque block $\rho^r(X_p)$ at that same position. Cut
this symbolic tree at the public $P$, using the usual stopping and
blocking rules. An opaque block occurs at a cut position and is
never inspected. Compare the entire resulting addressed exterior
with $C$. Let $\gamma_{S,r}$ be this finite equality test.

If $\gamma_{S,r}$ is true, every hole value is one of exactly two
forms:

$$
f_{r,p}(\mathbf x)=\rho^r(x_p)\quad\hbox{at an original hole},
\qquad
f_{r,p}(\mathbf x)=g_{r,p}\in\mathcal T\quad\hbox{at a born hole}.
\tag{NRF.16}
$$

The latter is the computed ground subtree inside an expanded original
leaf. There are finitely many such trees for this finite $S,r,C$.
The predicate $\gamma_{S,r}$ and the list (NRF.16) do not inspect
any residual value. Explicit ground expansions may be large, but
are finite and effective.

Reuse the native ground inverse from [ARH, Lemma 11.2][ARH]. Its one-step
form is

$$
\begin{aligned}
\iota(\alpha)&\text{ undefined},&\iota(\beta)&=\alpha,\\
\iota(\langle\beta,\alpha\rangle)&=\beta,&
\iota(\langle x,y\rangle)&=\langle\iota(x),\iota(y)\rangle
 \quad\text{in all other defined pair cases}.
\end{aligned}
\tag{NRF.17}
$$

The last case requires both child inverses. The exceptional pair
cannot overlap it, since $\alpha$ has no predecessor. The domain
of $\iota_r=\iota^{\circ r}$ is exactly $\rho^r[\mathcal T]$, and
$\iota_r(\rho^r x)=x$. This operation is applied only to known
finite ground terms, not as a free source port.

**Lemma 5.4 (finite geometry and exact partition tests).** For every
valuation $\mathbf x$, the exterior of $\rho^r(S[\mathbf x])$ is
$C$ exactly when $\gamma_{S,r}$ is true. In that case its actual
hole values are (NRF.16). All their equality tests reduce to finite
ground comparisons and tests of the forms

$$
x_p=x_q,\qquad x_p=h\quad(h\in\mathcal T\text{ explicitly known}).
\tag{NRF.18}
$$

The reductions preserve truth and falsity, including every required
disequality.

Proof. Substitution preserves each explicit pair of $S$. At an
explicit leaf its complete expansion is the finite ground term
used in Definition 5.3. Every variable is at a cut position, so
its transformed value is replaced by that hole without looking
inside it. This proves geometry by induction on the pattern and
the finite expanded leaves, including absence of early positions
and concrete blockers.

Two original-hole values compare by injectivity:
$\rho^r x_p=\rho^r x_q$ if and only if $x_p=x_q$.
Two born-hole values are known finite trees and compare literally.
For a mixed pair, $\rho^r x_p=g$ is false if $\iota_r(g)$ is
undefined, and otherwise is exactly $x_p=\iota_r(g)$.
Taking the Boolean complement gives each disequality, not an
approximation to it. A born filler itself need not have a
predecessor; only its equality with an original-hole image is being
tested. All comparisons refer to the same valuation. $\square$

**Proposition 5.5 (born holes are not independent root images).**
Requiring every selected filler to belong to $\rho^r[\mathcal T]$
is unsound even when the complete captured root has that membership.

Proof. Let the selector accept exactly the two literal leaves and
reject every pair. Invocation $u=\beta$ and $r=1$ give the capture
$\langle\beta,\alpha\rangle$, with selected cut $\{L,R\}$ and
two distinct classes. Its right filler $\alpha$ has no predecessor,
although the whole capture is $\rho\beta$. The original pruning
pattern is the single original leaf $\beta$; both holes in
(NRF.16) are ground born holes. No residual image test is imposed
on either of them. Theorem 3.2 realizes these same coordinates
for every independent $j$. $\square$

## 6. A finite simultaneous representation with unbounded residuals

**Definition 6.1 (regular original-state domains).** Use the finite
representative set $J$ of Definition 4.1. For each $r\in J$, let
$A_r$ have the same state set and pair operation as $A$, but leaf
states $(a_r,b_r)$. Acceptance is immaterial when recording a state.
Equation (NRF.13) says

$$
q_{A_r}(x)=q_A(\rho^r x).
\tag{NRF.19}
$$

Take the finite total deterministic product $M=\prod_{r\in J}A_r$.
Its state at $x$ is the whole vector $(q_{A_r}(x))_{r\in J}$.
For each product state $s$ let

$$
L_s=\{x\in\mathcal T:q_M(x)=s\}.
\tag{NRF.20}
$$

These are entire regular languages, with some possibly empty, finite
or infinite. Different states have disjoint languages. The product
and inverse-image principle are the ordinary tree-automaton operations
of [Engelfriet, Theorems 3.8, 3.32 and Exercise 3.68][ENG]; (NRF.19)
is their direct construction for this particular substitution.
No automaton state asserts equality of two actual trees.

**Definition 6.2 (finite equality types on the same original).** Fix
$S\in\Gamma(C)$, with variable set $V_S$. Perform Definition 5.3
for every $r\in J$. Form the finite set of distinct ground trees

$$
G_S=\{\iota_r(g_{r,p}):r\in J,\ \gamma_{S,r}\text{ true},\
 p\text{ a born hole},\ \iota_r(g_{r,p})\text{ defined}\}.
\tag{NRF.21}
$$

An equality type $\theta$ is a partition of
$V_S\sqcup\{c_h:h\in G_S\}$ in which different constant names
$c_h,c_{h'}$ are in different blocks. A block containing $c_h$
forces all its variables to the actual tree $h$. Each block containing
variables and no constant is a *free block*. Number those blocks by
least variable address as $1,\ldots,k$. They have values
$y_1,\ldots,y_k$ required to be pairwise distinct and outside $G_S$.
Constant-only blocks need no variable. Every actual valuation of
$V_S$ has exactly one such type, with uniquely determined free values.

For each free block choose a product state $\sigma_i$. Substitute
its variable $Y_i$ for all variables in that block of $S$, and the
appropriate ground tree for each forced block. Call the resulting
original constructor term $W_{S,\theta}(\mathbf Y)$. Each free
variable occurs at least once at a specified original hole address.
The cell's full residual domain is

$$
\Omega_{S,\theta,\sigma}=
\left\{\mathbf y\in\mathcal T^k:
 y_i\in L_{\sigma_i}\setminus G_S\ (1\le i\le k),\quad
 y_i\ne y_l\ (i\ne l)\right\}.
\tag{NRF.22}
$$

Its source decoder is direct original filling

$$
\operatorname{Dec}_{S,\theta}(\mathbf y)=W_{S,\theta}[\mathbf y].
\tag{NRF.23}
$$

Thus the representation language consists of finite constructor
patterns, finite equality types, finite deterministic state-language
descriptions, finite ground exclusions and explicit all-different
guards. In particular (NRF.22) is not the original selected predicate
renamed, and is not replaced by a finite witness list.

**Definition 6.3 (finite truth labels).** Attach bits $h_r,e_r$ to a
cell for every $r\in J$ as follows. If $\gamma_{S,r}$ fails, both
bits are false. Otherwise compute all pairwise comparisons of the
hole expressions (NRF.16) using Lemma 5.4. The type $\theta$
determines every variable-variable or variable-ground comparison
that occurs, because every relevant ground inverse is in $G_S$.
Set $h_r$ true precisely when the resulting equality partition is
exactly $\pi$, including every false bit.

If $h_r$ is false or $b$ is not selection-valid, put $e_r$ false.
Otherwise give an original-hole variable the $r$ coordinate of its
free block's $\sigma_i$, or $q_{A_r}(h)$ if forced to $h$.
Give each born hole its actual state $q_A(g_{r,p})$. Holes of the
same row class have the same state: for a mixed equality this follows
from $\rho^r h=g_{r,p}$, and for two original holes from their shared
actual value. Evaluate $C$ at these states and set $e_r$ to the truth
value of (NRF.6). The evaluations are finite and use no hidden
actual state retained by the producer.

For this cell define its arithmetic guards

$$
I^H=\bigcup_{r\in J:h_r}I_r,\qquad
I^E=\bigcup_{r\in J:e_r}I_r.
\tag{NRF.24}
$$

They are finite unions of singletons and arithmetic progressions.
The construction keeps the same equality type and the same product
state vector across *all* representatives; it does not choose new
original values when changing $r$.

**Lemma 6.4 (truth is constant on each residual cell).** For every
$\mathbf y\in\Omega_{S,\theta,\sigma}$ and every $r\in J$,

$$
\begin{aligned}
H_b(\operatorname{Dec}_{S,\theta}(\mathbf y),r)&\longleftrightarrow h_r,\\
E_b(\operatorname{Dec}_{S,\theta}(\mathbf y),r)&\longleftrightarrow e_r.
\end{aligned}
\tag{NRF.25}
$$

Proof. Geometry is independent of the residual values by Lemma 5.4.
When it succeeds, the complete equality type makes every comparison
in (NRF.18) constant, so $h_r$ is exactly the bare-row truth. The
product state specifies every $q_{A_r}(y_i)$, and the forced values
and born trees have the computed states. Equation (NRF.19) then
gives exactly the actual capture states. Theorem 2.2 gives $e_r$.
This uses complete actual sharing and disequality; it does not replace
them by the state constraints. $\square$

**Theorem 6.5 (terminating cell feasibility and actual filler extraction).**
Nonemptiness of every domain (NRF.22) is decidable by a finite
construction. A positive decision gives enough distinct actual finite
trees to fill its free blocks. A negative decision terminates as well.
The decision does not enumerate all original sources.

Proof. The case $k=0$ has the unique empty residual tuple; the forced
original term is fully determined. Suppose $k>0$, put $g=|G_S|$,
and use cap $L=k+g$. For each state $s$ of $M$ write
$\ell_s=\mathbf1_{q_M(\alpha)=s}+\mathbf1_{q_M(\beta)=s}$ and
iterate synchronously from $c_0(s)=0$:

$$
c_{t+1}(s)=\min\left(L,\ \ell_s+
 \sum_{\delta_M(a,b)=s}c_t(a)c_t(b)\right).
\tag{NRF.26}
$$

The two leaf symbols are counted separately even if their states
coincide. By induction on $t$, $c_t(s)$ is the number, capped at
$L$, of distinct finite trees of height less than $t$ with state $s$.
A tree is either one of the two leaves or an ordered pair with unique
children. Determinism gives a unique child-state pair; the summands
therefore count disjoint sets of trees, not accepting runs. Capping
before multiplication and addition commutes with the final cap on
nonnegative counts. These facts prove the induction.

The count vector is monotone. It has at most $L|\operatorname{States}(M)|$
strict increases before reaching a fixed point, and one additional
application detects stability. The height interpretation implies

$$
c_*(s)=\min(L,|L_s|).
\tag{NRF.27}
$$

Indeed a fixed vector cannot increase at a later height, and every
finite tree has finite height. This includes infinite languages:
any $L$ distinct members occur below some finite common height.

Compute the exact number $g_s$ of elements of $G_S$ with state $s$.
Then

$$
d_s=\min(k,c_*(s)-g_s)=\min(k,|L_s\setminus G_S|).
\tag{NRF.28}
$$

If $c_*(s)<L$, the language was counted exactly. If $c_*(s)=L$,
at most $g$ exclusions leave at least $k$ members. Subtraction is
nonnegative since all $g_s$ excluded trees are counted. Let
$m_s=|\{i:\sigma_i=s\}|$. The exact feasibility condition is

$$
\forall s,\qquad d_s\ge m_s.
\tag{NRF.29}
$$

Necessity follows from distinctness within each state. For sufficiency,
choose $m_s$ distinct values of that state outside $G_S$; different
states have disjoint languages and hence cannot collide. This is the
disjoint-domain specialization of the distinct-representative method
in [SLH, Theorem 61.1][SLH], not a new general matching theorem.

Actual trees can be extracted during the same finite height iteration.
At each state retain up to $L$ distinct terms from the leaves and
ordered pairs of previously retained child terms. If a nonempty
product has fewer than $L$ terms, each nonempty factor has fewer than
$L$ and its entire relevant finite set was retained. If it has at
least $L$, the product of the two capped lists still has at least
$L$. Different child-state pairs produce disjoint terms. Thus the
retained list size follows (NRF.26). On count stabilization stop;
there is no need to wait for the identities of capped representatives
to stabilize. Lists of size below $L$ then contain their entire state
languages; a full list contains $L$ actual distinct terms. Remove
$G_S$ and select the required $m_s$ values. Their finite constructor
derivations establish actual membership. These lists certify capacities
only; all of (NRF.22) remains the denotation. $\square$

**Theorem 6.6 (finite all-source representation, decoding and inverse extraction).**
From any finite $A$ and proposed $b$ one can effectively construct a
finite list $\mathcal C$ of nonempty cells (NRF.22)–(NRF.24) such that

$$
\begin{aligned}
\{(u,n):H_b(u,n)\}
 &=\bigcup_{c\in\mathcal C}
   \{(\operatorname{Dec}_c(\mathbf y),n):
                  \mathbf y\in\Omega_c,\ n\in I^H_c\},\\
\{(u,n):E_b(u,n)\}
 &=\bigcup_{c\in\mathcal C}
   \{(\operatorname{Dec}_c(\mathbf y),n):
                  \mathbf y\in\Omega_c,\ n\in I^E_c\}.
\end{aligned}
\tag{NRF.30}
$$

For selected sources the full operational denotation is

$$
\mathscr R_b=
\bigcup_{c\in\mathcal C}
\left\{
\bigl(\operatorname{Dec}_c(\mathbf y),n,j,
 \rho^{n+j}\operatorname{Dec}_c(\mathbf y)\bigr):
\mathbf y\in\Omega_c,\ n\in I^E_c,\ j\in\mathbb N
\right\}.
\tag{NRF.31}
$$

Every candidate in (NRF.31) lifts to an actual selected producing run
with identical $u,n,j$ and entire $b$. Every actual selected candidate
extracts a code that decodes back to the identical source and counts. For fixed
$u,n$, the canonical extracted source cell and residual values are
unique. The cells can retain arbitrarily large source trees.

Proof. Reject non-row-valid input by the empty list. Otherwise perform
the finite constructions of Definitions 4.1, 5.1, 5.3 and 6.1–6.3.
There are finitely many pruning patterns, finite expansions at finitely
many representative numerals, finitely many equality types of a
finite set, and finitely many assignments of states to free blocks.
Theorem 6.5 removes exactly the empty domains. Cells with every
$h_r$ false can also be discarded. Thus every stage terminates,
including the entirely empty case.

For any retained residual valuation, Lemma 6.4 and Theorem 4.2 give
(NRF.30) at every actual $n$. Substitution into Theorem 3.2 gives
(NRF.31) and the actual history lift. In particular the exponent in
its Return coordinate is $n+j$, never $\kappa(n)+j$.

Conversely take any original $u,n$ with $H_b(u,n)$, and set
$r=\kappa(n)$. Theorem 4.2 retains this very $u$ at $r$.
Lemma 5.2 extracts its unique original pruning pattern $S$ and its
actual subtree values. Equality among those values and with every
member of $G_S$ determines $\theta$ uniquely. The values of its
free blocks determine their unique $M$ states $\sigma$. They lie
in the full domain (NRF.22), so its cell cannot have been removed
as empty. Definition 6.3 gives $h_r$ true, and $e_r$ true if the
candidate was selected. Filling the original pattern with the
extracted values returns exactly $u$. Actual $n,j$ are kept as
coordinates of the code; they are not inferred from representative
states or supplied to the producer.

Within a cell every free block occurs at an original position, so
reading the corresponding subtree of the mathematical candidate
inverts (NRF.23). Between cells the canonical pruning, equality type
and product-state vector are unique. This proves the stated inverse
extraction, while imposing no bound on any residual value. $\square$

**Corollary 6.7 (effective decisions and what a witness means).**
Emptiness of $\mathscr R_b$, exact support of validation epochs,
membership of a supplied finite candidate $(u,n,j)$, and extraction
of an actual source and producing schedule at any feasible supplied
$n$ are decidable. The epoch support is the effective finite union
$\bigcup_{c\in\mathcal C}I^E_c$.

Proof. Each cell in the list is nonempty by Theorem 6.5, so its guard
is precisely its supported epochs. To obtain a witness at a feasible
$n$, choose a cell whose guard contains it and extract sufficient
fillers as above; Theorem 3.2 supplies the schedule for any supplied
$j$. For a supplied original source, prune it, compare its actual
residual values with the finite constants and each other, compute
the finite product states, and test its guard at $n$. Equivalently,
evaluate the bounded representative $\rho^{\kappa(n)}u$.
All are finite computations on supplied finite data. A witness
proves existence and is not thereby the unknown actual original.
Decoding with actual residuals recovers that candidate, whereas
recovering an unknown source from $b$ alone requires fiber constancy.
$\square$

## 7. Comparing relations and recovering original-source properties

**Theorem 7.1 (tuple equality and source-projection equality).** For
any finite $A,b$, both of the following distinct statements are
decidable:

$$
\begin{aligned}
\mathsf{TupleEq}(b)&:\quad
 \forall u\,\forall n,\ H_b(u,n)\Longrightarrow E_b(u,n),\\
\mathsf{SourceEq}(b)&:\quad
 \forall u,\ (\exists n\ H_b(u,n))
                   \Longrightarrow(\exists m\ E_b(u,m)).
\end{aligned}
\tag{NRF.32}
$$

A negative answer in the first case gives a finite original and a
failing epoch tuple. A negative answer in the second case gives one
finite original admitted by the bare row at some epoch and excluded
by selection at every epoch. Independent $j$ does not change these
comparisons of the $(u,n,j)$ relations or their $u$ projections.

Proof. Use the *same* cell list from Theorem 6.6 for both relations.
Every relevant original source has one canonical cell. Lemma 6.4
makes all representative-epoch bits constant throughout that whole
source cell, and Theorem 4.2 covers every epoch. Hence

$$
\begin{aligned}
\mathsf{TupleEq}(b)
 &\longleftrightarrow
 \neg\exists c\in\mathcal C\ \exists r\in J:\ h_{c,r}\land\neg e_{c,r},\\
\mathsf{SourceEq}(b)
 &\longleftrightarrow
 \neg\exists c\in\mathcal C:\
       (\bigvee_{r\in J}h_{c,r})\land
       \neg(\bigvee_{r\in J}e_{c,r}).
\end{aligned}
\tag{NRF.33}
$$

These are finite tests on nonempty cells. If a test fails, use
Theorem 6.5 to produce one valuation in that cell, decode it to
$u$, and choose a representative with $h_r$ true. In the second
case this *same* $u$ has $e_s$ false for every representative $s$,
therefore for every actual epoch. If the tests pass, the unique
cell of any purported counterexample contradicts the corresponding
finite assertion. No complement or inclusion theorem for arbitrary
globally constrained tree languages has been invoked. The proof
works because the finitely many predicates are evaluated on one
common original pattern, equality type and product-state vector.
$\square$

**Proposition 7.2 (the two comparisons genuinely differ).** There is
a public two-state selector for which the root boundary has different
bare and selected tuple relations but identical source projections.
There is also a selector for which these source projections differ.

Proof. Let the states be the labels of the leftmost leaf, with
$\delta(x,y)=x$, and accept $\beta$. For the root-hole boundary,
$H_b(u,n)$ holds for all $u,n$. Every positive iterate has leftmost
leaf $\beta$: the images of both leaves start with $\beta$, and
pairing preserves the leftmost descent. Thus

$$
E_b(u,n)\ \Longleftrightarrow\
 n\ge1\ \lor\ \text{the leftmost leaf of }u\text{ is }\beta.
\tag{NRF.34}
$$

The tuple $(\alpha,0)$ fails selection, but every original source
is selected at epoch one. Both source projections are $\mathcal T$.
Even the epoch projections agree, since a selected witness exists
at epoch zero. Thus neither one-dimensional projection determines
the joint relation.

Instead let $A$ accept exactly the single tree $\alpha$. No positive
$\rho$-image has root $\alpha$. The same selected root boundary
then has exactly $(u,n)=(\alpha,0)$, whereas its bare row has all
$u,n$. Its selected source projection is $\{\alpha\}$, a proper
subset of $\mathcal T$. These are separate quantified conclusions,
not an inference from the first failed tuple. $\square$

**Theorem 7.3 (finite-state properties of the original source).**
Given any other finite total deterministic bottom-up automaton $B$
with state map $q_B$, the set

$$
\mathcal V_b(B)=\{q_B(u):\exists n\ E_b(u,n)\}
\tag{NRF.35}
$$

is effectively computable, together with an actual original and
producing history for each state in it. At an attainable boundary,
$q_B(u)$ is recoverable exactly when this set is a singleton. Any
specified regular property of the invocation source is decidably
constant or nonconstant on that boundary, with finite counterexample
sources in the nonconstant case.

Proof. Replace $M$ in Definition 6.1 by $M\times B$ before assigning
states to free blocks. Geometry, equality types and ground exclusions
are unchanged. The capacity construction applies to this finite total
deterministic product. Evaluate the original term $W_{S,\theta}$
in the $B$ component, using the free values' assigned states and
the actual $B$ states of forced constants. This computes one fixed
$q_B(u)$ for every source in that cell. Keep its value precisely
when the nonempty cell has some $e_r$ true. Theorem 6.6 proves both
inclusions of (NRF.35), and Theorems 6.5 and 3.2 extract the stated
sources and histories.

On a nonempty fiber, singleton image is exactly constancy. For a
regular property with accepting set $F_B$, ask whether the computed
image lies wholly in $F_B$, wholly in its complement, or meets
both. In the last case the two extracted originals have opposite
property values and the same actual retained boundary. The state
being evaluated is explicitly that of $u$, not that of the captured
$\rho^n u$. No morphic image-complement interchange is needed.
$\square$

## 8. A complete deeper boundary and a persistent source property

**Definition 8.1 (one-hole context selector).** Let $D[-]$ be a fixed
finite ordered full context over the native constructors with exactly
one hole, at address $w$. Its other leaves and branches are concrete.
Let $A_D$ recognize exactly

$$
D[\mathcal T]=\{D[t]:t\in\mathcal T\}.
\tag{NRF.36}
$$

Such a finite total deterministic bottom-up automaton is effectively
available. One construction records, for every subcontext of $D$,
whether the current subtree matches it, treating its unique hole as
an unrestricted tree, and also records equality with each ground
subterm of $D$. Ground-leaf tests and ordered pair tests propagate
these finitely many Boolean flags bottom-up. The flag for $D$ is
the acceptance condition. Thus no unbounded hidden matching history
is part of the public selector. Take $w\ne\varepsilon$ when a
strictly deeper boundary is desired.

**Theorem 8.2 (mutual recovery of a full refined boundary).** For
any actual selected output $b=(P,C,\pi)$ of $A_D$ at validation
source $v$, put

$$
P^D=\{pw:p\in P\}.
\tag{NRF.37}
$$

From $b,D$ alone one can recover the entire row $R_{P^D}(v)$:
replace every hole of $C$ by a copy of $D[-]$ whose new hole is
addressed $pw$, and transport the partition by

$$
pw\sim_{\pi^D}qw\quad\Longleftrightarrow\quad p\sim_\pi q.
\tag{NRF.38}
$$

Conversely, from the refined addressed row and public $D$, one can
recover the original selected boundary $b$. The two maps are inverse
on actual selected outputs. They require no new source Reads and
preserve every equality and every disequality, not just the exterior
or the number of holes. Hidden residual trees remain unrestricted.

Proof. Each selected hole value belongs to (NRF.36), so it is
$D[t_p]$ for a unique $t_p$. The one-hole constructor map is
injective: the subtree at $w$ is exactly its argument. Therefore

$$
D[t_p]=D[t_q]\quad\Longleftrightarrow\quad t_p=t_q.
\tag{NRF.39}
$$

The addresses $pw$ are prefix-free because distinct $p,q$ already
are incomparable. The literal exterior at that finer cut is exactly
the stated substitution into $C$. Equation (NRF.39) proves all
partition bits, including cross-class inequalities. No relation
between a hidden value and an exterior constant was assumed.

For the inverse, remove the fixed suffix $w$ from every addressed
hole of the finer row, recovering exactly $P$. For each such $p$,
replace the entire displayed $D$ context at $p$ by a single hole
at $p$, and pull its complete partition back by $p\mapsto pw$.
The displayed contexts are disjoint and have their known literal
form on the attained image, so this operation recovers exactly
$C,\pi$. Empty $P$ gives no finer holes and leaves the same entire
ground tree on both sides. If $w=\varepsilon$ both maps are the
identity. This proves mutual recovery on the stated domain.
$\square$

**Proposition 8.3 (unbounded hidden values with genuine refinement).**
For $D[t]=\langle\beta,t\rangle$, a selected root row recovers
$R_{\{R\}}(v)$ as $\langle\beta,\square_R\rangle$ with its
singleton partition, while not determining $v$. The refinement
occurs at positive native epochs as well as at invocation. For
multiple selected holes, complete equalities and disequalities of
all their right subtrees transfer exactly.

Proof. A three-state automaton suffices: states $b,a,d$, leaf states
$q_\beta=b,q_\alpha=d$, pair transition equal to $a$ exactly when
its left state is $b$, and equal to $d$ otherwise; accept $a$.
Only the literal leaf $\beta$ has state $b$, so this accepts
exactly (NRF.36). Every $\langle\beta,t\rangle$ selects its
root, for arbitrary finite $t$, giving the same root row. Theorem
8.2 recovers its specified finer row. The two distinct captures
$\langle\beta,\alpha\rangle$ and
$\langle\beta,\beta\rangle$ already show lack of whole-tree
uniqueness; both are also possible original sources at epoch zero.
Moreover $(u,n)=(\beta,1)$ and $(\alpha,2)$ give the first capture.

For example $v=\langle D[x],D[y]\rangle$ rejects at the root
because its left child is a pair, and selects $L,R$. Its old holes
are equal if and only if $x=y$. Its refined cut $\{LR,RR\}$ has
exactly the same bit. Both signs are realized by actual finite
$x,y$, while their sizes are unrestricted. A bare root row, in
contrast, also admits $\alpha$ and cannot recover the asserted
right-hole exterior. The extra information comes from the public
selector's choice, not from a retained hidden state. $\square$

**Proposition 8.4 (endpoint boundary for the refinement).** Theorem
8.2 recovers the validation row. It does not in general recover the
same row at Return, nor the invocation row.

Proof. In Proposition 8.3 the capture
$v=\langle\beta,\alpha\rangle$ has finer row
$\langle\beta,\square_R\rangle$. One further update gives
$\rho v=\langle\langle\beta,\alpha\rangle,\beta\rangle$,
whose row at $R$ is
$\langle\langle\beta,\alpha\rangle,\square_R\rangle$.
Theorem 3.2 permits both $j=0$ and $j=1$ with the same $b,u,n$.
The originals $\beta$ at $n=1$ and
$\langle\beta,\alpha\rangle$ at $n=0$ also give the same
selected root boundary, but the former has $R$ blocked at invocation
and the latter has it present. Thus neither endpoint identification
follows from the validation decoder. $\square$

**Proposition 8.5 (a regular original property retained across both unknown offsets).**
There is a four-state public selector such that its choice of whether
to select the root recovers the property “both native leaf counts
are even” simultaneously for the invocation, validation and Return
sources, despite unknown $n,j$ and possible nonuniqueness of all
three trees.

Proof. Let $Q=(\mathbb Z/2\mathbb Z)^2$, use leaf states
$(1,0),(0,1)$, pair transition coordinatewise addition, and accept
only $(0,0)$. Its state is the parity vector
$\eta(t)=(N_\alpha(t),N_\beta(t))\bmod2$. The substitution satisfies

$$
\eta(\rho t)=T_2\eta(t),\qquad T_2(x,y)=(y,x+y).
\tag{NRF.40}
$$

This follows by counting the two leaf images and adding through
pairs. The map is invertible, with inverse $(a,b)\mapsto(b-a,a)$.
Hence $\eta(t)=0$ if and only if $\eta(\rho^k t)=0$ for every
$k\ge0$. The root is selected exactly when its state is zero.
The predicate $P=\{\varepsilon\}$ therefore gives the same
Boolean answer for $u,\rho^n u,\rho^{n+j}u$ on every actual
returning history.

The distinct sources $\langle\alpha,\alpha\rangle$ and
$\langle\beta,\beta\rangle$ give the same positive root boundary
at epoch zero. They remain compatible without a whole-source
reconstruction. A bare root row also admits $\alpha$, whose parity
vector is nonzero, so that bare row cannot recover this property.
This is a particular original-source consumer covered by Theorem
7.3; its additional persistence follows from the explicitly proved
invariance (NRF.40), not from an assumed Return snapshot. $\square$

## 9. Exact limits of regular summaries and epoch simplifications

**Proposition 9.1 (a nonregular selected source fiber).** Even at
fixed epoch zero, a complete selected-row source fiber need not be
an ordinary regular tree language.

Proof. Let $A$ record the parity of total leaf count, with both
leaf states $1$, transition addition modulo two, and $F=\{1\}$.
Consider $P=\{L,R\}$, exterior
$C=\langle\square_L,\square_R\rangle$, and a single shared class.
The exact epoch-zero fiber is

$$
\{\langle t,t\rangle:t\in\mathcal T,
                        \ N_\alpha(t)+N_\beta(t)\text{ odd}\}.
\tag{NRF.41}
$$

Both holes accept and their parent has even leaf count and rejects,
so Theorem 2.2 proves the displayed equality of fibers. There are
infinitely many distinct odd-leaf trees. Any finite deterministic
bottom-up recognizer for (NRF.41) assigns the same state to two
distinct such trees $s,t$. Acceptance of $\langle s,s\rangle$
then forces acceptance of $\langle s,t\rangle$, a contradiction.
Determinization of ordinary finite tree automata extends this
argument to nondeterministic recognizers [ENG, Theorem 3.8][ENG].
This is the diagonal obstruction of [BCGJV, Example 3.3][BCGJV]
inside the precise native selection family. It does not contradict
the finite constrained presentation (NRF.22). $\square$

**Proposition 9.2 (capacity and birth thresholds cannot be omitted).**
Nonempty accepting state languages do not suffice for distinct row
classes. The leaf-state preperiod alone is not a valid cutoff for
selected-boundary equality on all sources.

Proof. Let $A$ accept exactly $\alpha$. With two child holes in
different classes, both could be assigned its accepting state but
both would have to be the identical tree $\alpha$. Their required
disequality is impossible. One repeated class is realized by
$\langle\alpha,\alpha\rangle$. The obstruction is capacity one
versus two *classes*, not two occurrences of a shared class.

For the second assertion use the automaton that accepts both leaves
and rejects every pair, with leaf state $a$, branch state $d$, and
constant pair transition $d$. Its leaf-state orbit is
$(a,a),(a,d),(d,d),(d,d),\ldots$, so $\mu=2,\lambda=1$.
On original $\alpha$, epoch two is
$\langle\beta,\alpha\rangle$, selecting $\{L,R\}$.
Epoch three is
$\langle\langle\beta,\alpha\rangle,\beta\rangle$,
selecting $\{LL,LR,R\}$. The fixed epoch-two selected boundary
holds at $2$ and fails at $3$, refuting a cap at $\mu$.
The missing premise is saturation of the particular cut addresses;
$B_0$ in Theorem 4.2 supplies it. $\square$

**Proposition 9.3 (blocked and ground rows).** A truthful blocked
bare row can have no selected producer history, and a valid empty-cut
row can be excluded solely by its concrete leaf states.

Proof. Take $P=\{LL\}$ and $C=\alpha$ with no holes. This is a
row-valid bare row, realized by $u=\alpha,n=0$, since the root leaf
blocks the requested address. It is never a selected output because
selected cuts contain only present positions. For $P=\varnothing$
and the same $C$, selection validity holds, but the selector accepting
$\alpha$ selects the root instead. These are different reasons for
rejection. The finite syntax validation handles the first, and
(NRF.6) at the concrete root handles the second. Every ground row
has the empty residual tuple, not an omitted case. $\square$

## 10. Resource interpretation and mathematical scope

**Definition 10.1 (separate finite costs).** Representation size is
the size of the public descriptions of the patterns, ground constants,
finite state domains, equality types, truth labels and arithmetic
guards. Decision work is the work of constructing these descriptions,
expanding their fixed ground terms, enumerating their finite choices,
and reaching the capped fixed points. These differ from materializing
an actual residual valuation, its decoded source, or
$\rho^{n+j}u$ for an actual unbounded $n,j$.

For a valid row there are
$|J|=B_0+\mu+\lambda\le B_0+|Q|^2$ representatives. A direct
product has at most $|Q|^{|J|}$ states; identical coordinate
automata can be shared without changing the construction. For a
pattern with $v$ raw variables and $g$ distinct ground constants,
there are at most $\operatorname{Bell}(v+g)$ equality types before
excluding those that merge constants. With $k$ free blocks and
$N_M$ product states there are at most $N_M^k$ state assignments.
The capped count computation needs at most $(k+g)N_M$ strict
vector increases when $k>0$, each scanning its finite transition
table. These are sufficient finite construction bounds, not
polynomial or optimal-size bounds. A product augmented by $B$ in
Theorem 7.3 has the additional $|Q_B|$ factor.

All residual languages in (NRF.22) remain present. A finite
representative list limits only the capacity certificate, not the
possible source sizes. Constructor derivations can describe large
finite terms, whose literal expansion has its own cost. Actual
$\rho^{n+j}$ expansion is likewise separately charged; a compact
arithmetic guard is not cheap physical execution of its exponent.

The actual observer of Assumption 3.1 pays its entire full-capture
cost. In empty-cut RA, for attempt $i$ let $d_i$ be the guard-leaf
address length and $E_i$ its exterior Read addresses. The existing
exact CWS account specializes to

$$
T_i=d_i+2+|E_i|,\qquad
A_i=\frac{d_i(d_i+1)}2+d_i+\sum_{p\in E_i}|p|,
\tag{NRF.42}
$$

where $T_i$ counts Reads and $A_i$ counts all delivered literal
address letters. Failed attempts are included. On success $E_i$
contains every node of the captured tree. If $b_*$ is the actual
number of updates through outer Return, and $N_*,H_*$ are size
and height of $\rho^{b_*}u$, the supplied bounds give at most
$b_*+1$ attempts, at most
$(b_*+1)(N_*+H_*+2)$ Reads, and at most $H_*$ times that many
address letters. These are retrospective analysis parameters,
not source advice, retained counters or an interference promise.

After capture, one state evaluation per acquired node suffices for
$A$ if table lookup is charged separately. Selection, address
construction, exact subtree comparison and full partition formation
are additional finite local work. They require no further source
Reads but use paid acquired data. Temporary storage includes the
full acquired tree, state information if stored, comparison workspace,
output preparation and control. Cleanup also has a cost. The finite
relation construction is a mathematical decoder on public $A,b$;
it is not secretly inserted into the producer or supplied as
source-specific initialization.

Final retention is the canonical selected row and declared public
code and parameters. Its addressed holes already determine $P$, so
encoding $P$ once is lossless. In the CWS sixteen-symbol encoding,
if the exterior uses $c$ cells and has $h$ holes, the row uses
$c+\binom h2+2$ cells, four bits each, including every false
partition bit. Other lossless encodings may use canonical class
numbers; no globally minimal representation is asserted. All
public code storage, address bytes and actual accessible fields
remain part of their appropriate resource accounts.

**Proposition 10.2 (finite representation is not sparse-acquisition optimality).**
The existence of Theorem 6.6 and a small retained selected boundary
does not make the prescribed full-capture observer globally optimal
in Reads or storage.

Proof. If $F=Q$, the selected boundary is always the constant root
hole and singleton partition. A different native observer can take
one root Read as its designated validation, discard its reply in
canonical handoff, and return that constant boundary. On arbitrary
finite sources it has the same source/count relation (NRF.8), with
any $n$ updates before its Read and any $j$ afterwards. The
prescribed full-capture implementation nevertheless reads every
captured node on its successful traversal. Those trees have no
uniform size bound. Thus the finite representation and equal final
retention cannot refund the latter observer's acquisition cost or
prove its global optimality. $\square$

**Definition 10.3 (scope of the constructive relation).** The family
has one paid full capture, one public regular selector applied to
that capture, and one complete handoff. Theorems 3.2 and 6.6 preserve
the entire source/count relation for this family, not arbitrary raw
histories. They neither characterize arbitrary adaptive recaptures
or signed cross-capture links nor decide support of arbitrary
programs. They do not establish global minimum memory, optimal sparse
observation, physical spacetime recovery or recovery of physical
duration. Those broader questions remain open here. The mutual
recovery of Section 8 is of precise finite spatial boundaries on
this actual selected relation; the temporal coordinates remain
actual update counts with the explicit recovery conditions above.

## 11. Mathematical sources and transfer conditions

**Mathematical citation 11.1 (reused native results).** The following
suppliers retain their original hypotheses and conclusions. The
selector-specific additions are (NRF.6)–(NRF.7), their actual producer
composition (NRF.8), the automaton extension of the same-source epoch
law (NRF.12), and the finite original-source presentation and its
consumers (NRF.22)–(NRF.40). These are repository-derived ordinary
mathematical constructions; no worldwide priority assertion is made.

| Source | Mathematical scope used here |
| --- | --- |
| [NUE, Definition 1.2, Proposition 1.3, Theorem 2.2][NUE] | Proposed-row validation, exact filling, and same-original stabilization of equality to each fixed complete row. It does not include regular selection. |
| [NSF, Theorem 5.2 and Lemma 9.2][NSF] | Existing fixed-numeral signed feasibility; deep-prefix saturation, reached transport and injectivity. Arbitrary regular guards are not silently added to that feasibility interface. |
| [NCE, Theorems 4.2 and 5.1, Proposition 5.2][NCE] | Existential unknown-epoch support with simultaneous witnesses; witness replacement is distinct from the all-source decoder (NRF.23). |
| [NativeCutFibers][CUT] and [its Scribe][CUT-S] | `LegalValues`, `legal_values_row`, `rowFiberEquiv`, and their private inverse and distinctness helpers retain actual shared fillers and all different-class inequalities. |
| [ActualCutPartitionDecoder][ROW] and [its Scribe][ROW-S] | `literalRecord` and `canonicalRow_record_iff` identify the full addressed exterior and complete partition with canonical row information. |
| [NativeDepthPatterns][DEPTH] and [its Scribe][DEPTH-S] | `original_present_transport` and exact original-prefix decompositions apply to actually present positions; they do not transport absent positions backwards through birth. |
| [CWS, Theorems 3.3–3.4 and §4][CWS]; [CNA, §§2–5, 7][CNA] | Paid native acquisition, validation safety, finite-interference liveness and endpoint limitations. The empty-cut instance acquires a whole tree. |
| [CAB, Definition 1.3][CAB] | Complete accessibility handoff and separate validation/Return events, without physical-erasure or free-clock claims. |
| [ARH, Lemma 11.2][ARH] | The unique ground image parser and injectivity; only that ground inverse is needed in (NRF.17)–(NRF.21). No general synchronous source-constructor relation is assumed. |
| [SLH, Theorem 61.1 and Proposition 61.2][SLH] | Full residual domains distinguished from capped distinct-representative witnesses; a feasibility witness is not the actual unknown source. |
| [TargetRecoveryCriterion][REC] | Constancy on actual observation fibers, with the inhabited-domain or attained-image qualification. |

**Mathematical citation 11.2 (tree automata, sharing and morphic iteration).**
The automata and matching ingredients are literature-attested; their
native combination above is not attributed to a general closure or
ultimate-periodicity theorem.

Joost Engelfriet, *Tree Automata and Tree Grammars*, DAIMI FN-10
(1975), author-uploaded [arXiv:1510.02036][ENG], Theorem 3.8 gives
determinization, Theorem 3.32 Boolean closure, and Theorem 3.65
closure under linear tree homomorphisms. Here the ranked signature
is exactly $\alpha:0,\beta:0,\langle-,-\rangle:2$.
Each $\rho^r$ replaces the leaves by fixed finite ground trees
and sends the binary constructor to itself with each child used
once. Thus its image of a regular language is effectively regular.
For example the finite grammar

$$
S\longrightarrow\rho^r\alpha\mid\rho^r\beta\mid\langle S,S\rangle
\tag{NRF.43}
$$

denotes exactly $\rho^r[\mathcal T]$, with independent child
derivations. Expanding its two finite ground right sides and
applying determinization provides an alternative whole-root image
recognizer. It would test the complete filled root, not individual
born holes. The original-source construction above instead uses
the explicit inverse-image state calculation (NRF.19), and so
does not need an image automaton in its representation. Repeating
a class variable in $C$ is a different, nonlinear operation;
linear-image closure cannot remove its equality constraints.

Luis Barguñó, Carles Creus, Guillem Godoy, Florent Jacquemard and
Camille Vacher, *Decidable Classes of Tree Automata Mixing Local
and Global Constraints Modulo Flat Theories*, LMCS 9(2:1) (2013),
[arXiv:1302.6960v2][BCGJV], Definition 3.2, Example 3.3, Theorem
5.22 and Corollaries 5.23–5.24 describe the relevant distinction
between ordinary regular languages and global subtree constraints,
and decidability of emptiness for their stated classes. The finite
ranked trees and empty equational theory here meet that ambient
setting. In a fixed-context translation, each designated hole root
can receive a marker used nowhere inside fillers; constraints between
those markers then compare exactly the intended whole subtrees.
Their universal disequality constraint is not the negation of their
universal equality constraint. The present proof instead explicitly
compares every finite pair and uses disjoint deterministic-state
capacities in (NRF.29). It imports neither general constrained-language
complementation nor universality to justify Theorem 7.1.

Fabien Durand, *Decidability of the HD0L ultimate periodicity problem*,
[arXiv:1111.3268v3][DUR], §1.1 and Theorem 1, treats a supplied word
seed and two supplied morphisms, asking about an ultimately periodic
infinite-word limit. Prefix serialization of native trees intertwines
$\rho$ with the word morphism $a\mapsto b$, $b\mapsto pba$,
$p\mapsto p$, where $p$ marks a binary pair. That correspondence
does not make the HD0L theorem a sourcewise periodicity law for
unknown finite trees and selected boundaries. The proof of Theorem
4.2 uses the explicit finite $Q^2$ orbit, actual reached positions,
injectivity and the supplied fixed-row theorem; its quantifiers and
endpoint claims are established there directly.

[NUE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_UNKNOWN_EPOCH_GLUING.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CROSS_EPOCH_RELATIONS.md
[CNA]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md
[CWS]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_WORKSPACE.md
[CAB]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_ACQUIRED_CLOCK_BRIDGES.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[CUT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[CUT-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.scribe.cs
[ROW]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[ROW-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.scribe.cs
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[DEPTH-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.scribe.cs
[REC]: ../../../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean
[ENG]: https://arxiv.org/pdf/1510.02036
[BCGJV]: https://arxiv.org/pdf/1302.6960v2
[DUR]: https://arxiv.org/pdf/1111.3268v3

## 追加锚（本行以下为增补区）

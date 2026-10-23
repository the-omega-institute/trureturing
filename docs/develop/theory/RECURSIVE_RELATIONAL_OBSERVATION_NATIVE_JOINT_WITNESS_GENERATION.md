# Higher-order generation of joint finite native witnesses

## 1. Entire sources and the joint prefix predicate

**Definition 1.1 (native values and four replies).** Throughout,

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\\
\rho\langle s,t\rangle&=\langle\rho s,\rho t\rangle,\qquad
T_j=\rho^j\alpha.
\end{aligned}
$$

These are nonempty finite ordered trees. Pairing is free; $\rho$ is the
displayed interpreted substitution. An expression uses finite native
grounds, pairing, variables and supplied numeral powers of $\rho$.
Repeated occurrences of a variable denote one whole value. Numerals
are fixed in each input, with no common bound across inputs.

An original address is a word over $\{L,R\}$. Write $r_u(p)$ for
$\alpha$, $\beta$ or $\mathsf{branch}$ at a reached address, and
$\mathsf{absent}$ otherwise. Descendants of an absent address remain
absent. For $n,h\in\mathbb N$, put

$$
\begin{aligned}
u\simeq_n v
&\iff\forall |p|<n\quad r_u(p)=r_v(p),\\
u\equiv_h v
&\iff\forall |p|\le h\quad r_u(p)=r_v(p).
\end{aligned}
$$

Thus $\simeq_0$ is universal and $\equiv_h$ is exactly
$\simeq_{h+1}$. The strict-depth notation will be used for generated
certificates; the target predicate always uses inclusive depth.

**Definition 1.2 (complete row and retained input).** For a finite
prefix-free original cut $A$, the complete row $R_A(u)$ comprises
the reached subset $A\cap\operatorname{Pos}(u)$, the entire concrete
exterior obtained by putting numbered holes at those reached positions,
and the full equality partition of their whole subtrees. Hole numbers
are assigned in the fixed address order. Two different partition classes
require unequal values. An empty cut retains the whole source.

Fix a complete acquired input $I$. Its predicate $\Theta_I(u)$ is the
conjunction of its complete old row at $P$, all actual-epoch literal
records, all signed records, and every retained native guard and
off-task constraint. A literal $(a,p,c)$ means
$r_{\rho^a u}(p)=c$, including $c=\mathsf{absent}$ when present in the
input. A signed record $(a,p,b,q,\bowtie)$ means exactly

$$
p\in\operatorname{Pos}(\rho^a u)\ \land\
q\in\operatorname{Pos}(\rho^b u)\ \land\
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q,
\qquad \bowtie\in\{=,\ne\}.
$$

An absent endpoint falsifies either sign. All repeated records are
conjuncts on the same original source. The native guard vocabulary is
the one of [NSF, Definitions 1.1–1.2 and Lemma 5.1][NSF]: fixed
navigation and reached tests, finite native expression comparisons,
complete-row tests, and their specified Boolean combinations. Fixed
native image conditions, when retained, have the actual semantics in
Definition 3.2 below. Native rank coordinates introduced by the
[NIC][NIC] image cover describe these same original conditions; they
are not additional arbitrary scalar inputs.

Let $D=\{u\in\mathcal T:\Theta_I(u)\}$. At the target cut $Q$ take a
supplied finite list $B=\{r_1,\ldots,r_m\}$ of distinct attained
complete rows, where $m\ge2$, and put

$$
\begin{aligned}
D_i&=\{u\in D:R_Q(u)=r_i\},\\
J_B(h)&\iff
\exists(u_1,\ldots,u_m)\in\prod_{i=1}^mD_i
\quad\forall i,j\quad u_i\equiv_hu_j.
\end{aligned}
$$

The list $B$ need not exhaust the target image. Every $D_i$ is its
entire stratum; no other row is removed from $D$. These definitions
reuse the source and row semantics of NSF and NIC, and the joint
predicate of [SPC, §9][SPCEXT]. The sources indexed by different
rows are alternative originals. Within one alternative all shared
occurrences remain identical.

**Assumption 1.3 (actual acquired interface).** The paid-source and
complete-state contract supplies exactly the accessible fiber $D$, with
authentic final epoch $N$ at least every acquired epoch. All accessible
source-bearing distinctions are included in that contract. This is the
same supplied premise used by [NLC, Assumption 1.2][NLC] and
[SPC, Definition 3.1 and Theorem 3.2][SPC]. No construction of that
interface is part of the generation results below.

## 2. One depth spine and eagerly selected whole values

**Definition 2.1 (finite output semantics and types).** A finite
higher-order recursion scheme is understood in the simply typed
$\lambda Y$ presentation used by [Badyl–Parys, §2][BP]. Its ground
type $o$ is the output-tree type. Use finitely many ranked terminals,
including nullary $\alpha,\beta$, binary $\mathsf p$, binary
$\mathsf{nd}$, and unary $\mathsf{tick}$. Other terminals encode a
fixed finite payload layout, always with arity at most two.

For the possibly infinite generated tree $T_{\mathcal G}$, let
$\mathcal L(\mathcal G)$ consist of the finite trees obtained by
finitely many operations replacing an $\mathsf{nd}$ node by one of
its children, with no $\mathsf{nd}$ or $\mathsf{nd}_{\bot}$ left.
This is precisely [Badyl–Parys, §4][BP] finite-language semantics.
An infinite unfinished choice is not a finite output. Ordinary nodes
cannot be discarded by this operation.

The order convention is
$\operatorname{ord}(o)=0$ and
$\operatorname{ord}(\sigma\to\tau)
=\max(\operatorname{ord}(\sigma)+1,\operatorname{ord}(\tau))$.
Define

$$
V=o\to o\to o,\qquad
K_m=\underbrace{V\to\cdots\to V}_{m\text{ arguments}}\to o,
\qquad D_m=K_m\to o.
$$

Their orders are respectively $1,2,3$.

**Definition 2.2 (deterministic native builders).** The following
equations define finite typed terms:

$$
\begin{aligned}
\mathsf A\,a\,b&=a,&
\mathsf B\,a\,b&=b,\\
\mathsf P\,v\,w\,a\,b
&=\mathsf p\,(v\,a\,b)\,(w\,a\,b),&
\mathsf R\,v\,a\,b&=v\,b\,(\mathsf p\,b\,a).
\end{aligned}
$$

Here $\mathsf A,\mathsf B:V$ and
$\mathsf P:V\to V\to V$, $\mathsf R:V\to V$.
For $u\in\mathcal T$ define its closed builder $[u]:V$ recursively by

$$
[\alpha]=\mathsf A,\qquad [\beta]=\mathsf B,
\qquad [\langle s,t\rangle]=\mathsf P\,[s]\,[t].
$$

Every such builder is finite and contains no choice terminal or
generator call. Structural induction gives
$[u]\,a\,b$ as the tree obtained from $u$ by replacing its
$\alpha$ and $\beta$ leaves by $a$ and $b$. Substituting $b$ and
$\mathsf p\,b\,a$ gives the displayed native $\rho$ laws, so
$\mathsf R[u]$ is a deterministic builder of $\rho u$.
In particular,

$$
[u]\,T_a\,T_{a+1}=\rho^a u.
$$

This follows on the two leaves from
$\rho^a\alpha=T_a$ and $\rho^a\beta=T_{a+1}$, and on a pair from
distribution of $\rho^a$. The right sides $T_a,T_{a+1}$ here are
ground output trees. The numeral $a$ is expanded into a finite term.

For a fixed native expression $E$, its builder $E^{\sharp}(\mathbf v)$
is defined by substituting $v_i$ for variable $x_i$, $[g]$ for a
ground $g$, $\mathsf P$ for pairing and $\mathsf R^a$ for
$\rho^a$. Induction on $E$ proves

$$
E^{\sharp}([u_1],\ldots,[u_m])\,\alpha\,\beta
=E(u_1,\ldots,u_m).
$$

Thus fixed expressions and all required fixed epoch views can be
serialized from the same selected builders.

**Definition 2.3 (whole-value selection).** Use the finite equations

$$
\begin{aligned}
\mathsf{Gen}\,k
&=\mathsf{nd}\,(k\,\mathsf A)
  \bigl(\mathsf{nd}\,(k\,\mathsf B)
                   (\mathsf{Gen}\,(\mathsf{Left}\,k))\bigr),\\
\mathsf{Left}\,k\,x
&=\mathsf{Gen}\,(\mathsf{Right}\,k\,x),\\
\mathsf{Right}\,k\,x\,y
&=k\,(\mathsf P\,x\,y).
\end{aligned}
$$

The types are
$\mathsf{Gen}:(V\to o)\to o$,
$\mathsf{Left}:(V\to o)\to V\to o$ and
$\mathsf{Right}:(V\to o)\to V\to V\to o$; their orders are $3$.
For $m$ coordinates put

$$
\mathsf Q_m\,k
=\mathsf{Gen}\bigl(\lambda x_1.
   \mathsf{Gen}\bigl(\lambda x_2.\cdots
   \mathsf{Gen}(\lambda x_m.k\,x_1\cdots x_m)\cdots\bigr)\bigr).
$$

Here $\mathsf Q_m:D_m$. A constructor choice finishes selecting its
left child, then its right child, before passing their paired builder
to its continuation. Consequently a value passed to the final
continuation is a closed deterministic builder. Reusing that parameter
does not copy an unresolved choice.

**Definition 2.4 (synchronized layer and payload).** Fix any finite list
$\mathcal V$ of coordinate/epoch slots $(i,a)$, including $(i,0)$ for
each $i$. Repetitions are allowed. Add finitely many fixed expression
slots if needed. Serialize these raw finite native values in a fixed
binary list, using a binary terminal $\mathsf{cell}_j$ for slot $j$
and a nullary terminator. Call the resulting tree
$\operatorname{Payload}_{\mathcal V}(\mathbf u)$. Slot wrappers lie
outside the native value subtrees. The source slots make this map
injective. There is no $\mathsf{tick}$ inside a payload.

Let $\mathsf{Emit}:K_m$ serialize slot $(i,a)$ as
$v_iT_aT_{a+1}$ and each expression slot as
$E^{\sharp}(\mathbf v)\alpha\beta$. Define

$$
\begin{aligned}
\mathsf F_m\,g\,k
={}&\mathsf{nd}\,(k\,\mathsf A\cdots\mathsf A)\\
&\bigl(\mathsf{nd}\,(k\,\mathsf B\cdots\mathsf B)\\
&\quad\bigl(g(\lambda x_1\cdots x_m.
  g(\lambda y_1\cdots y_m.
  k\,(\mathsf P x_1y_1)\cdots(\mathsf P x_my_m)))\bigr)\bigr),\\
\mathsf C\,g
={}&\mathsf{nd}\,(g\,\mathsf{Emit})
                  (\mathsf{tick}\,(\mathsf C(\mathsf F_mg))),\\
\mathsf S={}&\mathsf C\,\mathsf Q_m.
\end{aligned}
$$

Both $\mathsf F_m:D_m\to D_m$ and $\mathsf C:D_m\to o$ have
order $4$. The scheme with start symbol $\mathsf S$ is denoted
$\mathcal G_{m,\mathcal V}$. All lambdas can be lifted to finitely
many nonterminals. Each captured variable has type among
$o,V,K_m,D_m$, so the lifted nonterminals have order at most $4$.
The finitely many numeral expansions and payload slots are effective
finite syntax. This is an upper bound on order, with no minimal-order
assertion.

**Theorem 2.5 (all finite joint tuples with certified depth).** For
every finite $m\ge1$, every finite slot list $\mathcal V$ as above,
every $n\in\mathbb N$ and every $\mathbf u\in\mathcal T^m$,

$$
\mathsf{tick}^n\operatorname{Payload}_{\mathcal V}(\mathbf u)
\in\mathcal L(\mathcal G_{m,\mathcal V})
\quad\Longleftrightarrow\quad
\forall i,j\quad u_i\simeq_nu_j.
$$

Every finite output has this form. All its epoch and expression slots
are faithful views of the same whole original values. Agreement includes
original-address absence. The certificate $n$ need not be the first
mismatch depth.

Proof. First consider a finite selection by $\mathsf{Gen}$ before its
continuation is called. Its outer choice either selects $\mathsf A$,
selects $\mathsf B$, or selects a pair. In the pair case both recursive
selections must finish before $\mathsf{Right}$ calls the continuation.
Induction on this finite selection gives exactly the builder $[u]$ of
a finite $u$. Conversely induction on $u$ makes these same choices
and yields $[u]$. No choice remains inside the returned builder.
An infinite sequence of recursive selections cannot give a finite
choice-free output: infinitely many surviving choice nodes would have
to be removed. Therefore $\mathsf Q_m$ selects exactly all finite
tuples, each coordinate once before using its continuation.

Write $\mathcal A_n$ for the tuple family selected by
$\mathsf F_m^n\mathsf Q_m$. At $n=0$ it is $\mathcal T^m$.
The equations for $\mathsf F_m$ give exactly three alternatives:
the all-$\alpha$ tuple, the all-$\beta$ tuple, and

$$
(\langle x_1,y_1\rangle,\ldots,\langle x_m,y_m\rangle)
\quad\text{with }\mathbf x,\mathbf y\in\mathcal A_n.
$$

The two selections in the third alternative are separate selections
of child tuples; their deterministic values are paired coordinatewise.
If all original roots agree through strict depth $n+1$, their roots
are either the same leaf or all branches. In the leaf cases every
strict descendant is absent in every coordinate. In the branch case
the actual left-child tuple and right-child tuple agree through strict
depth $n$. Conversely those two agreements imply agreement through
strict depth $n+1$ of the paired tuple. Induction on $n$ proves

$$
\mathcal A_n
=\{\mathbf u\in\mathcal T^m:
                         \forall i,j\ u_i\simeq_nu_j\}.
$$

This proves both source directions: every derivation produces actual
finite originals, and every requested original tuple is reproduced
with its actual children, not replaced by representative witnesses.
Choosing the continuation branch of $\mathsf C$ exactly $n$ times
leaves $n$ ordinary tick nodes and then
$(\mathsf F_m^n\mathsf Q_m)\mathsf{Emit}$. A finite output must
eventually take its stop branch; an infinite tick spine remains
infinite under finite choice pruning. The builder identities in
Definition 2.2 prove every emitted slot, with the same selected
parameter at every occurrence.

The only tick occurrences are on this one spine, so their number
is exactly $n$. Early common leaves can certify arbitrarily many
layers when the sources are equal. When a tuple first differs at
depth $d$, every $0\le n\le d$ is a valid certificate, whereas
$n=d+1$ is not. No maximality test is imposed. $\square$

## 3. Exact signed checking on the finite payload

**Definition 3.1 (explicit finite evaluation).** On a finite native
tree, whole equality is defined recursively: equal leaves agree,
different leaf labels disagree, a leaf and a branch disagree, and
two branches agree exactly when both ordered children agree. Its
negation is whole disequality. Both recursions terminate on finite
trees. For a fixed word $p$, navigation recursively follows its
letters through branches; reaching a leaf before the word ends
returns absent. For a supplied numeral $a$, first form the entire
finite tree $\rho^a u$ by the laws of Definition 1.1, and then navigate
in that tree.

In particular, epoch-$a$ navigation is not replaced by applying
$\rho^a$ to a nonexistent original subtree. An originally absent
address can be born in an epoch view. Source slot $(i,0)$ keeps its
original absence, independently of any such birth.

Compute a complete row at $A$ by navigating all members of $A$,
replacing exactly the reached subtrees by their numbered holes, and
recursively comparing each pair of reached subtrees. Equality with a
fixed row compares the reached subset, the whole hole context and
every partition bit. It includes all different-class disequalities.
The finite context comparison keeps every uncut concrete subtree.
Boolean complements are taken after evaluating the reach guards;
flipping a sign alone does not complement a guarded record.

**Definition 3.2 (fixed images and retained native ranks).** On finite
values the actual level-$k$ image is
$L_k^{\mathrm{fin}}=\rho^k[\mathcal T]$. Use [NIS, Lemma 2.2][NIS]
at its finite-tree restriction: it is the regular language generated
by the two ground alternatives $T_k,T_{k+1}$ and recursive pairing.
Membership is computed by recursively testing these ground
alternatives and pairing; equivalently, use the finite tree grammar

$$
Z_k\longrightarrow T_k\mid T_{k+1}\mid\langle Z_k,Z_k\rangle.
$$

Ground alternatives are finite syntax, not new scalar terminals.
This language includes images of the two finite leaves. It is not
the language of trees exceeding a minimum leaf depth.

For the normal rank coordinates of [NIC, Assumption 2.1][NIC], use
the supplied canonical normal code $B(u)$. It is computed bottom-up:
the leaves have codes $[0],[1]$; a pair of primitive codes
$[r+1],[r]$ collapses to $[r+2]$; every other pair is retained as
the ordered normal constructor. Thus any retained fixed rank test
is evaluated on the actual code of its named native value. In
particular, if $\kappa(u)$ is the minimum primitive rank in $B(u)$,
the supplied shift identity gives

$$
u\in L_k^{\mathrm{fin}}\iff\kappa(u)\ge k,
\qquad
\kappa(u)=k\iff
u\in L_k^{\mathrm{fin}}\setminus L_{k+1}^{\mathrm{fin}}.
$$

These fixed thresholds have the indicated image semantics. A primitive
rank correlation arising in a NIC piece remains its entire affine
condition together with its native templates and shared residuals.
It is not replaced by independent choices of numbers or independent
threshold tests. On original-source payloads those correlations are
retained by checking the original native equations from which the
cover was obtained. The equivalence is the two-direction cover and
signed pullback of [NIC, Theorems 3.2–3.3 and 4.3][NIC], rather than
an assertion that arbitrary variable-rank relations are regular.
No arbitrary arithmetic predicate is added to the acquired vocabulary.

**Definition 3.3 (finite signed checker).** Choose $\mathcal V$ to
include every required coordinate/epoch view. A repeated endpoint
may have its own additional copy of its whole view. Let
$\mathsf A_{I,B}$ be the following predicate on finite output trees.
Reject unless the tree consists of a finite unary tick spine followed
by the specified payload layout with finite native values in every
slot. Read its source slots $\mathbf u$. Recompute all view and
expression slots by Definition 3.1 and reject if any slot is unfaithful.
For each $i$, evaluate every conjunct of $\Theta_I(u_i)$ and the
complete target equality $R_Q(u_i)=r_i$ by Definitions 3.1–3.2.
Accept exactly when all these tests hold.

This definition is an explicit terminating finite-tree computation:
structural equality, fixed finite substitutions and navigation, finite
hole-context comparison, and the specified finite guard evaluation.
It invokes neither an existential feasibility procedure nor $J_B$.
In particular every positive equation is checked separately even
when several define the same named value or form a cycle.
All signed lists are kept, including off-task and repeated records.
The checker need not check the common prefix, which is certified by
the generator.

**Theorem 3.4 (entire signed acceptance and both source directions).**
The effective finite scheme of Theorem 2.5 and the explicit finite
checker of Definition 3.3 satisfy

$$
\begin{aligned}
\mathcal W_{I,B}
&:=\mathcal L(\mathcal G_{m,\mathcal V})
                       \cap\{t:\mathsf A_{I,B}(t)\}\\
&=\bigl\{\mathsf{tick}^n\operatorname{Payload}_{\mathcal V}(\mathbf u):
 n\in\mathbb N,\ \mathbf u\in\prod_{i=1}^mD_i,
 \ \forall i,j\ u_i\simeq_nu_j\bigr\}.
\end{aligned}
$$

The equality retains every original finite source tuple satisfying
these conditions, not merely an existence-equivalent subfamily.

Proof. For a member of the left side, Theorem 2.5 supplies its finite
original sources, its certified common original prefix and every
faithful slot. The checker tests the old full row, every literal at
its actual epoch, both guards of each signed comparison, its whole
value sign, every remaining constraint and the complete target row.
Thus its coordinate $u_i$ lies in the entire $D_i$.

Conversely take a tuple and numeral on the right side. The completeness
direction of Theorem 2.5 generates those very sources with those very
epoch views. Membership in $D_i$ means all finite tests in
Definition 3.3 hold. All recomputed slots coincide with the generated
slots, so the output is accepted. This also preserves every accidental
equality of different parameter names in an original source. No
normal-coordinate witness replacement, limit tree or selected contact
is used. Distinct $r_i$ imply distinct source values in these accepted
tuples, because one source has one complete $Q$-row. $\square$

**Theorem 3.5 (constraint-automaton presentation of the signed tests).**
On payloads already certified to have faithful slots, the complete
old/target row tests, fixed-coordinate literals, reached endpoint
tests and whole-subtree signs have an effective finite tree-automaton
presentation with global syntactic equality and disequality. The
same holds with the fixed regular image tests of Definition 3.2.
This assertion concerns the signed tests on faithful payloads; it
does not assert that slot faithfulness or arbitrary correlated
variable-rank constraints have such a presentation.

Proof. Give each endpoint occurrence used in a comparison its own
whole-view slot. A fixed path inside that slot determines the endpoint.
Its reachability, an absent literal, any reached label and a fixed
ground exterior are finite-state tests: only finitely many specified
paths and ground trees must be tracked. At a target or old hole,
accept every native filling while checking all the other nodes of
the concrete context. Fixed image conditions use the finite grammar
in Definition 3.2. Finite-state products conjoin these tests.

For each comparison give its first and second endpoints fresh states
$q_e,q'_e$. The finite-state part requires exactly one occurrence of
each, at its designated reached position, and forbids them elsewhere.
Distinct view slots make these two payload positions distinct even
when the original endpoints coincide. Descendants of a marked root
carry unmarked native states, so state marking changes no compared
subtree. Add $q_e\approx q'_e$ for a positive sign or
$q_e\not\approx q'_e$ for a negative sign. For a complete partition,
add one such test for every pair of reached holes, using separate
endpoint copies whenever necessary. If an endpoint is absent the
finite-state part rejects before the global test is considered.

In [Barguño et al., §3][BCGJV], these global atoms universally
compare subtrees at different positions carrying the indicated
states. With exactly one occurrence of each state here, they mean
exactly the intended whole comparison. Their equational theory is
empty, so equality is syntactic native-tree equality. Both positive
and negative atoms are available; a negative atom is not the
Boolean negation of a universal positive atom in general. The
singleton construction avoids that distinction and vacuity.
If a finite-state product splits an endpoint marker into finitely
many state variants, impose its global comparison on every pair of
variants. The regular part still requires exactly one marked position
per endpoint in total. Exactly one variant pair is then nonvacuous,
and it enforces the intended sign. This keeps the construction valid
with simultaneous literal, exterior and image-state information.
All state and transition sets are finite and effectively obtained
from the retained paths and contexts. $\square$

## 4. The exact unboundedness consumer

**Theorem 4.1 (inclusive offset and one unbounded quantity).** For
the entire $I,B$ of Definition 1.2 and every $h\in\mathbb N$,

$$
J_B(h)
\iff
\exists\mathbf u\quad
\mathsf{tick}^{h+1}\operatorname{Payload}_{\mathcal V}(\mathbf u)
                         \in\mathcal W_{I,B}.
$$

Moreover, writing $\#_{\mathsf{tick}}(t)$ for tick occurrences,

$$
\forall h\ J_B(h)
\iff
\forall M\in\mathbb N\ \exists t\in\mathcal W_{I,B}
                       \quad\#_{\mathsf{tick}}(t)\ge M.
$$

If every accepted tree has at most $M$ ticks for a supplied natural
$M$, then $\neg J_B(M)$. No such input-uniform bound is asserted.

Proof. The first equivalence is Theorem 3.4 with $n=h+1$ and
Definition 1.1. For the second, all-depth witnesses supply arbitrarily
large $h+1$ tick counts. Conversely a count at least $h+1$ supplies
one tuple whose original replies agree at every address through $h$.
This tuple witnesses $J_B(h)$. A witness for $J_B(M)$ would yield an
accepted tree with $M+1$ ticks, contradicting the supplied bound.
Counts measure one simultaneous tuple and the same depth for all
its coordinates. No marginal size, longest branch or leaf count is
used. The tuple can change with $h$. $\square$

**Definition 4.2 (the remaining language transfer).** Theorem 4.1
is a representation of the original unbounded alternative by a
concretely filtered finite language. It does not supply a recursion
scheme whose finite language is $\mathcal W_{I,B}$, or a
WMSO+$\mathsf U_{\mathrm{tup}}$ formula defining the checker on
the construction tree. Those are additional mathematical obligations.
The checker evaluates finite negatives before any limiting operation;
they are not required to hold at a common infinite contact.

The [NSF][NSF] supplied-depth feasibility and original-source recovery
remain the available finite decisions. Theorem 2.5 adds a shared
whole-value carrier and Theorem 4.1 identifies its exact depth measure;
neither is a second proof of finite feasibility. The [NIC][NIC]
positive image cover gives a separate parameter presentation of
the positive solutions. Applying $\mathsf F_m$ to an arbitrary
positive-cover selector has no established equation-preservation
property: its all-leaf alternatives and independent child selections
can violate positive definitions. No composition of that selector
with the synchronization construction is assumed here. In
$\mathcal G_{m,\mathcal V}$ all positive definitions remain exact
tests on the fully generated original tuple.

**Theorem 4.3 (the productive native family is retained).** Take the
entire SPC family with

$$
F(y)=\langle\alpha,\rho y\rangle,
\qquad U(x,y)=\langle x,\langle y,F(y)\rangle\rangle,
$$

including its old root row, its full literals, the actual-epoch record
$(1,RL,0,RRR,=)$ and the negative $(0,RL,0,RR,\ne)$.
For its two complete rows $r_0,r_1$ of [SPC, Theorems 3.2–3.3][SPC],
every supplied original witness pair there occurs in the corresponding
accepted slice of $\mathcal W_{I,\{r_0,r_1\}}$.

Proof. SPC identifies the entire strata as
$D_0=\{U(y,y):y\in\mathcal T\}$ and
$D_1=\{U(F(y),y):y\in\mathcal T\}$, with their entire common
exterior and complete finite partitions. Its displayed finite pair
at depth $h$ uses $y=F^{h+1}(\beta)$ and has all original replies
equal through $h$. Every literal, sign and reached endpoint is part
of that supplied theorem. Apply Theorem 3.4 to these actual originals
and $n=h+1$. The emitted epoch-one copy uses the same selected $y$,
so its $RL$ subtree is $\rho y$, while the epoch-zero $RRR$ subtree
is the identical value. The finite inequality $y\ne F(y)$ remains
checked at its original reached endpoints. Thus the original family,
rather than independently reselected occurrences of $y$, is retained.
This is a consumer of SPC's productive result, not a new contact or
non-rationality claim. $\square$

## 5. A generic equality-filter transfer is impossible

**Definition 5.1 (binary-output correspondence instances).** A PCP
instance consists of a finite nonempty alphabet $\Sigma$ and two
morphisms $f,g:\Sigma^*\to\{0,1\}^*$. A solution is a nonempty
word $w\in\Sigma^+$ with $f(w)=g(w)$. This is exactly the binary
codomain and nonempty-input convention of [Nicolas, §1.1][NICOLAS].
Its §1.3 supplies the mature undecidability premise, in particular
already for seven input letters. Empty tile images are not excluded
by the construction below.

Encode a binary word as a finite native tree:

$$
W(\varepsilon)=\alpha,\qquad
W(0v)=\langle\alpha,W(v)\rangle,
\qquad W(1v)=\langle\beta,W(v)\rangle.
$$

For a fixed binary word $a$, let $C_a:o\to o$ be its unary
context, with $C_\varepsilon x=x$ and
$C_{0a}x=\mathsf p\,\alpha\,(C_ax)$,
$C_{1a}x=\mathsf p\,\beta\,(C_ax)$.
Induction proves $C_a(W(b))=W(ab)$. The code $W$ is injective:
an empty word has a leaf root, while a nonempty code has a branch
whose left leaf specifies its first bit and whose right subtree
recursively specifies its remainder.

**Theorem 5.2 (one whole equality defeats generic filtered emptiness
and unboundedness).** From every instance $(\Sigma,f,g)$ effectively
construct a finite scheme $\mathcal P$ of order at most $2$ and a
finite checker $\mathsf E$ using one whole-subtree equality, such that

$$
\begin{aligned}
\mathcal L(\mathcal P)\cap\mathcal L(\mathsf E)\ne\varnothing
&\iff\exists w\in\Sigma^+\quad f(w)=g(w),\\
\mathit{SUP}_{\{\mathsf{tick}\}}
   (\mathcal L(\mathcal P)\cap\mathcal L(\mathsf E))
&\iff\exists w\in\Sigma^+\quad f(w)=g(w).
\end{aligned}
$$

Consequently neither filtered emptiness nor filtered tick unboundedness
is decidable uniformly for arbitrary finite higher-order schemes and
even this single syntactic equality test.

Proof. Let $\mathsf{bundle}$ be a binary terminal. A notation
$\mathsf{nd}_{i\in\Sigma}$ denotes a fixed finite binary choice
cascade, with no choice node needed for a singleton list. Use
parameters $a,b:o\to o$ and equations

$$
\begin{aligned}
\mathsf{Start}
&=\mathsf{nd}_{i\in\Sigma}
      \bigl(\mathsf{Next}\,C_{f(i)}\,C_{g(i)}\bigr),\\
\mathsf{Next}\,a\,b
&=\mathsf{nd}\,(\mathsf{Stop}\,a\,b)\\
&\quad\bigl(\mathsf{nd}_{i\in\Sigma}
    (\mathsf{Next}\,(\lambda x.a(C_{f(i)}x))
                     (\lambda x.b(C_{g(i)}x)))\bigr),\\
\mathsf{Stop}\,a\,b
&=\mathsf{nd}\,(\mathsf{bundle}\,(a\alpha)\,(b\alpha))
                  (\mathsf{tick}\,(\mathsf{Stop}\,a\,b)).
\end{aligned}
$$

The first tile is chosen before $\mathsf{Next}$, excluding the empty
input word. After tiles $i_1\cdots i_k=w$, the two deterministic
context parameters are $C_{f(w)}$ and $C_{g(w)}$: appending tile
$i$ composes $C_{f(w)}$ with $C_{f(i)}$, and likewise for $g$.
Induction on the chosen tile sequence proves this assertion. An
eventual stop and $n$ delay choices therefore give exactly

$$
\mathsf{tick}^n\mathsf{bundle}(W(f(w)),W(g(w))),
\qquad w\in\Sigma^+,\quad n\in\mathbb N.
$$

Conversely every such $w,n$ prescribes a finite choice sequence.
An infinite tile selection retains infinitely many choice nodes;
an infinite delay retains an infinite ordinary tick spine. Neither
is a finite output under Definition 2.1. These observations prove
the displayed output language exactly. Context parameters have
order $1$, and $\mathsf{Next},\mathsf{Stop}$ have order $2$.
Lambda lifting the finite context compositions preserves this bound.

The checker first enforces this finite tick/bundle layout, and then
compares the entire two native subtrees immediately below the bundle.
They are nonempty and at distinct positions. Its only nonlocal test
is their equality. It can also be presented by the singleton
$q\approx q'$ construction of Theorem 3.5, with empty equational
theory. By injectivity of $W$, acceptance is precisely
$f(w)=g(w)$. If there is a solution, its fixed context pair permits
every $n$ through $\mathsf{Stop}$. If no solution exists, no finite
output is accepted. This proves both equivalences. A purported
uniform decision for either left side would decide binary-output
nonempty PCP, contradicting the stated undecidability premise.
$\square$

**Theorem 5.3 (scope of the obstruction).** Theorem 5.2 forbids a
generic effective transfer from arbitrary finite-output higher-order
generation plus one whole equality to the decidable unboundedness
formalism of [Badyl–Parys][BP]. It gives no undecidability result
for the original fixed-$\rho$ acquired fibers of Definition 1.2.

Proof. A uniform decision for the generic filtered language would
apply to the supplied order-two schemes and singleton comparison,
giving the contradiction in Theorem 5.2. In particular,
[Barguño et al., Theorem 34 and Corollary 35][BCGJV] decide emptiness
of the standalone finite constraint automaton, not its intersection
with an arbitrary higher-order finite-output language. An unspecified
intersection closure cannot supply the forbidden decision.
Likewise there is no uniform effective construction of a finite
scheme with exactly that filtered output language: applying the
Badyl–Parys SUP reflection to its tick letter would decide the
second predicate of Theorem 5.2. This rules out a generic accepted-
sublanguage construction as well as a generic direct decision.

The reduction uses freely chosen tile contexts $C_{f(i)},C_{g(i)}$
as productions. It does not produce an acquired input $I$ whose
entire original solution family is that PCP language. Nor does it
produce distinct attained native rows with the required complete
state contract. In particular no translation of those arbitrary
tile contexts into the restricted fixed-$\rho$ acquired relations
has been proved. The native problem can therefore still admit a
specific transfer theorem exploiting its own relations. $\square$

## 6. Full tuple-unbounding logic and separated selections

**Definition 6.1 (the exact logic and its finite types).** Use the full
WMSO+$\mathsf U_{\mathrm{tup}}$ of [Badyl–Parys, §3][BP] on
possibly infinite binary labeled trees. Its set variables range over
finite node sets. Its atomic predicates are label tests on sets,
subset, and left/right child relations on singletons. It allows
conjunction, negation, finite-set existential quantification and
arbitrarily nested tuple unbounding:

$$
T,\nu\models\mathsf U(X_1,\ldots,X_k).\psi
\iff
\forall n\in\mathbb N\ \exists X_1,\ldots,X_k\text{ finite}
\quad
\bigl(\forall i\ |X_i|\ge n\bigr)\land
T,\nu[\mathbf X\mapsto\mathbf X]\models\psi.
$$

Here $k$ is fixed by the formula; the notation allows $k=0$ as in
that syntax. There is one jointly satisfying tuple for each $n$.
First-order variables are shorthand for singleton finite sets.
There are no unrestricted infinite-set or infinite-path quantifiers
and no atomic whole-subtree equality.

The same §3 assigns a finite set $\operatorname{Typ}_\phi$ to
every formula, a truth function on these types, and a compositional
function determining the parent type from its label, free-variable
memberships at the root, and two child types. These are Facts 3–4
and Proposition 5, used here as literature premises, including
their full tuple-unbounding case.

In that case, if $\phi=\mathsf U(X_1,\ldots,X_k).\psi$, its type
has one component for each $A\subseteq\{1,\ldots,k\}$:

$$
\left\{\tau\in\operatorname{Typ}_\psi:
\forall n\ \exists\mathbf X\text{ finite}\quad
\llbracket T\rrbracket_\psi^{\nu[\mathbf X\mapsto\mathbf X]}=\tau
\ \land\ \forall i\in A\ |X_i|\ge n\right\}.
$$

Thus potential types lie in the finite set
$\mathcal P(\operatorname{Typ}_\psi)^{2^k}$. Their parent
composition takes unions of the growing index sets contributed
by the two children, with a fixed root-membership pattern. For
necessity, along unbounded witnesses pass to an infinite subsequence
with fixed root bits, child types and, for each required coordinate,
the child containing the larger part of its set. Witnesses of size
at least $2n+1$ then give size at least $n$ in that child. For
sufficiency, choose the two child witness tuples at the requested
bound, combine their finite sets and add the prescribed root bits.
For finite existential quantification the type is the finite set
of realizable subformula types. Negation retains the subformula
type, and conjunction takes a product. This is why the finite
compositional type premise applies also with negation, finite
auxiliary sets and nested tuple unbounding on infinite carriers.

**Definition 6.2 (canonical independent candidate selections).** Let
$T_G$ be the tree of the ground scheme

$$
G=\mathsf{nd}\bigl(\alpha,
       \mathsf{nd}(\beta,\mathsf p(G,G))\bigr).
$$

For each $t\in\mathcal T$ define its canonical finite selected-node
set $S_t$ in $T_G$. It contains the root and the chosen path of
choice nodes to the root constructor of $t$. An $\alpha$ chooses
the first child of the outer choice. A $\beta$ chooses the second
child, then the first child of the inner choice. A pair chooses
the second child of both choices and includes both corresponding
child selections. At ordinary pair nodes both children are kept;
at leaves the selection ends. This recursively specifies one finite
selection for every finite $t$. Contracting its selected choice
nodes gives exactly $t$, and the constructor alternatives recover
$t$ uniquely. Hence $\mathcal L(T_G)=\mathcal T$ with these
canonical selections.

A separated carrier has two fixed occurrences of $T_G$ below a
fixed finite context. Its free selection tracks restrict to $S_s$
in the first occurrence and $S_t$ in the second; all other tracks
in those occurrences are empty or fixed independently of $s,t$.
For a depth track add a third, disjoint subtree
$T_{\mathrm{clk}}=\mathsf{clk}(T_{\mathrm{clk}})$ and let $H_h$
be its first $h+1$ nodes. Context memberships and any other subtrees
are fixed. Candidate choices do not change the carrier tree.

**Theorem 6.3 (no fixed separated whole-equality or depth validator).**
There is no full WMSO+$\mathsf U_{\mathrm{tup}}$ formula $E(X,Y)$
on the separated carrier such that for all $s,t\in\mathcal T$,
under their canonical selection valuation,

$$
E(S_s,S_t)\iff s=t.
$$

On the carrier with the separate clock there is likewise no formula
$A(H,X,Y)$ satisfying for every $h\in\mathbb N$ and
$s,t\in\mathcal T$,

$$
A(H_h,S_s,S_t)\iff s\equiv_h t.
$$

The claim permits arbitrary finite auxiliary-set quantifiers,
negation and nested tuple unbounding in the formula.

Proof. Fix a proposed formula $\phi$ and let
$M=|\operatorname{Typ}_\phi|$. Define finite combs

$$
c_0=\beta,\qquad c_{j+1}=\langle\alpha,c_j\rangle.
$$

At the second candidate subtree consider its $M+1$ local valuations
with $Y=S_{c_j}$, for $0\le j\le M$, and all other free tracks
empty or the fixed prescribed tracks there. Two indices
$i<j\le M$ have the same $\phi$-type. The first candidate valuation
can now be fixed to $X=S_{c_i}$. Every other context membership
and subtree valuation is the same in the two comparisons.
Proposition 5 of Badyl–Parys propagates the equality of the second
candidate's types through the finitely many ancestors of that
occurrence. Fact 4 therefore gives the same truth value on
$(c_i,c_i)$ and $(c_i,c_j)$. These combs are different, contradicting
the required whole-equality specification.

For the depth specification make the collision with the local
$H$ track empty in the second candidate occurrence, as it always
is. After the collision fix the separate clock to $H_i$ and the
first candidate to $c_i$. These choices do not change either of
the colliding local types. The first discrepancy between $c_i$
and $c_j$ is exactly at $R^i$, of depth $i$: there $c_i$ has label
$\beta$, while $c_j$ is still a branch. All strict prefixes and
their left subtrees agree. Thus $c_i\equiv_i c_i$ but
$c_i\not\equiv_i c_j$. Type propagation again gives equal truth
values, a contradiction. The clock can be chosen after the collision
because it is in a different subtree. Bound auxiliary variables
and all their possible choices are already represented in the full
formula type; no restriction to a finite payload or to MSO has
been used. $\square$

**Theorem 6.4 (scope under changed candidate encodings).** The equality
obstruction also holds if each chosen value is encoded by any fixed
finite number of finite free-variable tracks local to its candidate
subtree, provided that the two codes are independent and the same
fixed finite context combines them. It excludes neither eager
selection before shared emission nor synchronized tuple generation.

Proof. For a fixed formula there are still only finitely many local
types for the second candidate, however its finitely many tracks
encode a value. Apply the pigeonhole principle to an infinite list
of different values, keep the first code equal to one member of
a colliding pair, and propagate types as in Theorem 6.3. Exact
equality demands different answers on the diagonal and off it.
For the explicit depth obstruction one needs an encoded family with
the comb discrepancies used there and a clock outside the replaced
subtree; the canonical carrier supplies both.

In Theorem 2.5 a whole deterministic value is selected before its
multiple occurrences are emitted, and $\mathsf F_m$ jointly selects
all constructors above a common depth. Those occurrences cannot
be replaced independently while keeping the rest of that generation
derivation fixed. They therefore do not meet the separated-code
hypothesis. The type collision also does not rule out an
input-specific formula deciding unboundedness without validating
every independent candidate pair. $\square$

## 7. An actual complete native row consumer of separation

**Definition 7.1 (one fully guarded acquired fiber).** Put

$$
A(x,y)=\langle\langle\alpha,\beta\rangle,\langle x,y\rangle\rangle.
$$

The old cut is $P=\{\varepsilon\}$ with its complete one-hole row.
The actual epoch-zero literal list is

$$
\{(0,\varepsilon,\mathsf{branch}),
  (0,L,\mathsf{branch}),(0,R,\mathsf{branch}),
  (0,LL,\alpha),(0,LR,\beta)\}.
$$

Retain the signed records

$$
(1,LL,0,LR,=),\qquad (0,LL,0,LR,\ne),
$$

the authentic final epoch $N=1$, and target cut $Q=\{RL,RR\}$.
There is no extra source discriminator at the complete cut.

**Theorem 7.2 (entire fiber, both rows and separated-validation
failure).** The entire original fiber of Definition 7.1 is exactly
$\{A(x,y):x,y\in\mathcal T\}$. Its two complete target rows have
reached set $Q$, whole exterior

$$
\langle\langle\alpha,\beta\rangle,
                    \langle\square_1,\square_2\rangle\rangle,
$$

and respectively one partition class $r_=$ or two classes $r_\ne$.
They are both attained, and their entire strata are

$$
D_=\{A(t,t):t\in\mathcal T\},\qquad
D_\ne=\{A(s,t):s,t\in\mathcal T,\ s\ne t\}.
$$

For this fixed input, a fixed full WMSO+$\mathsf U_{\mathrm{tup}}$
validator on independent canonical choices of $x,y$ cannot recognize
the complete row $r_=$ on every candidate. With a separate clock it
cannot recognize every requested inclusive original-prefix comparison
between $A(c_i,c_i)$ and $A(c_i,c_j)$ either.

Proof. The five literals force exactly the displayed constructor
skeleton, leaving precisely its two reached finite native subtrees
$x,y$. At epoch one the left child is
$\langle\beta,\langle\beta,\alpha\rangle\rangle$, so its $LL$
subtree is $\beta$, equal to the epoch-zero $LR$ subtree. The
negative compares the reached original $\alpha$ and $\beta$,
which differ. Thus every $A(x,y)$ satisfies both guards and both
signs, as well as the old complete root row, and every legal source
has this form. This proves both original-source directions.

Both target holes are reached. Their whole subtrees are exactly
$x,y$, so the stated context and the two partitions give all rows
and the exact strata. The equal row is attained by $A(\alpha,\alpha)$,
and the unequal row by $A(\alpha,\beta)$. Under Assumption 1.3 these
are alternative originals of the same supplied acquired input; no
additional acquisition construction or source-bearing field is used.

Use the carrier obtained by inserting independent occurrences of
$T_G$ at $x,y$ in this fixed skeleton, with any row tag in a fixed
finite context. All other literals, old-row tests and history signs
already hold on every finite selection. A validator for $r_=$ would
therefore give the forbidden $E$ of Theorem 6.3. More concretely,
its $M+1$ comb choices give $i<j\le M$ with identical second-slot
types. Keep $x=c_i$ and an equal-row tag fixed. The valuation with
$y=c_i$ represents a member of $D_=$; replacing only its independent
second choice by $c_j$ gives a member of $D_\ne$. Whole-type
composition leaves the formula's truth unchanged, so exact row
validation fails on this actual acquired fiber.

For the original-prefix version fix the first source to
$A(c_i,c_i)$ and compare against a second source with its independent
$y$ slot either $c_i$ or $c_j$, all other slots fixed. The first
original discrepancy is exactly at $RRR^i$, of depth $i+2$.
A proposed comparison formula has finitely many local types for that
replaceable slot. After its comb collision, choose the separate clock
for $h=i+2$. The unchanged types force equal truth on the equal and
unequal prefix cases, which have opposite answers. For
$M=|\operatorname{Typ}_\phi|$ the collision can be chosen with
$i+2\le M+1$. This is a formula-dependent comparison obstruction,
not an exclusion depth for $J_B$. The input itself still contains
the entire two strata above. $\square$

## 8. What the decidable logic supplies and what it does not

**Definition 8.1 (finite resolutions as a logical relation).** On the
construction trees used here, every choice has two existing children
and no choice can produce empty output. A finite complete resolution can be
described by a finite selected-node set containing the root, with
one selected child at each selected choice node and all existing
children at each selected ordinary node, and no selected
$\mathsf{nd}_{\bot}$. The selection is prefix closed and has no
unaccounted continuation at its leaves. Child-direction tracks may
record the choice when needed. These are weak monadic conditions.
Contracting the selected choice nodes gives the resolved finite
output; ordinary successor in that output is the selected finite
path through zero or more intervening choice nodes. This path
relation is also weak monadic, since each witnessing path is finite.

In $T_{\mathcal G_{m,\mathcal V}}$ every successful complete finite
resolution has one payload root $z$. Its selected tick ancestors
are exactly the $n$ nodes on the certificate spine. To express
unboundedness of accepted outputs it would suffice to supply a legal
formula for acceptance of that selected resolution and to use

$$
\mathsf U X.\ \exists_{\mathrm{fin}} S\ \exists z\quad
\operatorname{Resolution}(S,z)
\ \land\ X=\{v\in S:v\text{ is a tick ancestor of }z\}
\ \land\operatorname{Accept}_{I,B}(S,z).
$$

The equality describing $X$ is a weak monadic set equality, not
whole-subtree equality. The term $\operatorname{Accept}_{I,B}$ in
this displayed specification denotes the finite checker semantics
of Definition 3.3; no definability of that term is assumed. It is
not an added predicate in the Badyl–Parys syntax.

**Definition 8.2 (the model-checking transfer obligation).** The
required effective translation would supply a finite recursion scheme
and a legal full WMSO+$\mathsf U_{\mathrm{tup}}$ sentence whose truth
is equivalent to the accepted tick unboundedness of Theorem 4.1 for
each entire native input $I,B$. Its decision consequence would be
the following application of [Badyl–Parys, Theorem 2][BP]; it is not
an additional construction of the translation. Theorems 2.5–4.1
do not supply it.

Given such a translation, apply the supplied model-checking theorem to that finite
scheme and legal sentence. Truth gives $\forall h\ J_B(h)$ by
Theorem 4.1; the existing NSF finite supplier gives actual original
tuples at each requested depth. Falsity gives existence of a failed
finite depth. Enumerate $h$ using that same terminating supplied-depth
decision and stop at its first failure; the proven existence of
such a depth makes this search terminate. This distinguishes the
positive logical decision from a supplied numerical bound. If a
bound on accepted tick counts is also provided, Theorem 4.1 gives
the direct offset $H=M$.

Badyl–Parys requires the finite scheme and legal sentence as input.
Its SUP reflection, Theorem 8, reflects the actual unfiltered finite
language of a supplied scheme. Its finite-transducer closure,
Theorem 10, requires the stated finite transducer, including its
no-output-cycle condition. Neither theorem inserts an arbitrary
computable whole-value test into node labels. Theorem 5.2 excludes
a generic equality-filter transfer, and Theorem 6.3 excludes the
specified fixed separated validator. A native-specific correlated
translation can meet neither obstruction's hypotheses and remains
a distinct possibility.

**Definition 8.3 (unchanged unrestricted obligation).** For arbitrary
entire $I$ and finite distinct attained $B$ with $|B|\ge2$, the
unresolved task is an effective native-specific decision between
$\exists H\ \neg J_B(H)$ and $\forall h\ J_B(h)$, with actual
finite witnesses on request in the latter case. A finite generator
and full-subtree checker are a representation, not automatically
a recursion scheme or legal logic formula for the accepted sublanguage.
Fixed image semantics, correlated native ranks, every positive
definition, full exteriors and partitions, and finite guarded negatives
must all survive any proposed translation.

The closed-value comparisons of [SPC, §7][SPCEXT], its ordinary
finite-state obstructions in §8 and its separate owned-lift analysis
in §9 are separate existing results. No closed functional class,
rational contact, fixed rank choice, preselected limit or separate
marginal unboundedness replaces the target here. [NLC, §§4–6][NLC]
supplies native leaf-depth and supplied constructor-context decisions
at their stated scopes; this does not identify source size with
common full-prefix depth. The statements here concern finite native
sources and their mathematical presentations.

## 9. Mathematical attributions

**Definition 9.1 (repository dependencies).** [NSF][NSF], *Native
signed feasibility and bounded observation interfaces*, supplies the
native syntax, complete signed-source semantics, finite observation
compilation and original-source recovery. [NIC][NIC], *Finite native
image covers and the raw prefix-cost boundary*, supplies the
positive image cover, original-native signed pullback and complete
row strata. [NIS][NIS], *Native image saturation for recursive
relational observation*, supplies actual image parsing at fixed
levels. [NLC][NLC], *Native minimum leaf depth and exact
constructor-context contact*, supplies the leaf-depth and supplied
contact scopes. [SPC][SPC], *Finite signed native witness production
and non-rational pair contact*, supplies the whole productive family
consumed in Theorem 4.3; [its extended §§7–10][SPCEXT] supplies the
closed-comparison and existing obstruction boundaries cited above.
These results are reused within the exact domains stated here.

**Definition 9.2 (primary literature dependencies).** Anita Badyl and
Paweł Parys, *Extending the WMSO+U Logic With Quantification Over
Tuples*, [arXiv:2311.16607v1][BP], supplies the finite scheme model
in §2, the full logic and finite compositional types in §3, and
the model-checking, finite-output, reflection and transducer
theorems cited in §§4 and 8 above. Its published counterpart is
[CSL, article 2][BPDOI]. Luis Barguño, Carles Creus, Guillem Godoy,
Florent Jacquemard and Camille Vacher, *Decidable Classes of Tree
Automata Mixing Local and Global Constraints Modulo Flat Theories*,
[arXiv:1302.6960][BCGJV], supplies the precise global-constraint
semantics of §3 and the standalone emptiness statements of §5.
François Nicolas, *(Generalized) Post Correspondence Problem and
semi-Thue systems*, [arXiv:0802.0726][NICOLAS], supplies the binary
codomain, nonempty solution convention and undecidability premise
in §§1.1 and 1.3.

The order-four synchronized native carrier and its exact accepted
family correspondence, the order-two PCP filter construction, and
the separated-selection obstruction with its complete acquired-fiber
consumer are the deductions proved in this volume. The cited
literature's general theorems are premises of those deductions,
rather than claims of a new model-checking, automata-emptiness or
PCP theorem. The generic and separated obstructions have exactly
the hypotheses stated in Theorems 5.3 and 6.4.

[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[NIS]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_SATURATION.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[SPCEXT]: https://github.com/the-omega-institute/trureturing/blob/db23810980530aea4b6fc2a056615460c8cbecb9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[BP]: https://arxiv.org/html/2311.16607v1
[BPDOI]: https://doi.org/10.4230/LIPIcs.CSL.2024.2
[BCGJV]: https://ar5iv.labs.arxiv.org/html/1302.6960
[NICOLAS]: https://ar5iv.labs.arxiv.org/html/0802.0726

## 追加锚（本行以下为增补区）

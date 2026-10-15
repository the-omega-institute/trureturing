# Native finite-menu minimal memory and initial-vector completeness

## 1. The task and its mathematical suppliers

For the exact initial family $\mathcal F_D$ defined below and a fixed
public finite menu, the initial selected-reply vector and a supplied
update count determine every future selected reply exactly when the
menu, after removal of its initial $R$, contains every prefix of each
of its members. The empty menu is allowed. The necessity
has concrete height-bounded source witnesses for every missing proper
prefix; sufficiency gives a finite decoder. Section 5 states and proves
this criterion in full.

[DEV], *Adaptive acquired references and the retention frontier*,
revision `142f723c`, supplies the finite-menu solution in §§12.1–12.10:
spatial response statistics, the sharp horizon, constructor overlap,
pruned codes, exact counts, bounded common representatives, minimum
retained alphabets and paid conditional capture. Those results are
credited premises here. Their proofs are not additional contributions
of this companion. The initial-vector criterion and its witnesses are
from [PRIOR, Theorem 7.2]; they are not stated in [DEV]. The symbolic
bit bounds and the useful task boundaries are retained below with
proofs or precise supplier statements.

The distinction between the supplier's tasks matters. [DEV, §10]
optimizes fresh native acquisition of an **unknown** lag after bounded
retention on a phase-minimum family. Its §11 supplies the count and
optimizes the number of fixed public ray coordinates. Its §12 supplies
the count and optimizes arbitrary complete retained information for the
finite initial family used here. These are different interfaces and
different resource objectives.

This is ordinary handwritten, `repo-derived` mathematics. Generic
same-input/different-output separation is background. The uncovered
content is relative to [DEV], with the inherited proof credited to
[PRIOR]; external originality is unverified. The source identities and
statement correspondence are fixed in §10.

## 2. Native definitions and the complete interface

**Definition 2.1 (finite trees, update and literal values).** Let
$\mathcal T$ be the finite nonempty ordered full binary trees generated
by leaves $\alpha,\beta$ and pairing $\langle x,y\rangle$. Leaves have
height zero, and

$$
\operatorname{height}(\langle x,y\rangle)
 =1+\max(\operatorname{height}(x),\operatorname{height}(y)).
$$

The one-register update is

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{FM.1}
$$

A literal is a finite word over $\{L,R\}$; $\varepsilon$ is the empty
word. The reached addresses of $u$ form $\operatorname{Pos}(u)$.
At a reached $q$, $\operatorname{val}(q,u)$ is $\alpha$, $\beta$ or
$\mathsf{br}$ according to its constructor. If a leaf at a strict
prefix blocks navigation, its value is $\mathsf{abs}$. The root is
always reached. The notation $u|_a$ is used only at a reached address.
An actual $\operatorname{Read}(q)$ submits the entire materialized
literal and obtains its value at that event. Computing the same value
from retained data creates no Read event. These are the native objects
of [DEV, Definitions 1.1–1.4].

**Definition 2.2 (exact initial family and relative menu).** Fix public
$D\ge1$ and

$$
\begin{aligned}
\mathcal F_D
 &=\{\langle\alpha,v\rangle:v\in\mathcal T,
                              \operatorname{height}(v)\le D\},\\
A_D&=\{p:1\le |p|\le D,\ p\text{ begins with }R\},\\
P&\subseteq A_D,\qquad S=R^{-1}P=\{q:Rq\in P\},\\
S_L&=\{r:Lr\in S\},\qquad S_R=\{r:Rr\in S\},\\
d(S)&=\begin{cases}-1,&S=\varnothing,\\
\max_{q\in S}|q|,&S\ne\varnothing.
\end{cases}
\end{aligned}
\tag{FM.2}
$$

Menus may be empty or nested; they need not be prefix-free. The relative
menu can contain $\varepsilon$, and its words have length at most
$D-1$. A public ordering fixes every vector's order. Since
$\operatorname{height}(\langle\alpha,v\rangle)=1+\operatorname{height}(v)$,
this is exactly [DEV, Definition 11.1]'s family, not a smaller family.
Deleting the initial $R$ is a relabeling of queries, not a source
operation. Homomorphism gives the relative-menu identity used in
[DEV, (AAR.61) and Theorem 12.6]:

$$
\operatorname{val}(Rq,\rho^k\langle\alpha,v\rangle)
 =\operatorname{val}(q,\rho^k v)
 \quad(q\text{ any literal},\ k\ge0).
\tag{FM.3}
$$

The outer root remains a branch, so this identity includes an empty
suffix and every blocked suffix.

**Definition 2.3 (arbitrary complete retained state).** At a specified
initial capture the actual source is $t\in\mathcal F_D$. A deterministic
encoder retains $m(t)$ before the future count is supplied. Every other
accessible source-dependent distinction is a fixed function of $m(t)$
and public $D,P$ and program data. This condition includes control,
prior outputs, reply latches, query histories, descriptors, pointers,
region identities, readable lengths, capacities and allocation metadata.
It is a condition on the entire handoff, not on one named variable.

A passive deterministic decoder receives that state and an exact
$k\in\mathbb N$ with the authentic same-root, same-register promise
$U_w=\rho^k t$. It has no fresh source access and must return

$$
V_P(U_w)=\bigl(\operatorname{val}(p,U_w)\bigr)_{p\in P}
\tag{FM.4}
$$

for every initial source and every nonnegative count. The minimized
quantity is the number of reachable initial retained states, or the
width of a fixed binary name for them. The supplied count is separate.
The code does not authenticate the history promise.

**Definition 2.4 (separate charges).** A fixed-width $b$-bit payload has
at most $2^b$ values, with one empty codeword at $b=0$. Source-independent
code, public menus and preprocessing, initial acquisition, communication,
encoder and decoder workspace, local bit/cell work, output storage and
cleanup have separate costs. Acquisition, transmission and working
representation of $k$ are also paid; an integer is not one unbounded
unit-cost cell. For the actual submitted words $p_1,\ldots,p_T$ charge

$$
T,\qquad A=\sum_{i=1}^T|p_i|,\qquad
Q_{\mathrm{operand}}=
\max\bigl(\{0\}\cup\{|p_i|:1\le i\le T\}\bigr)
\tag{FM.5}
$$

separately. Repeated submissions count repeatedly. Inaccessible physical
remnants still have a storage cost. The information-state optimum is
not an optimum of all these resources.

## 3. Credited atomic law, spatial signatures and horizon

**Mathematical citation 3.1 (the full atomic path law).** Put
$s(q)=\#_L(q)+2\#_R(q)$, $e(\alpha)=0$, $e(\beta)=1$ and
$T_n=\rho^n\alpha$. The atomic recursion and guarded path law used
in [DEV, Theorems 12.3 and 12.6] are

$$
T_0=\alpha,\quad T_1=\beta,\quad
T_n=\langle T_{n-1},T_{n-2}\rangle\ (n\ge2),\quad
\rho^k\beta=T_{k+1}.
\tag{FM.6}
$$

For a nonempty $r$, write $\ell(r)=1$ when its last letter is $L$ and
$\ell(r)=0$ when it is $R$. Presence and the reached subtree are

$$
r\in\operatorname{Pos}(T_n)
 \ \Longleftrightarrow\ n\ge s(r)+\ell(r),\qquad
T_n|_r=T_{n-s(r)}\quad\text{when present}.
\tag{FM.7}
$$

The subtree expression is the recursion (FM.6) along legal edges:
$L$ subtracts one and $R$ subtracts two, each from a parent index at
least two. The final-edge guard is exactly the presence condition in
(FM.7). Thus the credited reply table is

$$
\operatorname{val}(r,T_n)=
\begin{cases}
\mathsf{abs},&n<s(r),\\
\alpha,&n=s(r),\\
\beta,&n=s(r)+1,\\
\mathsf{br},&n\ge s(r)+2
\end{cases}
\quad(r\ne\varepsilon\text{ ending in }R),
\tag{FM.8}
$$

$$
\operatorname{val}(r,T_n)=
\begin{cases}
\mathsf{abs},&n<s(r)+1,\\
\beta,&n=s(r)+1,\\
\mathsf{br},&n\ge s(r)+2
\end{cases}
\quad(r\ne\varepsilon\text{ ending in }L).
\tag{FM.9}
$$

At $\varepsilon$ the replies are alpha, beta and branch at indices
$0,1,\ge2$. In particular a final $L$ has no alpha phase. This is the
atomic law stated in [DEV, Theorem 12.3]'s proof, with its stated
supplier attribution.

**Definition 3.2 (initial signatures in the supplier's coordinates).**
For any actual finite $u$ and literal $q$, let
$r_q(u)=\operatorname{val}(q,u)$ and define

$$
(b_q,c_q)(u)=
\begin{cases}
(0,0),&r_q(u)=\mathsf{br},\\
(2,1),&r_q(u)=\alpha,\\
(1,0),&r_q(u)=\beta,\\
(s(r)+2-e(u|_a),\ \mathbf1_{r\text{ ends with }R}),
 &q=ar\text{ is absent, }a\text{ its blocking leaf},\ r\ne\varepsilon.
\end{cases}
\tag{FM.10}
$$

This is [DEV, Definition 12.2, (AAR.57)]. The blocking leaf is reached
and unique. For every initially nonbranch reply, including a reached
leaf at $a=q$, its branch count is
$b_q(u)=s(q)-s(a)+2-e(u|_a)$.

The signature $K_q(u)=(r_q(u),b_q(u))$ of [PRIOR, §3] contains exactly
the same information on attained inputs. From it recover $c_q=1$
precisely for an initial alpha or an initially absent final-$R$ target.
Conversely (FM.10) gives an initial branch when $b=0$, beta when $b=1$,
alpha when $(b,c)=(2,1)$, and absent in the remaining attained cases.
An absent final-$R$ target has $b\ge3$, while an absent final-$L$
target has $b\ge2$. These case correspondences preserve the
alpha-versus-absence distinction at $b=2$.

**Mathematical citation 3.3 (whole future and legal separation).**
[DEV, Theorem 12.3, (AAR.59)–(AAR.61)] proves, for all finite $u$,
all $q$ and all $k\ge0$,

$$
\operatorname{val}(q,\rho^k u)=
\begin{cases}
\mathsf{br},&k\ge b_q(u),\\
\beta,&b_q(u)\ge1,\ k=b_q(u)-1,\\
\alpha,&c_q(u)=1,\ k=b_q(u)-2,\\
\mathsf{abs},&\text{otherwise}.
\end{cases}
\tag{FM.11}
$$

Here $b_q$ is the first branch count, $0\le b_q\le s(q)+2$, and
$c_q=1$ implies $b_q\ge2$. An initial branch stays branch; alpha
has phases alpha, beta, branch; beta has phases beta, branch. An
initially absent target has beta at $b_q-1$, alpha at $b_q-2$ only
when it ends in $R$, and absence at its other earlier counts.
Transport in this formula is at the actual initial blocking leaf,
never at an absent literal.

Equality of the attained signatures is equivalent to equality of
all future replies. In the $K_q$ notation a separator is $k=0$ if
the initial replies differ, and otherwise
$k=\min(b_q(u),b_q(u'))$ when the branch counts differ. At that
count exactly one reply is branch. This explicit choice is a direct
reading of the published formula, not an additional horizon theorem.

For nonempty $S$ the exact menu threshold is

$$
B(S)=\max_{q\in S}(s(q)+2)
     =\max_{p\in P}s(p)=H_P\le2D.
\tag{FM.12}
$$

For the empty menu set $B(\varnothing)=H_\varnothing=0$. Theorem 12.3
of [DEV] proves that every selected reply is branch for every
$k\ge B(S)$, that this is the least uniform threshold over
$\mathcal F_D$ when $P$ is nonempty, and that unequal future vectors
are separated at some common $0\le k<B(S)\le2D$. Its common sharpness
source is $\langle\alpha,\alpha\rangle$: every relative target $q$
first becomes branch at $s(q)+2$ and is beta one count earlier.
For the full menu $B(S)=2D$, including $D=1$.

## 4. Credited normal forms and minimum retained memory

**Definition 4.1 (equivalence and the overlap indicator).** For any
finite relative menu $S$ and finite trees, put

$$
u\equiv_S u'
\quad\Longleftrightarrow\quad
\forall q\in S\ \forall k\ge0,\quad
\operatorname{val}(q,\rho^k u)=\operatorname{val}(q,\rho^k u').
\tag{FM.13}
$$

For nonempty $S$, set $\eta(S)=0$ if every target is $Lr$ with
$r\ne\varepsilon$, and set $\eta(S)=1$ otherwise. Thus
$\eta(S)=1-\delta(S)$ for [DEV, Definition 12.5]'s $\delta$ on
nonempty menus. The empty case is treated separately.

**Mathematical citation 4.2 (complete constructor classification).**
The constructor analysis in [DEV, Theorem 12.6] gives the following
statements simultaneously for every nonempty finite $S$.
Alpha and beta are inequivalent, and alpha is inequivalent to every
branch. Beta can agree with a branch only when $\eta(S)=0$; in that
case, for every $x,y$,

$$
\beta\equiv_S\langle x,y\rangle
\quad\Longleftrightarrow\quad x\equiv_{S_L}\alpha
\quad\Longleftrightarrow\quad x=\alpha.
\tag{FM.14}
$$

The right child is unrestricted. This is one joint identification on
the entire menu, not separately chosen matches at different targets.
The final equivalence uses the same published analysis: on a nonempty
menu the alpha class is the singleton alpha. For branches, in every
case including $\varepsilon\in S$,

$$
\langle x,y\rangle\equiv_S\langle x',y'\rangle
\quad\Longleftrightarrow\quad
x\equiv_{S_L}x'\ \text{and}\ y\equiv_{S_R}y'.
\tag{FM.15}
$$

The exclusions are exhaustive: a target $\varepsilon$ distinguishes
beta from a branch initially; a target $L$ distinguishes absence
from a present child; a target $Rr$ has beta branch time $s(r)+3$,
beyond any branch child's bound $s(r)+2$. If none occurs, all targets
are strictly below $L$ and the joint overlap (FM.14) applies. For
$S=\varnothing$ all trees are equivalent. In particular $\{L\}$
does not permit the overlap, whereas $\{LL\}$ does. These are the
published classification cases, retained as premises without a second
constructor proof.

**Mathematical citation 4.3 (finite grammar, rank and representatives).**
Use [DEV, Definition 12.5 and Theorem 12.6]'s branch-first integer
normal form, with $N(S)=n(S)$:

$$
N(\varnothing)=1,\qquad
N(S)=N(S_L)N(S_R)+1+\eta(S)\quad(S\ne\varnothing).
\tag{FM.16}
$$

For nonempty $S$ put $J_S=N(S_L)N(S_R)$. Its branch codes are
$0,\ldots,J_S-1$, alpha has code $J_S$, and beta has the separate
code $J_S+1$ only when $\eta(S)=1$. Precisely,

$$
\begin{aligned}
e_\varnothing(u)&=0,\\
e_S(\langle x,y\rangle)&=e_{S_L}(x)N(S_R)+e_{S_R}(y),\\
e_S(\alpha)&=J_S,\\
e_S(\beta)&=\begin{cases}
J_S+1,&\eta(S)=1,\\
e_{S_L}(\alpha)N(S_R)+e_{S_R}(\alpha),&\eta(S)=0.
\end{cases}
\end{aligned}
\tag{FM.17}
$$

Only the first line applies to the empty menu. In the overlap case
$S_L$ is nonempty and $S_R$ is empty, so the final line is a well-typed
branch code, not an extra leaf code. Every nonempty child menu has
smaller maximum word length. The recursion is finite, terminating and
prunes unused subtrees by returning zero immediately on an empty menu.

The integer is the rank of its menu-typed form. To unrank $i<J_S$,
take the quotient and remainder of $i$ by $N(S_R)$ and unrank them
in the two child menus. The remaining valid integers select their
leaf tags. Reverse this procedure to construct a representative
$r_S(i)$, using alpha for the empty code and pairing the two child
representatives for a branch code. The supplier proves

$$
\begin{aligned}
e_S(u)=e_S(u')&\ \Longleftrightarrow\ u\equiv_S u',\\
e_S(r_S(i))&=i\qquad(0\le i<N(S)),\\
\operatorname{height}(r_S(i))&\le\max(0,d(S)+1).
\end{aligned}
\tag{FM.18}
$$

Thus (FM.16) counts disjoint actual classes. Each product pair is
realized by one actual full tree formed from its child representatives;
nested targets and shared blockers are not assigned independent
signatures. Every class occurs under every height cap at least
$\max(0,d(S)+1)$. In particular
$\langle\alpha,r_S(i)\rangle\in\mathcal F_D$. The leaf-first ranks
in [PRIOR, §§5–6] name these same classes in a different order;
no equality of the two numerical encodings is asserted.

**Mathematical citation 4.4 (attained arbitrary-state optimum).**
[DEV, Theorem 12.6] applies to Definition 2.3 and gives exactly

$$
\min |m(\mathcal F_D)|=N(S),\qquad
b(D,P)=\left\lceil\log_2 N(S)\right\rceil.
\tag{FM.19}
$$

For any correct deterministic encoding, equality of its complete
retained states must imply equality of $e_S$ on the right subtrees.
The published separation lower bound uses no effectiveness assumption
on that encoding; effectiveness is supplied by the attaining code.
All $N(S)$ lower-bound representatives are in the exact initial family,
and a pair of different codes has a common legal separator below $2D$.

For attainment retain $e_S(v)$ for $t=\langle\alpha,v\rangle$ in the
fixed public width (FM.19). Unrank it, build $r_S(i)$, navigate the
finite representative to obtain (FM.10), and evaluate (FM.11) at the
supplied $k$. Relabel the relative outputs by $q\mapsto Rq$.
This is the supplier's effective representative decoder; it does not
construct the potentially large current tree. A fixed default on
invalid codewords makes it total. Empty $S$ uses one state, zero bits
and the empty output.

The optimum requires the complete-state and cleanup conditions of
Definition 2.3. Recurrence tables, rank arithmetic, public codebooks,
representative construction and their work are finite, not free.
Source-dependent preprocessing, code lengths, pointers or old outputs
remaining accessible outside the exported state enlarge that state.
The generic separation principle used by [DEV] is credited background;
(FM.19) is reuse of its native minimum theorem.

## 5. Exactly when initial selected replies are sufficient

**Definition 5.1 (relative prefix completeness).** A finite menu $S$
is prefix-closed when every prefix of every member, including
$\varepsilon$ and the member itself, belongs to $S$. The empty menu
is prefix-closed. This condition applies after deleting the initial
$R$: it does not require the original root address to belong to $P$.
Write

$$
I_S(v)=\bigl(\operatorname{val}(q,v)\bigr)_{q\in S}.
\tag{FM.20}
$$

**Theorem 5.2 (initial-vector criterion with actual missing-prefix
witnesses).** Fix $D\ge1$, the entire family $\mathcal F_D$ and any
public $P\subseteq A_D$, with $S=R^{-1}P$. The following are equivalent:

1. A single-valued decoder from $I_S(v)$ and supplied $k$ gives every
   future selected vector, for all $\operatorname{height}(v)\le D$
   and all $k\ge0$.
2. One total computable decoder has that property.
3. For all $v,v'$ of height at most $D$,
   $I_S(v)=I_S(v')$ implies $e_S(v)=e_S(v')$.
4. $S$ is prefix-closed, including the empty case.

For every $q\in S$ and every missing proper prefix $a\prec q$,
there are explicit sources $t,t'\in\mathcal F_D$ with identical entire
initial selected vectors and different future vectors at one common
count $k<2D$. The theorem and the path-context construction are credited
to [PRIOR, Theorem 7.2]; the independent constructive proof follows.

Proof. Item 2 implies item 1. By (FM.3) and (FM.18), item 1 implies
item 3: unequal normal forms give different required vectors at a
common count, which a function of the same initial vector cannot
return. We construct the effective reconstruction under item 4 and
then construct witnesses when item 4 fails.

Suppose first that $S$ is prefix-closed. For the empty menu, the empty
vector determines its sole code and every empty future vector. If $S$
is nonempty, it contains $\varepsilon$, and every nonempty child menu
$S_L,S_R$ is prefix-closed. Indeed a prefix $b$ of $r\in S_L$ gives
the prefix $Lb$ of $Lr\in S$, so $Lb\in S$ and $b\in S_L$;
the right case is identical.

The initial root coordinate distinguishes alpha, beta and branch.
If it is alpha or beta, the entire tree is that leaf; its code is
computed by (FM.17), and all selected strict descendants are initially
absent. If it is branch, the entries indexed by $Lr\in S$ are exactly
the initial $S_L$-vector of its actual left child, and likewise on the
right. Induction on maximum menu depth reconstructs the two child
codes; an empty child menu contributes zero without any observation.
Combining them by the branch line of (FM.17) reconstructs $e_S(v)$.
The base nonempty menu $\{\varepsilon\}$ has two empty child menus,
so this induction terminates. It works for every finite actual tree,
not only the height-bounded ones.

This reconstruction also specifies an effective procedure on all
finite input tuples: check that a declared leaf has absent entries
at all its selected strict descendants, reject an absent root in any
nonempty recursive menu, and propagate inconsistent recursive data as
rejection. Missing or malformed tuple entries also cause rejection.
Every check is finite; every attained vector passes. On success use
Citation 4.4's representative decoder at $k$; on rejection return a
fixed default vector of the required size. This is one total computable
decoder, correct on every promised input. Reconstruction proves item 3,
and composition proves item 2.

Now suppose prefix closure fails. Choose any $q\in S$ and missing
proper prefix $a\prec q$, and write $q=ar$, $r\ne\varepsilon$.
Define a one-hole path context by

$$
C_\varepsilon[z]=z,\qquad
C_{Lb}[z]=\langle C_b[z],\alpha\rangle,\qquad
C_{Rb}[z]=\langle\alpha,C_b[z]\rangle.
\tag{FM.21}
$$

Set

$$
v=C_a[\alpha],\qquad v'=C_a[\beta],\qquad
 t=\langle\alpha,v\rangle,\quad
 t'=\langle\alpha,v'\rangle.
\tag{FM.22}
$$

These are actual full trees. Every strict ancestor of $a$ is a branch;
the leaf at $a$ is their only difference. Their right-subtree heights
are exactly $|a|\le|q|-1\le D-2$, so both original sources are in
$\mathcal F_D$. If $a=\varepsilon$, the right subtrees are simply
alpha and beta. Failure of prefix closure is impossible at $D=1$,
whose only possible relative word is $\varepsilon$; thus the displayed
bound creates no missing small-depth case.

The complete initial vectors agree. A selected proper ancestor of $a$
is branch in both trees. A selected strict descendant of $a$ is absent
in both. A selected address incomparable with $a$ takes an unchanged
side subtree and has the same value, including any absence, in both.
The only address whose initial value changes is $a$ itself, and it is
not selected. These cases exhaust every member of $S$.

At the initially reached leaf $a$, the future subtrees are $T_k$ and
$T_{k+1}$. Transport is used at $a$, not at the initially absent $q$.
Take the common count

$$
k=s(r)+1.
\tag{FM.23}
$$

Both final-letter cases of (FM.8)–(FM.9) give beta at $r$ in $T_k$
and branch at $r$ in $T_{k+1}$. Thus the selected original target
$Rq\in P$ has different replies in the two continuations. Moreover

$$
0\le k=s(r)+1\le2|r|+1\le2D-1<2D.
$$

Each source stays on its own register and undergoes exactly these $k$
genuine updates; all public data and the supplied count agree. There
is no change of source within a history. Consequently the common
initial selected vector admits neither a correct single-valued decoder
nor equal normal forms for this pair. Items 1 and 3 fail, hence item 2
fails as well. This proves necessity for every missing proper prefix
and completes all equivalences. $\square$

## 6. Full menus, bit bounds and the separate ray objective

**Corollary 6.1 (the full-menu specialization).** For $P=A_D$ let
$S_d=\{q:|q|\le d-1\}$ when $d\ge1$, and $S_0=\varnothing$.
Then the exact minimum is $C_D$ states and
$\lceil\log_2 C_D\rceil$ fixed bits, where

$$
C_0=1,\qquad C_d=2+C_{d-1}^{\,2}\quad(d\ge1).
\tag{FM.24}
$$

This is the specialization of [DEV, (AAR.66)–(AAR.68)]: the root is
selected, so $\eta(S_d)=1$, and both child menus are $S_{d-1}$.
No additional counting proof is required. Theorem 5.2 further shows
that the initial full-menu vector itself determines every future
full-menu vector, since $S_D$ is prefix-closed.

At $D=1$ the nonempty menu $\{R\}$ has the three right-subtree
representatives alpha, beta and $\langle\alpha,\alpha\rangle$, all of
height at most one; these have distinct root replies and require two
fixed bits. An absent reply at $R$ is impossible. The empty menu has
one state and zero bits. These representatives and counts are also
listed in [DEV, Theorem 12.7].

**Proposition 6.2 (symbolic binary-width bounds).** For every $D\ge1$,

$$
3^{\,2^{D-1}}\le C_D,\qquad
C_D+1\le4^{\,2^{D-1}},
\tag{FM.25}
$$

and hence

$$
\left\lceil2^{D-1}\log_2 3\right\rceil
\le\left\lceil\log_2 C_D\right\rceil\le2^D.
\tag{FM.26}
$$

Proof, as in [PRIOR, Proposition 8.2]. The lower inequality follows
by induction from $C_1=3$ and $C_d\ge C_{d-1}^2$. For $x\ge1$,
$x^2+3\le(x+1)^2$, so (FM.24) implies
$C_d+1\le(C_{d-1}+1)^2$. Induction from $C_1+1=4$ gives the upper
inequality. Taking logarithms gives the lower width bound. The upper
inequality gives $\log_2 C_D<2^D$, whose ceiling is at most the integer
$2^D$. $\square$

**Mathematical citation 6.3 (fixed public ray coordinates).** In
[DEV, Theorem 11.4 and Corollary 11.6], $Q$ is a fixed finite public
set of distinct eventually-right rays and the retained data are the
lossless table

$$
Z_Q(t)=(h_t(\omega))_{\omega\in Q},\qquad
h_t(\omega)=s(a)+e(t|_a),
\tag{FM.27}
$$

where $a$ is the actual leaf on that ray. Its entries advance by $k$
on the genuine continuation. Such a table solves the supplied-count
task exactly when

$$
Q\cap[pR]\ne\varnothing\quad(p\in P),\qquad
Q\cap[aR]\ne\varnothing\quad(aL\in P),
\tag{FM.28}
$$

where $[b]$ denotes the rays with prefix $b$. If

$$
B_P=\{pR:p\in P\}\cup\{aR:aL\in P\},\qquad
B_{P,\max}=\{b\in B_P:\text{no strict extension of }b\text{ lies in }B_P\},
$$

the exact minimum is $|B_{P,\max}|$ coordinates, attained by one
eventually-right ray through each maximal cylinder. It is $2^{D-1}$
for $A_D$ and zero for the empty menu. This is the published ray
count, with its own proof and input restrictions.

| Complete retained interface and minimized resource | Full-menu optimum |
| --- | --- |
| Arbitrary reachable information states | $C_D$ |
| Arbitrary fixed-width binary payload | $\lceil\log_2 C_D\rceil$ |
| Fixed public ray table, number of distinct coordinates | $2^{D-1}$ |

One coordinate may carry several bits; coordinates need not vary
independently, and a lossless table may retain task-irrelevant
information. [DEV, Theorem 12.8] already proves strict alphabet
compression for $P=\{R\}$: the ray $R^\infty$ has exactly the scores
$2,3,\ldots,2D+3$, while its prediction classes are
$\{2\}$, $\{3\}$ and $\{4,\ldots,2D+3\}$. At $D=1$, right subtrees
$\langle\alpha,\alpha\rangle$ and $\langle\alpha,\beta\rangle$ have
scores four and five and the same permanent-branch task state.
Four raw names and three task names both happen to require two fixed
bits there. None of these coordinate counts is an arbitrary-memory
bit lower bound or a free acquisition procedure.

## 7. Counterexamples and count-sensitive consequences

**Mathematical citation 7.1 (the two distinct sampling collisions).**
[DEV, Example 11.5 and Theorem 11.4]'s actual sources

$$
t_\beta=\langle\alpha,\beta\rangle,\qquad
t_{\mathrm{pair}}=\langle\alpha,\langle\alpha,\alpha\rangle\rangle
$$

have the same score three on $Q=\{RLR^\infty\}$. At $P=\{R\}$
their initial replies are beta and branch, with both sources in
$\mathcal F_1$; the missing cylinder is $[RR]$. At $P=\{RL\}$
they give absent and alpha, with both in $\mathcal F_2$; the ray hits
$[RLR]$ but misses the parent-right cylinder $[RR]$. Citation 4.2
keeps their codes distinct in both tasks. Placing these local sources
in a common actual branch context preserves the corresponding
prefixed initial distinctions whenever the resulting sources satisfy
the height bound: the path to the hole is the same reached branch path
in both. This is the context mechanism of [DEV, (AAR.48)–(AAR.49)].

**Mathematical citation 7.2 (a sparse initial vector).** The example
following [DEV, Proposition 11.7] uses $D\ge2$, $P=\{RL\}$ and
$t=\langle\alpha,\alpha\rangle$,
$t'=\langle\alpha,\beta\rangle$. Both initial selected replies are
absent; at count one they are absent and beta. It is the missing
$\varepsilon$ prefix in $S=\{L\}$. Theorem 5.2 supplies witnesses
for every such failure, beyond this one example. For this pair its
uniform witness rule also separates at count two, by beta versus
branch; a separating count need not be the earliest one.

**Mathematical citation 7.3 (same optimal code, different hidden
structure).** Reuse [DEV, Counterexample 11.9]'s sources

$$
\begin{aligned}
X&=\langle\alpha,\alpha\rangle,&Y&=\langle\beta,\alpha\rangle,\\
t&=\langle\alpha,\langle X,X\rangle\rangle,&
t'&=\langle\alpha,\langle Y,X\rangle\rangle.
\end{aligned}
\tag{FM.29}
$$

Both are in $\mathcal F_2$. For $P=\{RL,RR\}$ every selected reply
is branch at every count. Adding $R$ gives the same fact for
$P=A_2$. Citation 4.3 therefore gives equal optimal codes for these
sources in both tasks. The initial full-menu vector is sufficient
for its future replies by Theorem 5.2, despite this equality of codes
on different sources.

A complete row at a prefix-free cut retains the literal exterior,
addressed reached holes, concrete blockers and every equality and
disequality between hidden subtrees [DEV, Definition 1.2]. The
published counterexample proves that the rows at $\{RL,RR\}$ have
the same exterior and different hidden equality partitions at every
common count: their hidden pairs are
$(\rho^k X,\rho^k X)$ and $(\rho^k Y,\rho^k X)$, respectively.
The latter pair stays unequal, as the supplier's right-clock argument
shows. The same sufficient ray table is initially $(5,6)$ in both
sources, for $Q=\{RLR^\infty,RRR^\infty\}$; it remains sufficient
when $R$ is added. Thus neither sufficient ray memory nor the minimal
reply code determines the complete row or the full source. This
consequence uses the existing counterexample and classification,
without a second hidden-equality proof.

**Proposition 7.4 (the count cannot be silently removed).** For every
nonempty $P\subseteq A_D$, no passive deterministic decoder receiving
only initial source-dependent state and public $D,P$ recovers all
future $P$-vectors without a count or other new source-bearing input,
even if it retains the whole initial tree.

Proof, retaining [PRIOR, Proposition 9.4]'s menu-specific witness.
Use the one initial source $t_0=\langle\alpha,\alpha\rangle$ and any
$q\in S$. Put $b=s(q)+2$. The two authentic continuations with
counts $b-1$ and $b$ give beta and branch at $Rq$, by Citation 3.1.
The entire passive input is identical because the original source is
the same and neither count nor another new distinction is supplied.
A deterministic function cannot output both required vectors.
The empty menu is excluded because it always returns the empty vector.
$\square$

Saturation allows the supplied count to be replaced by
$\min(k,B(S))$ for value prediction [DEV, Theorem 12.9]. It does not
reveal when that threshold was reached. Every count at least $B(S)$
gives the same all-branch vector. By contrast an exact count, or an
exact rebased nonempty ray table, has unboundedly many values; even
for one fixed source the tables at $0\le k\le K$ require $K+1$
different lossless names [DEV, Proposition 11.10]. These are distinct
storage and recovery objectives.

## 8. Credited conditional capture and its origin

**Mathematical citation 8.1 (paid guarded acquisition).** Under the
availability of a stationary initial $\mathcal F_D$ source,
[DEV, Theorem 12.9] supplies a native encoder realization. Read $L$
as alpha, traverse the right subtree with complete literal operands,
and reread $L$ as alpha. Reject an invalid guard, unexpected absence
or a branch at absolute depth $D+1$ in the right subtree. Successful equal-alpha
guards validate one actual initial version at the final guard Read.
Compute (FM.17) from the acquired tree, export its fixed-width code in
a fixed public region, and clear or retract all other accessible
source dependence. The published successful bounds are

$$
T\le2^{D+1}+1,\qquad A\le D\,2^{D+1}+3,\qquad
Q_{\mathrm{operand}}\le D+1.
\tag{FM.30}
$$

The full-tree traversal variant of [PRIOR, Proposition 10.1] is the
same guarded acquisition with an additional body visit to the root
and to $L$. For one successful body visiting each present node of $t$
once, its exact account is

$$
T=|\operatorname{Pos}(t)|+2,\qquad
A=\sum_{p\in\operatorname{Pos}(t)}|p|+2,\qquad
Q_{\mathrm{operand}}=\operatorname{height}(t)\le D+1.
\tag{FM.31}
$$

The two extra submissions in (FM.31) are the length-one guards; the
body includes all nodes, including the length-zero root. Since the
source has height at least one, the guards do not raise its operand
maximum. This bookkeeping preserves that variant without repeating
the published capture proof.

All unsuccessful attempts, operand construction, temporary trees,
traversal data, code computation and cleanup are separately paid.
The host must expose no surviving source-bearing transcript, reply
latch, output, pointer, capacity or allocation distinction outside the
code. Inaccessible remnants still cost physical storage. Empty $P$
needs no acquisition for its constant output. A sufficient acquired
ray table can alternatively be compressed by [DEV, Theorems 12.4
and 12.6], paying Proposition 11.8's acquisition and codebook costs.

The historical origin is the final successful guard Read, not Return
or the end of cleanup. A supplied later count must include every update
from that capture, including updates during encoding or cleanup.
This procedure has no unprotected liveness guarantee once the writer
has changed the initial alpha at $L$; alpha does not return there.
It is a conditional capture construction, not a way to assume an
initial snapshot for free.

**Mathematical citation 8.2 (separate unknown-lag acquisition).**
[DEV, Proposition 11.8] separately uses that genuinely acquired alpha
at $L$ to search $L,LR,LR^2,\ldots$ until a leaf of label bit $f$
is read at $LR^j$. At that actual final Read $w$ the acquired count
is $k_w=2j+f$. The service is safe and terminates under finite
interference and observer progress, with exactly $j+1$ queries,
$(j+1)(j+2)/2$ literal letters and maximum operand $j+1$ on that run.
On a quiescent call $j=\lfloor k/2\rfloor$. These costs and the
capture-origin relation are additional to passive decoding. Computing
the selected values of $U_w$ then creates no target Read events at $w$.

## 9. Operation boundaries and remaining programme

**Mathematical citation 9.1 (the initial family is not an update carrier).**
As stated in [DEV, Mathematical citation 12.10], for every
$t=\langle\alpha,v\rangle\in\mathcal F_D$,

$$
\rho t=\langle\beta,\rho v\rangle\notin\mathcal F_D.
\tag{FM.32}
$$

The static prediction target indexes genuine continuations by $(p,k)$;
it requires no endomap on $\mathcal F_D$. [DEV] separately identifies
the finite, shift-closed carrier of suffixes of attained response
trajectories. That mathematical carrier is not an assertion that the
initial family is update-invariant or that a concrete observer has
arbitrary free operations on it.

Normalization, ranking, unranking, representative construction,
initial-vector reconstruction and supplied-count decoding have the
stated finite procedures. Their existence does not establish arbitrary
observer-operation closure, an in-family source update, unknown-lag
service at no extra price, unrestricted menu expansion, rerooting or
rebasing to a new capture. Reference and origin changes require their
own retained common-history relation and operation proofs.

The output is only the literal-value vector at the promised version.
A later actual Read may occur after further updates. A common-version
body of actual observations needs its own acquisition, validation and
paid retries. The code and clock agreement authenticate neither the
same-register premise, an origin before the first capture nor the
placement of unobserved events. Hidden equality and full-source recovery
remain different targets, as Citation 7.3 demonstrates.

**Open problem 9.2 (costs beyond the initial payload).** Determine
exact costs for forming and using the minimal code when query count,
total literal letters, maximum operand length, public installation,
communication, local bit/cell work, transient workspace and cleanup
are jointly charged. The attained state and fixed-width minima do not
supply those optima. Citation 8.1 is a conditional finite acquisition,
not a joint or interference-optimal procedure.

**Open problem 9.3 (broader interfaces).** Determine the corresponding
frontiers for all-source families, unknown future menus, source-dependent
ray selection with its selection information charged, complete-row
acquisition, hidden equality and full-source recovery. For changes of
reference or capture, specify the common-history relation and prove
each supported operation. The finite supplied-count results and the
prefix criterion do not settle the broader recovery programme for
spatial, temporal, boundary and memory descriptions. These are the
remaining boundaries of [DEV, Open problems 9.4 and 11.12, and §12.10].

## 10. Exact attribution and statement correspondence

**Mathematical citation 10.1 (source identities).** The two source
snapshots fixing the citations in this volume are:

| Citation | Mathematical source and exact snapshot |
| --- | --- |
| [DEV] | *Adaptive acquired references and the retention frontier*, revision `142f723c`, including §§1–12; SHA-256 `3d1a16530adf59065ec64c5d26791ea5cdb0cf20fb74355365d0adc670d59bdd`. |
| [PRIOR] | *Native finite-menu minimal memory*, the source with §§1–12 and Theorem 7.2; SHA-256 `f81c2985462d3984fe5e97244293b6ed2e0fdf129da5a8d5b0a63d6742bbf75c`. |

A cited published premise carries its exact hypotheses from the stated
native interface. References within [DEV] remain its own supplier
attributions; they do not add unacquired data or operations here.
The complete overlap and retained-result correspondence is:

| Mathematical conclusion | Prior statement | Published supplier or retained proof here |
| --- | --- | --- |
| Native family, four replies, nested/empty menu and complete state | [PRIOR, §§1–2] | [DEV, Definitions 1.1–1.4, 11.1 and 12.1]; §2 fixes the same parameters and relative reduction. |
| Atomic presence asymmetry, blockers and full response phases | [PRIOR, Lemma 3.2 and Theorem 3.4] | [DEV, Definition 12.2 and Theorem 12.3]; Citations 3.1–3.3 include the explicit signature correspondence. |
| Exact saturation and legal finite separation | [PRIOR, Corollary 3.5] | [DEV, Theorem 12.3]; $B(S)=H_P$ in (FM.12). |
| All constructor collisions, including the joint strict-left overlap | [PRIOR, §4] | [DEV, Theorem 12.6]; Citation 4.2 states every case and both equivalences. |
| Terminating pruned form, exact recurrence and bounded common realization | [PRIOR, §5] | [DEV, Definition 12.5 and Theorem 12.6]; Citation 4.3 uses its code order and actual representatives. |
| Rank/unrank, effective decoder, arbitrary-state and bit minima | [PRIOR, §6] | [DEV, Definition 12.5 and Theorem 12.6]; Citations 4.3–4.4 retain the complete-state conditions. |
| Initial-vector iff relative-prefix-closure criterion | [PRIOR, Theorem 7.2] | Full independent proof in Theorem 5.2, including every missing proper prefix, effective sufficiency and actual common-count sources; not stated in [DEV]. |
| Full-menu recurrence and the $D=1$ cases | [PRIOR, Corollary 8.1] | Specialization of [DEV, Theorems 12.6–12.7] in Corollary 6.1; its initial-vector assertion also uses Theorem 5.2. |
| Symbolic binary-width bounds | [PRIOR, Proposition 8.2] | Full proof in Proposition 6.2 from the credited recurrence. |
| Fixed public ray count and its distinct resource meaning | [PRIOR, Citation 8.3] | [DEV, Theorem 11.4, Corollary 11.6 and Theorem 12.8]; Citation 6.3. |
| Sampling failures, sparse initial vector, hidden equality and full source | [PRIOR, Propositions 9.1–9.3] | [DEV, Example 11.5, §11.7, Counterexample 11.9 and Theorem 12.6]; Citations 7.1–7.3. |
| Count omission for every nonempty menu | [PRIOR, Proposition 9.4] | Full common-source proof in Proposition 7.4, consistent with [DEV, §§11.8–11.10 and 12.9]. |
| Guarded capture, full-tree query account and historical origin | [PRIOR, §10] | [DEV, Proposition 11.8 and Theorem 12.9]; §8 gives the precise full-tree variant and separate unknown-lag service. |
| Non-invariance, operation limits and unresolved resource optima | [PRIOR, §11] | [DEV, §12.10 and Open problems 9.4 and 11.12]; §9 preserves these limits. |

The substantive independent proof retained here is the prefix criterion
with its native missing-prefix witnesses. The bit inequalities and
count-omission witness are useful proved consequences. The spatial
statistic, constructor analysis, normal-form count, bounded realization,
minimal code, horizon and capture are published reuse. The criterion
adds a precise test for one proposed retained representation; it does
not supply new generic quotient mathematics or identify all recovery
interfaces with one another.

## 追加锚（本行以下为增补区）

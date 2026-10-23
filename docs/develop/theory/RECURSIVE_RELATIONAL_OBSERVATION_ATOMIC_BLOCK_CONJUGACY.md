# Canonical atomic blocks, acquired relations and original physical observations

## 1. The source, acquisition and observation contracts

**Definition 1.1 (native trees and literal addresses).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{ABC.1.1}
$$

The domain consists of all nonempty finite ordered free trees. There is
no common bound on size or depth and no supplied skeleton, orbit or template.
Let $\mathcal P=\{L,R\}^{*}$, with root $\varepsilon$. The reached positions
of $u$ form $\operatorname{Pos}(u)$; the whole subtree $u|_p$ exists only
for $p\in\operatorname{Pos}(u)$. The literal reply $r_u(p)$ is one of
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$. Every finite physical word
is a legal read request, whether or not it is reached.

For a finite prefix-free set $A\subseteq\mathcal P$, use the complete
original row $R_A(u)=(C_A(u),\pi_A(u))$ of [SLH, Definition 59.1][SLH].
The holes occur precisely at $I_A(u)=A\cap\operatorname{Pos}(u)$, in
lexicographic address order; $C_A(u)$ retains every outside constructor
and concrete leaf. The complete partition $\pi_A(u)$ equates two holes
exactly when their whole subtrees are equal. An absent original cut gives
no hole. In particular $R_\varnothing(u)$ contains all of $u$, whereas
$R_{\{\varepsilon\}}(u)$ is the constant one-hole row.

**Assumption 1.2 (the entire acquired input).** Use [ARH, Assumption
1.3][ARH] with arbitrary finite data $P,Q,R,H_0,H_{\rm rel}$ and authentic
entry epoch $N$. In particular $R$ is the actually acquired full $P$ row,
$H_0$ is the finite literal history, and a signed record
$e=(a,s,b,t,\bowtie)$, $\bowtie\in\{=,\ne\}$, means

$$
\operatorname{Rel}_e(u)\ \Longleftrightarrow\
 s\in\operatorname{Pos}(\rho^a u)\ \land\
 t\in\operatorname{Pos}(\rho^b u)\ \land\
 (\rho^a u)|_s\ \bowtie\ (\rho^b u)|_t.
\tag{ABC.1.2}
$$

Both guards are required for either sign. All records constrain the same
original source. The complete accessible initial state has exactly the
nonempty source fiber

$$
D=\{u\in\mathcal T:R_P(u)=R,\quad
 r_{\rho^a u}(s)=c\ ((a,s,c)\in H_0),\quad
 \operatorname{Rel}_e(u)\ (e\in H_{\rm rel})\}.
\tag{ABC.1.3}
$$

Every old repeated class, every cross-class and off-task disequality,
every old existence guard and every additional record is imposed jointly.
The register has actually reached $\rho^N u$, where $N$ is at least every
acquired epoch. Acquisition was paid before the cut and may have finite
sourcewise cost without a uniform bound. The full accessible state,
including source-bearing caches, addresses, counts, lengths, control,
timing, references, permissions and archives, is common on precisely $D$
and recovers the retained input. Further accessible distinctions would
change (ABC.1.3).

The target is the entire original $R_Q(u)$. A permitted service is a
common deterministic effective controller, correct and terminating for
every $u\in D$. It obtains new source information only from actual
$\mathsf{Read}(p)$ replies; its other source actions are same-register
forward $\mathsf{ApplyRho}$ and absorbing $\mathsf{Halt}$. There is no
reset, reroot, clone, source identity, unknown-subtree equality or hidden
source port. The cost coordinates are every new raw read call $q$,
actual post-entry update count $a$, and
$\ell=\sum_{\text{actual reads }p}|p|$. Local computation, address generation,
installation, working storage, authentication, retention and physical time
are separate resources. These are the contracts of ARH and [JRF,
Definitions 1.2–1.3][JRF], with $a$ denoting JRF's update coordinate $d$.

**Definition 1.3 (atomic supply and the scope of the correspondence).** Put
$T_j=\rho^j\alpha$ for $j\in\mathbb N$. The supplied atomic identities are

$$
T_0=\alpha,\quad T_1=\beta,\quad
T_{j+2}=\langle T_{j+1},T_j\rangle,\quad
\rho^mT_j=T_{j+m}.
\tag{ABC.1.4}
$$

Their index is injective. These facts, the guarded atomic subtree formula,
and native injectivity of $\rho$ are used from [ARH, Definition 4.1][ARH]
and [TRANSPORT, §§22–24][TRANSPORT]. The source identification in
[SourceTransportCentralizer][CENTRALIZER] is
$\alpha=\mathtt{of\ true}$, $\beta=\mathtt{of\ false}$, ordered pairing
$=\mathtt{FreeMagma.mul}$ and $\rho=\mathtt{substitution}$; its
$\mathtt{source\_transport\_centralizer}$ already classifies the atomic
stability equation and excludes a positive globally surjective iterate.

An arbitrary injective source encoding is also already available:
[SourceTreeEncoding][ENCODING], $\mathtt{source\_code\_equiv}$, concerns
finite trees with natural leaves and their tagged hereditary-finite codes.
The correspondence below additionally identifies the native constructor,
forward action, original-address navigation, whole-row target and acquired
joint fibers. Its coordinates describe a possible source mathematically;
they are not added to the accessible state in Assumption 1.2.

## 2. A canonical representation of every finite source

**Definition 2.1 (normal atomic-block trees).** Let $\mathcal K$ be the
ordinary finite term algebra with primitive terms $[j]$, $j\in\mathbb N$,
and one ordered binary constructor $F$. Define $\mathcal N\subseteq\mathcal K$
recursively by

$$
[j]\in\mathcal N,\qquad
F(X,Y)\in\mathcal N\ \Longleftrightarrow\
 X,Y\in\mathcal N\ \land\
 \neg\exists j\ge0\ (X=[j+1]\land Y=[j]).
\tag{ABC.2.1}
$$

Thus the forbidden pattern is a pair of primitive children whose left
rank is one more than the right rank. The condition applies at every
constructor occurrence, not just the root. On normal arguments define
the native pairing operation

$$
J(X,Y)=
\begin{cases}
[j+2],&X=[j+1],\ Y=[j]\text{ for some }j\ge0,\\
F(X,Y),&\text{otherwise}.
\end{cases}
\tag{ABC.2.2}
$$

Define expansion $E:\mathcal K\to\mathcal T$ and canonical coding
$B:\mathcal T\to\mathcal N$ by

$$
\begin{aligned}
E([j])&=T_j,& E(F(X,Y))&=\langle E(X),E(Y)\rangle,\\
B(\alpha)&=[0],&B(\beta)&=[1],&
B(\langle u,v\rangle)&=J(B(u),B(v)).
\end{aligned}
\tag{ABC.2.3}
$$

The two different constructors $F$ and $J$ will remain distinguished.
The former belongs to the ambient free algebra; the latter represents
native pairing in canonical coordinates.

**Theorem 2.2 (effective mutual recovery and maximal atomic blocks).**
$B$ and $E|_{\mathcal N}$ are mutually inverse effective maps on the
entire indicated domains. For every $u\in\mathcal T$ and $X,Y\in\mathcal N$,

$$
E(B(u))=u,\qquad B(E(X))=X,\qquad
E(J(X,Y))=\langle E(X),E(Y)\rangle.
\tag{ABC.2.4}
$$

In $B(u)$ the primitive occurrences correspond exactly to the maximal
atomic subtrees of $u$: an atomic subtree has the form $T_j$, and maximal
means that no strictly containing subtree of $u$ is atomic. Every
non-atomic constructor and the order of its children is retained.

Proof. $J$ maps normal arguments to a normal result: its first case is
primitive, and its second case has normal children and no forbidden root
pattern. Its expansion identity is (ABC.1.4) in the first case and the
definition of $E$ in the second. Structural induction on $u$ now proves
$E(B(u))=u$.

Induction on $j$, using (ABC.1.4) and (ABC.2.2), gives $B(T_j)=[j]$.
For $X=[j]$ this proves $B(E(X))=X$. For a normal $F(X,Y)$, induction
recovers its two children, and (ABC.2.1) excludes precisely the collapse
case of $J$. Thus $B(E(F(X,Y)))=F(X,Y)$. These are both inverse identities;
in particular no two normal codes expand to the same source.

Consequently $u$ is atomic if and only if $B(u)$ is primitive. If $u$
is atomic its whole root is the unique maximal atomic occurrence. If
$u=\langle v,w\rangle$ is non-atomic, its code has a constructor at the
root and its maximal atomic occurrences are exactly those of $v$ and $w$,
with the corresponding physical prefixes. Induction on $u$ proves the
occurrence assertion, including arbitrary nested and repeated subtrees.

All definitions perform finite recursion on a supplied finite tree or
code; producing $T_j$ uses finite recursion on the supplied integer $j$.
The algorithms therefore terminate on each such input. No bound on the
unknown input, no promised code shape, and no bound on expansion cost is
used. $\square$

**Theorem 2.3 (uniform forward translation and its exact image).** For
$m\in\mathbb N$, let $\tau_m$ add $m$ to every primitive rank of a code
and preserve $F$. Then $\tau_m$ maps $\mathcal N$ into $\mathcal N$,
$\tau_0$ is the identity, $\tau_{m+n}=\tau_m\tau_n$, and

$$
\begin{aligned}
\tau_m J(X,Y)&=J(\tau_m X,\tau_m Y),\\
E(\tau_m X)&=\rho^m E(X),\\
B(\rho^m u)&=\tau_m B(u).
\end{aligned}
\tag{ABC.2.5}
$$

The image $\tau_m[\mathcal N]$ consists exactly of normal codes all of
whose primitive ranks are at least $m$. Subtracting $m$ from those ranks
is its unique inverse on that image. If $m>0$, $\tau_m$ is not surjective
on $\mathcal N$.

Proof. Translation preserves which terms are primitive and preserves
both truth and falsity of the exceptional relation $i=j+1$ between two
primitive siblings. It therefore preserves (ABC.2.1), and direct use of
the two cases of $J$ proves the first identity. The monoid laws follow
from addition at each leaf. Structural induction on $X$, using
$\rho^mT_j=T_{j+m}$ and preservation of native pairing, proves the second
identity. Theorem 2.2 then proves the third.

Every translated rank is at least $m$. Conversely, if all ranks of a
normal code are at least $m$, subtracting $m$ preserves the exceptional
sibling relation in both directions, so produces a normal code. This is
a two-sided inverse on the specified image. The primitive code $[0]$
is outside that image when $m>0$. Thus the conjugacy is for the forward
$\mathbb N$-monoid action, not a group action or a source reset. $\square$

**Corollary 2.4 (one advancing coordinate and a stationary structure).**
For a normal code let $\mu(X)$ be its least primitive rank, and set
$Z(X)=\tau_{-\mu(X)}X$, where the subtraction is defined on the image
specified in Theorem 2.3. Let

$$
\mathcal Z=\{X\in\mathcal N:\mu(X)=0\}.
$$

Every original source corresponds uniquely and effectively to a pair
$(Z,m)\in\mathcal Z\times\mathbb N$, with

$$
u=E(\tau_m Z),\qquad
\rho^n u=E(\tau_{m+n}Z).
\tag{ABC.2.6}
$$

Proof. A finite nonempty code has a finite nonempty rank set and hence a
least rank. Theorem 2.3 justifies subtraction, and the result has minimum
zero. Conversely $\tau_m Z$ has minimum $m$ and recovers the same $Z$.
These inverse operations and Theorem 2.2 prove uniqueness and effectivity.
Translation changes that minimum by $n$ and leaves all rank differences
and the constructor structure unchanged. $\square$

## 3. Original physical addresses inside compressed atomic blocks

**Definition 3.1 (partial native children and exact navigation).** Adjoin
an absence symbol $\bot\notin\mathcal N$. Define $d_L,d_R$ by

$$
\begin{array}{c|cc}
X&d_L(X)&d_R(X)\\\hline
\bot&\bot&\bot\\
[0]\text{ or }[1]&\bot&\bot\\
[j]\ (j\ge2)&[j-1]&[j-2]\\
F(Y,Z)&Y&Z.
\end{array}
\tag{ABC.3.1}
$$

Set $\nu_\varepsilon(X)=X$ and $\nu_{pe}(X)=d_e(\nu_p(X))$ for
$e\in\{L,R\}$. Define the root-reply map $\lambda$ by

$$
\lambda(\bot)=\mathsf{absent},\quad
\lambda([0])=\alpha,\quad\lambda([1])=\beta,\quad
\lambda([j])=\mathsf{branch}\ (j\ge2),\quad
\lambda(F(Y,Z))=\mathsf{branch}.
\tag{ABC.3.2}
$$

Every successful child in (ABC.3.1) is normal. In particular navigation
inside $[j]$ uses its native expanded children, not children in the
ambient code syntax.

**Theorem 3.2 (guarded whole-subtree and literal correspondence).** For
every $u\in\mathcal T$, $n\ge0$ and finite physical word $p$,

$$
\begin{aligned}
p\in\operatorname{Pos}(\rho^n u)
 &\Longleftrightarrow\nu_p(\tau_nB(u))\ne\bot,\\
B((\rho^n u)|_p)&=\nu_p(\tau_nB(u))\quad\text{when reached},\\
r_{\rho^n u}(p)&=\lambda(\nu_p(\tau_nB(u))).
\end{aligned}
\tag{ABC.3.3}
$$

Thus a signed record is exactly the following predicate on $X=B(u)$:

$$
\nu_s(\tau_aX)\ne\bot\ \land\
\nu_t(\tau_bX)\ne\bot\ \land\
\nu_s(\tau_aX)\ \bowtie\ \nu_t(\tau_bX).
\tag{ABC.3.4}
$$

Proof. At a normal constructor, $E$ is native pairing. At $[j]$, the
expanded source is a leaf exactly for $j=0,1$, and for $j\ge2$ its
children are $T_{j-1},T_{j-2}$ by the supplied recurrence. Therefore
(ABC.3.1) gives exactly the reached native children and their canonical
codes. Induction on the length of $p$, propagating $\bot$ after the first
failed edge, proves the first two statements at epoch zero for every
normal code. Equation (ABC.3.2) gives its literal root reply. Apply these
facts to $\tau_nB(u)=B(\rho^n u)$ to obtain (ABC.3.3). Under the two guards,
Theorem 2.2 makes code equality equivalent to whole native subtree
equality; its negation gives the disequality case. $\square$

**Proposition 3.3 (native constructor, hidden positions and absence).**
The following boundary statements hold on the native source class.

1. $J([1],[0])=[2]$, but $F([1],[0])\ne[2]$ in $\mathcal K$.
   Both ambient terms expand to $T_2$; only $[2]$ is normal.
2. The code $B(T_2)=[2]$ has only its root as an ambient syntactic
   position, while $T_2$ has positions $\varepsilon,L,R$.
3. A nonnegative atomic residual index alone is not an existence test:
   $2-w(LL)=0$, but $LL\notin\operatorname{Pos}(T_2)$, where
   $w(p)=\#_L(p)+2\#_R(p)$.
4. For the original source $\beta$, $L$ is absent originally and reached
   after one update. The signed comparison $(0,L,1,R,\ne)$ is false.

Proof. The first two assertions follow from the recurrence
$T_2=\langle\beta,\alpha\rangle$ and (ABC.2.1)–(ABC.2.3). For the third,
the original $L$ child is the leaf $\beta$, which blocks $LL$.
Equivalently the supplied [ARH, (4.3)][ARH] requires, for nonempty $p$,
$j\ge w(p^-)+2$ before using $T_{j-w(p)}$. At $j=2,p=LL$ this guard
fails. For the fourth, $\rho\beta=\langle\beta,\alpha\rangle$, so the
second endpoint exists and the first does not. Assumption 1.2 requires
both and therefore rejects either sign. These facts preclude replacing
physical cuts by code positions or interpreting an absent endpoint as a
negative equality certificate. $\square$

## 4. The complete original row without a bound on its exterior

**Definition 4.1 (finite-cut masking in native coordinates).** Fix a finite
prefix-free $Q$. Define $M_Q(X)\in\mathcal N$ for $X\in\mathcal N$ by
recursion on the finite cut trie. If $Q=\varnothing$, put $M_Q(X)=X$.
If $\varepsilon\in Q$, put $M_Q(X)=[0]$. In the remaining case, if
$X=[0]$ or $X=[1]$, put $M_Q(X)=X$. Otherwise $X$ is a native branch;
put $Q_e=\{p:ep\in Q\}$ and

$$
M_Q(X)=J(M_{Q_L}(d_LX),M_{Q_R}(d_RX)).
\tag{ABC.4.1}
$$

The recursion stops when a trie branch contains no cut, retaining its
entire unexamined code. Put $I_Q^\#(X)=\{q\in Q:\nu_q(X)\ne\bot\}$.
The coded row data consist of this reached set, $M_Q(X)$, and the complete
partition of that set defined by

$$
q\sim_X r\quad\Longleftrightarrow\quad\nu_q(X)=\nu_r(X).
\tag{ABC.4.2}
$$

The code $M_Q(X)$ represents the concrete tree obtained by filling every
reached hole with $\alpha$; it is not itself the output context.

**Theorem 4.2 (whole-row recovery and exact row equality).** Let $X=B(u)$.
Expansion of $M_Q(X)$ followed by replacing the subtrees at $I_Q^\#(X)$
by their numbered holes yields exactly $C_Q(u)$. Together with (ABC.4.2)
this recovers the whole original $R_Q(u)$. For $X,Y\in\mathcal N$, put $I=I_Q^\#(X)$. Then

$$
\begin{aligned}
\operatorname{Same}_Q(X,Y)\ \Longleftrightarrow\quad&
 I_Q^\#(Y)=I,\\
&M_Q(X)=M_Q(Y),\\
&\forall q,r\in I,\quad
 [\nu_q(X)=\nu_r(X)]\Longleftrightarrow
 [\nu_q(Y)=\nu_r(Y)]
\end{aligned}
\tag{ABC.4.3}
$$

is equivalent to $R_Q(E(X))=R_Q(E(Y))$. This includes empty cuts, a root
cut, all-absent cuts, repeated hole values and arbitrarily large concrete
exteriors.

Proof. Induct on the cut trie. An empty trie changes nothing. A root cut
replaces the reached root by $\alpha$. If the current source is a leaf
and all pending cuts are nonempty, they are absent and it remains the
same concrete leaf. Otherwise (ABC.3.1) gives the actual two children;
the induction hypotheses perform the appropriate masking in each, and
(ABC.2.4) reassembles them. Thus

$$
E(M_Q(B(u)))=C_Q(u)[\alpha,\ldots,\alpha].
\tag{ABC.4.4}
$$

Masking retains the reached root of each replaced subtree. Prefix-freeness
ensures that replacements neither hide nor create another requested cut.
An originally absent cut remains blocked by its concrete strict-prefix
leaf outside all holes. The reached set therefore still specifies the
same hole addresses in the masked tree. Replacing precisely those
subtrees by numbered holes recovers $C_Q(u)$, even if the canonical mask
has collapsed some surrounding atomic block.

For two contexts whose holes have the same fixed address set $I$, filling
all holes by $\alpha$ is injective: replacement at $I$ is an inverse on
its image. Hence equality of $M_Q(X),M_Q(Y)$ is, by Theorem 2.2 and
(ABC.4.4), exactly equality of their concrete contexts once $I$ agrees.
Theorem 3.2 makes (ABC.4.2) exactly their complete hole partition. These
three conditions prove both implications of (ABC.4.3).

When $Q=\varnothing$, the reached set is empty and $M_Q(X)=X$, so row
equality is full source equality. When $Q=\{\varepsilon\}$, masking is
$[0]$ and the singleton partition is fixed. With all cuts absent the mask
again expands to the entire source. The proof does not discard or bound
any outside subtree. $\square$

## 5. Exact transport of every admitted acquired-history fiber

**Definition 5.1 (evaluation of residual expressions).** For a finite
ordinary source term $A$ over variables $V$, define $A^\#$ on valuations
$\mathbf X:V\to\mathcal N$ by interpreting $\alpha,\beta$ as $[0],[1]$,
native pairing as $J$, and each variable by its assigned code. Interpret
$\rho^a(A)$ by $\tau_a(A^\#(\mathbf X))$. Ground trees are interpreted
by $B$ of that tree. In particular a syntactic native pair is never
translated as an unconditional ambient $F$.

Use exactly the finite guarded cells of [ARH, Definition 3.1 and
Proposition 3.2][ARH]. A cell $\eta$ has source term
$W_\eta=C[(t_{[i]})_i]$, shared frontier variables $V_\eta$, all old
class constraints $\Delta_\eta=\{t_b\ne t_c:b<c\}$, literal conditions,
and all signed whole-subtree residual relations with their endpoint
guards. Define $\Omega_\eta^\#$ to contain all normal valuations satisfying
every one of these conditions after the above translation. Concrete
false endpoint guards reject a valuation for either sign. Empty cells
are permitted; the finite cell construction does not decide emptiness.

**Theorem 5.2 (two full fiber inclusions and a unique original realization).**
There are effective mutually inverse correspondences

$$
\coprod_\eta\Omega_\eta^\#\ \longleftrightarrow\ D
\ \longleftrightarrow\ B[D],
\qquad
(\eta,\mathbf X)\longmapsto E(W_\eta^\#(\mathbf X))
\longmapsto W_\eta^\#(\mathbf X).
\tag{ABC.5.1}
$$

No independently selected component, representative source or marginal
solution replaces any fiber in (ABC.5.1). The complete original target on
each cell is the row of Theorem 4.2 at $W_\eta^\#(\mathbf X)$.

Proof. First, induction on $A$ using Theorem 2.2 gives the commuting
evaluation identity

$$
A^\#(\mathbf X)=B(A[E\mathbf X]),
\qquad
\tau_a A^\#(\mathbf X)=B(\rho^a(A[E\mathbf X])).
\tag{ABC.5.2}
$$

Thus every ordinary or morphic equality, and every disequality between
reached endpoints, has exactly the same truth value before and after
coding. Theorem 3.2 gives the same fact for literals and their guards.
For the concrete leaf-sector endpoints in ARH's cells, its guard and
whole-tree supplier are unchanged and (ABC.5.2) codes their resulting
$T_j$ as $[j]$.

Given $u\in D$, ARH Proposition 3.2 supplies its unique cell and its
unique valuation $v$ of the original frontier subtrees. Assign
$\mathbf X(x)=B(v(x))$ at every frontier variable. Equation (ABC.5.2)
preserves all the cell constraints, hence
$\mathbf X\in\Omega_\eta^\#$ and $W_\eta^\#(\mathbf X)=B(u)$.
This proves that every admitted source is represented.

Conversely, let $\mathbf X\in\Omega_\eta^\#$ and set $v=E\mathbf X$.
Every conjunct is true for that one valuation by (ABC.5.2) and the guarded
navigation correspondence. In particular all $t_b[v]\ne t_c[v]$ hold,
including pairs involving classes unused by the new cuts; every repeated
occurrence uses the same variable assignment. ARH Proposition 3.2 therefore
gives $W_\eta[v]\in D$. It enforces the whole old context and its absent
cut guards as well as every literal and additional relation. Theorem 2.2
gives $B(W_\eta[v])=W_\eta^\#(\mathbf X)$. This proves the reverse
inclusion without a product relaxation.

ARH's inverse reads a representative occurrence of each old class and
its pattern frontier from the concrete original source. It is unique;
Theorem 2.2 then recovers precisely $\mathbf X$. Distinct cells remain
disjoint even though some expressions can collapse to atomic codes.
These finite constructions prove effectivity of both directions when
the concrete argument is supplied. They do not give the actual observer
that argument. The target assertion follows from Theorem 4.2 and ARH's
full target correspondence (ARH.3.4), including residual variables in
the outside context. $\square$

**Proposition 5.3 (semantic coordinates are not acquired data).** On the
entry with $P=\{\varepsilon\}$, its single-hole old row, empty histories
and $N=0$, the entire fiber is $\mathcal T$. No function of the common
retained input equals $B(u)$ on this fiber. For $Q=\{L\}$, no permitted
zero-read service returns the complete original row on this fiber.

Proof. The old row and complete initial state agree for $u=\alpha$ and
$v=\beta$, but $B(u)=[0]\ne[1]=B(v)$. Hence no function of those common
data gives both correct codes. The cut $L$ is absent for both sources;
the required rows are the distinct concrete trees $\alpha$ and $\beta$.
Without new replies, common deterministic control follows the same
computations and forward actions on the two sources, receives no
source-dependent input, and gives the same output at halt. This cannot
be correct for both. Providing the code or its least rank would refine
the entry fiber. A calculation on a hypothetical code is consequently
not an acquisition or a physical receipt. $\square$

**Proposition 5.4 (canonical coordinates for the supplied elimination charts).**
For an input accepted by [ARH, Definition 20.2][ARH], let
$F_\eta(Y_\eta)$ and $D_\eta$ be the reconstructed source template and
complete residual domain supplied by its Proposition 20.3. The coordinates
$y\in Y_\eta$ are surviving original subtrees at the fixed reached
addresses $a_{\eta,y}$. Interpret the normalized template by $J$ and
$\tau_a$ as in Definition 5.1, and put

$$
\begin{aligned}
\Theta_\eta^\#
 &=\{\mathbf X\in\mathcal N^{Y_\eta}:D_\eta(E\mathbf X)\},\\
\Psi_\eta(\mathbf X)&=F_\eta^\#(\mathbf X)
                     =B(F_\eta[E\mathbf X]).
\end{aligned}
\tag{ABC.5.3}
$$

Then $\Psi_\eta$ is a bijection onto the canonical codes of precisely
that chart's sources, with inverse given by
$X_y=\nu_{a_{\eta,y}}(\Psi_\eta(\mathbf X))$.
The union over the selected cover is exactly $B[D]$.

Define $X\equiv_h^\# X'$ to mean equality of
$\lambda(\nu_p(X))$ and $\lambda(\nu_p(X'))$ for every $|p|<h$;
for tuples require this coordinatewise. With
$A_\eta=\max(\{0\}\cup\{|a_{\eta,y}|:y\in Y_\eta\})$, the supplied
original-prefix directions become

$$
\begin{aligned}
\mathbf X\equiv_h^\#\mathbf X'
 &\Longrightarrow
 \Psi_\eta(\mathbf X)\equiv_h^\#\Psi_\eta(\mathbf X'),\\
\Psi_\eta(\mathbf X)\equiv_{A_\eta+h}^\#\Psi_\eta(\mathbf X')
 &\Longrightarrow \mathbf X\equiv_h^\#\mathbf X'.
\end{aligned}
\tag{ABC.5.4}
$$

The chart selector remains a bounded original-prefix observation, and
ARH's entire-row disagreement predicate has the exact interpretation

$$
\operatorname{Bad}_\eta(E\mathbf X,E\mathbf X')
\ \Longleftrightarrow\
\neg\operatorname{Same}_Q
       (\Psi_\eta(\mathbf X),\Psi_\eta(\mathbf X'))
\quad(\mathbf X,\mathbf X'\in\Theta_\eta^\#).
\tag{ABC.5.5}
$$

Proof. ARH Propositions 19.4 and 20.3 supply both whole-source inclusions,
the unique original-coordinate inverse and the finite selector. Apply
Theorem 2.2 to every coordinate and (ABC.5.2) to the reconstructed
template. This proves (ABC.5.3) and its inverse; all residual constraints
are evaluated on the same tuple. In particular eliminating a variable
does not discard an old disequality or an acquired sign involving it.
Theorem 3.2 identifies $\equiv_h^\#$ exactly with agreement of the
expanded original trees at addresses of length less than $h$. Applying
ARH Proposition 20.4 gives both lines of (ABC.5.4). These are native
prefixes, not prefixes of the compressed $F$ syntax. ARH's selector asks
only fixed original constructor questions, so its bounded-prefix and
paid-read interpretation is preserved. Finally ARH Proposition 21.3
identifies its Bad with disagreement of the entire native rows, and
Theorem 4.2 proves (ABC.5.5).

The effective criterion and finite negative witnesses on these charts
are supplied by ARH Theorem 22.1. They use automata on the surviving
*original finite-tree* coordinates $E\mathbf X$, not an assumed
recognizability of $\Theta_\eta^\#$ in the logical language of §7.
The conjugacy preserves that restricted decision and its actual consumer;
it does not extend the constructor-elimination recognizer to every
acquired input. $\square$

## 6. Paid traces in the two presentations

**Definition 6.1 (an opaque coded register).** A coded presentation of
Assumption 1.2 has hidden original parameter $X\in B[D]$ and current
register state $Y=\tau_NX$. It has exactly the same accessible controller
state and the same ports as the native presentation. The semantic effect
of an actual update is $Y\mapsto\tau_1Y$. An actual request of the literal
word $p$ returns $\lambda(\nu_p(Y))$. Halt is absorbing. The controller
cannot inspect $X,Y$, their constructor structure, primitive ranks,
$\mu$, $Z$, or the cell valuation. It has no additional operation for
$J$, $E$, $B$, navigation or code equality on the unknown register.

These are semantic descriptions of the existing ports. In a physical
realization an update is still $\mathsf{ApplyRho}$ on the same register,
and a read is still $\mathsf{Read}(p)$ at the same original root. Local
computations may use acquired finite data and hypothetical candidates,
under the same restrictions as the native controller.

**Theorem 6.2 (bidirectional actual-service and sourcewise cost correspondence).**
Every permitted native controller has a permitted opaque coded controller,
and conversely, with the same accessible initial state. On corresponding
sources $u\leftrightarrow B(u)$, they have identical sequences of actual
updates, submitted physical words, returned labels, accessible control
states, outputs and genuine halt. Source-totality and correctness for the
entire original $R_Q$ are equivalent. In particular

$$
(q_A(u),a_A(u),\ell_A(u))
 =(q_{A^\#}(B(u)),a_{A^\#}(B(u)),\ell_{A^\#}(B(u))).
\tag{ABC.6.1}
$$

Proof. Use the same effective control rules, local data representation
and initial accessible state. Relate hidden register states by
$Y=B(t)$, initially $t=\rho^N u$. If the next action is an update,
Theorem 2.3 relates the resulting states. It is one actual forward action
in each presentation. If the action is a read, the equal accessible states
choose the same finite word $p$. Theorem 3.2 proves equal replies, so the
accessible continuations agree. A local computation uses only that equal
state and has the same next control result. At halt both controllers
have the same output and neither has a source-action continuation.

Induction through any finite run proves these assertions. The same
argument in the reverse presentation applies to every coded controller
because Definition 6.1 prohibits inspection of the hidden coordinates.
It executes its existing port requests on the native register and needs
no computation of $B(u)$ or $E(X)$ at entry. There is no restriction to
finite tables or to programs with a known uniform bound: any sourcewise
finite run is covered. A terminating run corresponds to a terminating
run, and a failure to terminate cannot acquire an unmatched halt.
Theorem 4.2 identifies the required target. Theorem 5.2 covers every and
only admitted source. Thus correctness and source-totality transfer in
both directions against all allowed adaptive competitors.

The actual action sequences are identical, including repeated calls,
epochs zero and one, reads of absent addresses, updates before any read,
and halt without a read. Each read contributes one to $q$ and the length
of that same submitted word to $\ell$; each actual update contributes one
to $a$. Summing proves (ABC.6.1). No acquisition event or update is added
by the mathematical state relation. This establishes no equivalence or
saving for expansion work, storage, installation, retention, authentication
or physical elapsed time. $\square$

**Corollary 6.3 (the three optimization objects stay distinct).** Let
$c_A(u)=(q_A(u),a_A(u),\ell_A(u))$. The correspondence preserves the full
sourcewise cost function under $B$, its coordinatewise supremum vector,
and, separately, every rational nonnegative weighted value

$$
b(A)=(\sup_Dq_A,\sup_Da_A,\sup_D\ell_A),\qquad
W_\lambda(A)=\sup_{u\in D}\lambda\cdot c_A(u).
\tag{ABC.6.2}
$$

It therefore preserves their feasible upper-budget sets, Pareto minima
as sets, and weighted infima and any existing attainment. It supplies
no algorithm computing these sets or values on arbitrary acquired fibers.

Proof. Equation (ABC.6.1) and the source bijection preserve each individual
value and the sets over which the indicated suprema are taken. The two
controller directions identify the feasible objects before optimization,
so the corresponding infima and witnesses agree as well. The weighted
sum is taken on one source before its supremum. There is no step replacing
it by the sum of three separate suprema; [JRF, Example 8.3][JRF] already
gives a native strict inequality between those quantities. These are
semantic equalities even when the suprema are infinite, without a search
or termination claim. $\square$

**Proposition 6.4 (the universal operational suppliers restrict to the full
signed fiber).** The following parts of JRF retain their conclusions on
$D$ and on its opaque presentation: Lemma 2.2's all-source nonexpansive
late probes; Theorem 3.1's cap of actual epochs at $M=\max(N,5)$;
Lemma 3.2's removal of repeated or constant-root reads; and Lemma 3.4's
use of shortest physical occurrences of old classes. In particular every
permitted $A$ has an effective capped service satisfying, on each same
$u\in D$,

$$
q_{A^c}(u)=q_A(u),\quad
a_{A^c}(u)=\min(a_A(u),M-N),\quad
\ell_{A^c}(u)\le\ell_A(u).
\tag{ABC.6.3}
$$

The separate cleanup has $q\le\ell+\max(0,2-N)$ and does not increase
any coordinate. Neither transformation asserts equality of the old and
new actual receipts.

A different supplier, [SCR, Theorems 9.2 and 10.1][SCR], gives raw-count
normalization at $M_4=\max(N,4)$. For $N\ge1$, it first performs
$M_4-N$ actual updates and then reads only at $M_4$. For $N=0$, it keeps
all actual epoch-zero actions until the simulated controller first asks
for an update, then performs four actual updates and reads only at four.
A run halting before that request stays at zero. For each $u\in D$, let
$q_A^+(u)$ count the original reads after that request when $N=0$, and
all original reads when $N\ge1$. The resulting service satisfies

$$
q_{A^{\flat_4}}(u)=q_A(u),\qquad
\ell_{A^{\flat_4}}(u)
 \le\ell_A(u)+(M_4-1)q_A^+(u),
\tag{ABC.6.4}
$$

with the same full-row output and sourcewise termination. Its actual
update count is $M_4-N$ for positive entry, and either zero or four at
zero entry, according to the stated reply-dependent switch. This
raw-count statement does not replace the joint dominance in (ABC.6.3).

Proof. JRF Lemma 2.2 is quantified over every $u\in\mathcal T$, so its
same-source reply and literal-length inequalities restrict to $D$.
The proof of JRF Theorem 3.1 needs those identities, common complete
control and pointwise termination, all present in Assumption 1.2. It
keeps early actions, including epochs zero through four, unchanged; after
the cap it executes the stipulated shorter actual reads. Simulated late
updates remain local computations, not actual receipts. This is exactly
the proof of (ABC.6.3), independent of how $D$ is described.

The cleanup uses equality of repeated replies at an unchanged actual
epoch and the all-source constant-root fact after epoch two. Additional
signed predicates do not alter either identity. The shortest-occurrence
step uses only equality of all occurrences of a retained old class and
the known old context; both remain true on $D$. All constraints are kept
in the domain while those pointwise identities are applied. Theorem 6.2
transfers these actual conclusions to the opaque presentation. These
supplier applications prove sourcewise dominance; JRF's literal-only
feasibility or stopping algorithms have not been invoked.

For the separate raw normalization, SCR Theorem 9.2 supplies, for every
$n\ge1$, $M_4\ge4$ and finite $p$, a common effective physical address
$\widehat T(n,M_4,p)$ with

$$
r_{\rho^n u}(p)=r_{\rho^{M_4}u}(\widehat T(n,M_4,p)),\qquad
|\widehat T(n,M_4,p)|\le |p|+M_4-1
\quad(u\in\mathcal T).
\tag{ABC.6.5}
$$

This identity restricts to every same $u\in D$, regardless of its
retained signed relations. SCR Theorem 10.1's controller simulation uses
only that identity and the complete common state, so the source/action
hypotheses are exactly Assumption 1.2. Each simulated read causes one
actual read, including repeated or constant requests. Summing its length
bound only over positive-mode requests proves (ABC.6.4); zero-mode
addresses are unchanged. Simulated updates never become actual updates
or receipts. Every normalized controller is itself a permitted serial
controller on $D$, giving the reverse service inclusion for this
raw-count comparison. Theorem 6.2 supplies its opaque counterpart too.

SCR Theorem 9.3 makes four the sharp threshold for its universal
positive-epoch at-most-one-read property without extra source evidence,
even allowing arbitrary reply decoding. It does not impose that lower
bound on a particular acquired fiber. Its length estimate (ABC.6.5)
is additive, and the initial advancement can exceed the updates of a
comparator that halts early. Thus neither $\ell_{A^{\flat_4}}\le\ell_A$
nor joint sourcewise dominance is inferred. The nonexpansive supplier
used in (ABC.6.3) remains JRF's $n\ge m\ge5$ theorem. $\square$

## 7. The finite logical interface and its normal-domain obligation

**Definition 7.1 (the ambient term-power language).** Use the covariant
$\Sigma$-term-power of a relational presentation of Presburger arithmetic
$\mathcal C=(\mathbb N,0,1,+,\le)$, with one binary constructor
$\Sigma=\{F\}$. A function symbol of the base is replaced by its graph
when necessary. The term sort is exactly $\mathcal K$: all finite
$F$-trees with natural-number primitives. Shapes forget the primitive
values. A leafset is a subset of the leaves of one specified shape. Write
$\mathfrak A$ for the resulting four-sorted term-power structure.

The language and semantics are those of Kuncak–Rinard, *On the Theory
of Structural Subtyping*, [§§6.2–6.5, Figures 9–11, Theorem 56,
Corollary 57 and Theorem 58][KR]. They include constructor tests,
guarded selectors, term and shape equality, quantification over terms,
shapes and leafsets, and the pointwise lifting of base formulas on terms
of a common shape. Write $[\varphi]^I_s(X_1,\ldots,X_k)$ for the
leafset at which the base formula $\varphi$ holds, defined when all
$X_i$ have shape $s$. Equality to $\mathsf{true}^I_s$ means that the
base formula holds at every leaf. Partial expressions are used only with
their definedness conditions; equivalently the constructions below can
be written as guarded relational graphs.

The cited result decides this ambient language because the base
first-order theory is decidable. Ginsburg–Spanier,
[*Semigroups, Presburger Formulas, and Languages*, Theorems 1.2–1.3][GS],
supplies the Presburger decision and effective semilinear correspondence.
This does not make an arbitrary recursive predicate on unknown tree
shapes an ambient formula. The native domain remains $\mathcal N$,
which is a proper subset of the term sort.

**Theorem 7.2 (finite formulas for native operations on normal arguments).**
For each fixed numeral $m$, each fixed finite physical word $p$ and each
fixed finite cut $Q$, finite formulas in Definition 7.1 express the
graphs of $\tau_m,J$, guarded $\nu_p$, root replies, $M_Q$ and
$\operatorname{Same}_Q$, correctly whenever the input codes are normal.
They also express the translated finite residual terms and cell
conjunctions of §5 on normal valuations. No quantification over an
arbitrary address, leaf-selection operation or recursive predicate is
used by these formulas.

Proof. For a supplied $m$, the graph of translation is the well-defined
same-shape condition

$$
\mathsf{Shift}_m(X,Y)\ \Longleftrightarrow\
\mathsf{sh}(X)=\mathsf{sh}(Y)=s\ \land\
[y=x+m]^I_s(X,Y)=\mathsf{true}^I_s.
\tag{ABC.7.1}
$$

Here $s$ is existentially quantified if not already named; $m$ is a
numeral in a base formula, not an unprovided external scalar shared
through a new leaf-selection port. The semantics in Figures 10–11
make (ABC.7.1) exactly leafwise translation on any ambient term.

Let $\mathsf{Pri}(X)$ be the primitive-term test. With primitive arguments,
their common shape is the one-leaf shape, so lifting a Presburger relation
and requiring its leafset to be full gives exactly that relation between
their ranks. Define $\mathsf{Succ}(X,Y)$ in this way to mean that both
are primitive and the rank of $X$ is the rank of $Y$ plus one. Then the
graph of $J$ is

$$
\begin{aligned}
\mathsf{Join}(X,Y,Z)\ \Longleftrightarrow\ &
 [\mathsf{Succ}(X,Y)\land\mathsf{Shift}_2(Y,Z)]\\
 &\lor[\neg\mathsf{Succ}(X,Y)\land Z=F(X,Y)].
\end{aligned}
\tag{ABC.7.2}
$$

On normal inputs it is precisely (ABC.2.2). The special first case is
necessary even though $F$ itself is an available free constructor.
Primitive numerals $[j]$ are definable by the primitive test and the
lifted predicate $x=j$ at the one-leaf shape.

A left-child graph is the disjunction of $X=F(Y,Z)$ with child $Y$, and
the primitive case $x\ge2$, $y=x-1$. A right-child graph uses the same
constructor case with child $Z$ and the primitive case $x\ge2$, $z=x-2$.
Each arithmetic relation is Presburger. There is no child for primitive
zero or one. Existentially composing $|p|$ such child graphs yields
$\mathsf{Nav}_p(X,Y)$, with $\mathsf{Nav}_\varepsilon(X,Y)$ equal to
$X=Y$. Its domain formula is $\exists Y\,\mathsf{Nav}_p(X,Y)$.
Absence is the negation of that domain formula, not a distinguished tree
value that can satisfy a disequality. Root replies use the primitive
zero and one tests, or a constructor or primitive rank at least two.
Existentially compose navigation and root tests for the other three
literal replies.

For masking, unroll the finite recursion of Definition 4.1. The empty-cut
case is equality of input and output; the root-cut case sets output to
$[0]$. The leaf case uses its primitive zero/one tests. In the branch
case introduce its two native children, their two recursive masks, and
one $\mathsf{Join}$ relation. Each recursive invocation uses a strictly
smaller remaining cut depth; this is a finite formula construction from
$Q$, not recursion inside the logical language. It retains unconstrained
outside subtrees as term variables. Expand (ABC.4.3) using finitely many
domain tests, mask graphs and guarded equality comparisons at the fixed
members of $Q$. This gives a finite formula for whole-row equality even
when its concrete exterior is unbounded.

Finally unfold a finite residual expression using primitive constants,
$\mathsf{Join}$ and the finitely many fixed-numeral shift graphs.
Existential intermediate variables are uniquely determined by these
graphs on normal arguments and remain normal. Code equality is ordinary
term equality. Apply this to each conjunct of §5, keeping its original
variable sharing and both guards for signed endpoints. Theorem 5.2 proves
the meaning on normal valuations. None of these constructions asserts
that unrestricted quantification over $\mathcal K$ already means
quantification over $\mathcal N$. $\square$

**Assumption 7.3 (uniform native-domain interpretation, an open obligation).**
There is a finite formula $\mathsf{Normal}(X)$ in precisely the language
of Definition 7.1, supplied effectively with a proof that

$$
\mathfrak A\models\mathsf{Normal}(X)
 \quad\Longleftrightarrow\quad X\in\mathcal N
\quad\text{for every }X\in\mathcal K.
\tag{ABC.7.3}
$$

Its meaning must impose (ABC.2.1) at every internal occurrence of an
arbitrarily shaped finite term. A recursive traversal deciding normality
of a *given* term is not such a formula. Nor is a scheme with one clause
for every depth, a new primitive predicate declared decidable, or a
quantifier over subterms absent from the cited language. An alternative
finite interpretation may replace (ABC.7.3) only with proved full-domain
source correspondence, equality, constructor, fixed-epoch navigation
and whole-row formulas in a decidable language. No such unrestricted
interpretation is assumed in §§1–6 or proved here.

**Proposition 7.4 (why the domain obligation cannot be silently erased).**
The unrestricted ambient quantifiers in Definition 7.1, with equality
as native equality, do not give the interpretation of §2. Normality at a
fixed supplied constructor shape is, however, finitely expressible.
Neither observation settles Assumption 7.3.

Proof. The distinct ambient terms $[2]$ and $F([1],[0])$ have the same
expansion by Proposition 3.3. Ambient disequality can therefore be true
between two descriptions of the same native source. Quantifying over all
ambient terms while treating equality as native equality is not sound
for signed native constraints. Simply using the ambient constructor
would also contradict (ABC.7.2).

Now fix a finite shape $s$ and label its finitely many leaves by natural
variables $n_1,\ldots,n_k$. For each internal node whose children are both
leaves impose $n_i\ne n_j+1$ in their left-to-right order. Their finite
conjunction, together with the supplied shape, is exactly (ABC.2.1),
since these are precisely the possible forbidden occurrences. This is
a Presburger condition and can also be expressed by finitely many guarded
constructor selectors and lifted primitive comparisons. It concerns a
supplied shape, not all shapes in one formula. There are normal shapes
of arbitrarily great depth: take a complete binary shape with every
primitive label zero. Its primitive siblings have equal ranks, so no
forbidden occurrence exists. Consequently a finite enumeration of such
fixed shapes does not cover the native domain. $\square$

**Proposition 7.5 (conditional exact source formulas and fixed-prefix decision).**
Under Assumption 7.3 one can construct a finite ambient formula
$\mathsf{Adm}(X)$ whose solutions are exactly $B[D]$. For every supplied
$h\ge0$ one can then decide exactly

$$
\begin{aligned}
\forall X,Y\quad
 [\mathsf{Adm}(X)\land\mathsf{Adm}(Y)\land
       \bigwedge_{|p|\le h}\lambda(\nu_p(X))=\lambda(\nu_p(Y))]
 \Longrightarrow\operatorname{Same}_Q(X,Y).
\end{aligned}
\tag{ABC.7.4}
$$

A true decision with this supplied $h$ gives a permitted static full-row
service by the inherited ARH existence bridge. Searching $h=0,1,\ldots$
under the assumption semidecides positive bounded recovery. It does not
supply a stopping rule when every test is false.

Proof. For every cell in §5 quantify a code variable for each of its
shared frontier variables and conjoin $\mathsf{Normal}$ for each.
Conjoin the formulas of Theorem 7.2 for its complete guarded constraints
and $X=W_\eta^\#(\mathbf X)$. Take the finite disjunction over cells,
and conjoin $\mathsf{Normal}(X)$. The two directions of Theorem 5.2 give
exactly $B[D]$. No empty-cell decision or independent optimization is
needed to form the disjunction.

There are $2^{h+1}-1$ words with length at most $h$. Equality of two
literal replies is the finite disjunction over their four labels. Expand
these finitely many predicates and $\operatorname{Same}_Q$ by Theorem
7.2. With (ABC.7.3), this is a sentence of the cited language; Kuncak–Rinard
Corollary 57 decides it. Theorems 3.2, 4.2 and 5.2 make it exactly
$\operatorname{PrefDet}(D,Q,h)$ of [ARH, Definition 2.2][ARH].

For a true test use [ARH, (2.3) and its proof][ARH]: at the actual epoch
$N$, its supplied historical literal decoder acquires the indicated
original prefix with at most $2(2^{h+1}-1)$ actual new reads. Enumerate
concrete finite candidate sources until one satisfies the entire retained
input and recovered prefix. Concrete membership is decidable and the
actual source guarantees a witness. The prefix criterion makes the
witness's complete row equal to the actual row. Only the actual current
reads are receipts; hypothetical candidates supply local computations.
This reuses the paid existence construction, with no new equality port.
Finally a search over $h$ terminates if some test is true. Neither the
formula decision nor this argument bounds how many false tests precede a
true one, or detects that none will ever be true. $\square$

**Proposition 7.6 (finite-syntax service checking and its quantifier boundary).**
Under Assumption 7.3, a supplied finite reply tree with fixed physical
addresses and fixed read epochs, all at least $N$ and nondecreasing along
each path, has decidable leaf reachability and decidable constancy of the entire original row at each
leaf. When every reached leaf is constant, effective output labels turn
it into a permitted actual service. Its exact sourcewise path costs and
separate worst vector and weighted worst sums are computable, with an
original-source witness for every reached leaf. This assertion does not
quantify over unbounded choices of addresses or over all program codes.

Proof. For a leaf $t$, let $\mathsf{Path}_t(X)$ be the finite conjunction
of its acquired replies, using $\tau_m$ and navigation at the fixed
physical word at each vertex. It is a formula from Theorem 7.2. Reachability
is

$$
\exists X\ (\mathsf{Adm}(X)\land\mathsf{Path}_t(X)),
\tag{ABC.7.5}
$$

and row constancy is

$$
\forall X,Y\quad
 [\mathsf{Adm}(X)\land\mathsf{Adm}(Y)\land
  \mathsf{Path}_t(X)\land\mathsf{Path}_t(Y)]
 \Longrightarrow\operatorname{Same}_Q(X,Y).
\tag{ABC.7.6}
$$

Both are finite sentences under the assumption. For each nonempty leaf,
enumerate concrete finite sources and evaluate (ABC.1.3) and its fixed
path until obtaining a witness. This terminates because (ABC.7.5) was
first decided true; empty leaves do not enter the search. Compute the
witness's full $Q$ row and use it as that leaf's output. Equation
(ABC.7.6) proves its correctness for every source reaching the leaf.

Execute the stipulated nonnegative epoch differences by actual updates,
and the same fixed literal words by actual reads. Induction on the reply
path shows that every actual source follows its own formula and reaches
a nonempty leaf. Halt there is genuine and absorbing. A root halt and
zero-length root words are included. Each reached leaf has fixed costs
$(q_t,a_t,\ell_t)$, where $a_t$ is its last read epoch minus $N$ (zero at
a root halt), and $\ell_t$ is the sum of the submitted literal lengths.
There are no post-final-read updates in this stated tree contract.
Maximizing each coordinate or, separately, $\lambda\cdot(q_t,a_t,\ell_t)$
over the finitely many reached leaves gives the stated exact values.
Each retained source witness realizes its leaf costs. No leafwise
marginals from different sources have been combined. The enumeration is
for outputs of an already supplied finite tree, not a search over all
services. $\square$

## 8. Remaining decision and resource questions

**Definition 8.1 (three distinct effective obligations).** The unrestricted
bounded-recovery question remains [ARH, Definition 9.1][ARH] on precisely
(ABC.1.3): decide whether any determining original prefix exists and supply
an actual source-total full-row consumer when one does. ARH Theorems 6.1,
14.1 and 22.1 already decide their recognized root-certificate, synchronous
and constructor-elimination cases. Their restricted conclusions require
no Assumption 7.3. For arbitrary acquired inputs, the following are distinct
obligations of the present logical route.

1. **Native source interpretation.** Supply Assumption 7.3, or another
   exact uniform interpretation with its declared language and both
   original-source inclusions. Theorem 7.2 supplies finite operation
   formulas only on normal arguments; it does not fill this obligation.
2. **Existence of a determining prefix.** Decide $\exists h\,
   \operatorname{PrefDet}(D,Q,h)$ with a negative stopping argument as
   well as a positive witness. Even granting item 1 and Proposition 7.5's
   fixed-$h$ decision, this remains an additional problem.
3. **Unbounded-address service decisions and exact optimization.** Supply
   a logical or other effective decision of existential finite service
   addresses preceding universal quantification over *all* admitted
   sources, with full-row constancy as the terminal condition. Relate
   it in both directions to every permitted adaptive serial competitor,
   and supply the finite search horizons and witness extraction needed
   for the raw price, joint Pareto basis and separate rational weighted
   minimax. A finite-menu decision alone does not meet this obligation.

For item 3 the target condition has the form

$$
\exists(p_v)_v\ \forall X,Y\quad
 [\mathsf{Adm}(X)\land\mathsf{Adm}(Y)]\Longrightarrow
 \bigwedge_t
 [\mathsf{Path}_t(X;(p_v))\land\mathsf{Path}_t(Y;(p_v))
       \Longrightarrow\operatorname{Same}_Q(X,Y)],
\tag{ABC.8.1}
$$

with $p_v$ ranging over arbitrary finite physical words and with legal
monotone epochs. The finite conjunction in each path is determined by
the supplied skeleton. Unlike Theorem 7.2, (ABC.8.1) requires navigation
at variable words. It is a mathematical specification, not a formula
asserted to belong to Definition 7.1. Reachability, literal address costs
and extraction of actual terminal outputs must use the same source
interpretation as its universal quantifiers.

JRF Theorem 4.3 discharges its corresponding address quantifiers through
matched WS2S source, target and reply formulas for literal-history fibers;
Theorem 5.3 additionally uses the literal-only GB decision and a static
supplier to justify its finite Pareto search. Theorem 7.1 separately
proves weighted minimax, including zero weights and same-source sums.
Their universal operational ingredients transfer by Proposition 6.4.
The recognized ARH decisions also discharge bounded-recovery existence
and supply static consumers on their positive instances. In particular,
ARH (14.2) or (CE.22.2)–(CE.22.3) supplies a finite raw bound $K_0$ and
finite maximum physical address length $D_0$, hence a static upper budget
$(K_0,0,K_0D_0)$. These are the static-supplier hypotheses of JRF
Definition 5.1 and Lemma 5.2. Together with the epoch-five cap and cleanup,
they give the same finite cofinal rectangle of worst read and update
budgets on such a positive instance: $q\le\max(K_0,K_0D_0+\max(0,2-N))$
and $a\le\max(N,5)-N$. Cofinality compares coordinatewise worst budgets;
it does not make the static supplier cheaper on each same source.
This does not decide whether a pair in that rectangle is feasible with
arbitrarily long addresses. That independent
decision is required before JRF Theorem 5.3 searches for a minimum length;
its literal-only source-language proof is not supplied by the ARH
bounded-recovery criterion. The weighted proof retains its separate
same-source and zero-weight obligations.

The full effective conclusions therefore still require exact suppliers
for the signed morphic domain, including (ABC.8.1), with every relation
retained. Neither the finite basis conclusion of Dickson's lemma nor a
finite image of $R_Q$ supplies those missing stopping arguments.

**Proposition 8.2 (what the conjugacy adds to the supplier boundary).**
The correspondences of §§2–6 preserve the unrestricted recovery question
and every specified resource objective. They convert each finite native
construction and each fixed-epoch whole-subtree comparison into canonical
pairing, guarded native navigation, equality and uniform rank translation.
They give no implication from the ambient term-power decision to
unrestricted native bounded recovery without the additional obligations
of Definition 8.1.

Proof. Theorem 2.2 covers every original source, Theorem 2.3 covers its
exact forward action, Theorem 5.2 covers the complete acquired fiber,
and Theorem 4.2 covers the entire original row. Theorem 6.2 gives both
actual-service directions and exact sourcewise costs; Corollary 6.3 gives
the corresponding optimization identities. These prove preservation of
the original question, not its decidability.

Theorem 7.2 identifies finite formulas for the indicated native operations
on normal codes. Proposition 7.4 shows that merely enlarging the source
domain to all ambient terms is not a sound substitute. Proposition 7.5
uses a separately assumed domain formula and still only decides one
fixed prefix at a time. Proposition 7.6 has fixed words, whereas (ABC.8.1)
has unbounded word quantifiers. None of those proofs contains the missing
domain formula, a negative stopping rule for all $h$, or a translation of
variable-word navigation. Thus the unconditional conclusions stated here
do not assert any of those stronger decisions. $\square$

**Definition 8.3 (recognized decisions and logical supplier limits).**
The acquired-input decision suppliers have the following exact scopes.
[ARH, §§4–6][ARH] recognizes root-to-descendant certificates and computes
finite/cofinite atomic-orbit indices with every further constraint still
imposed. [ARH, §§10–18][ARH] instead recognizes the whole-input family
$\mathfrak S$: after its fixed original-prefix cover, every retained
constraint and required hole-equality comparison must reduce under its
specified test to Boolean combinations of aligned fixed-power or ground
relations. Its domains are joint padded finite-tree tuple languages.
Proposition 12.1 includes both the complete concrete exterior and every
hole-pair equality in Bad. The productive diagonal-prefix sequence of
Theorem 13.1 has finitely many states and stabilizes; Theorem 14.1 uses
that actual stopping rule and bounded original chart selection to decide
existence of a determining prefix. A negative decision yields finite
admissible bad source pairs at every requested original depth.

[ARH, §§19–25][ARH] supplies the recognized family $\mathcal E_{\rm CE}$.
Mandatory constructor definitions are eliminated by a finite search
through permitted schedules, with at most one removal per original
variable and no new variables during elimination. Surviving parameters
remain actual original subtrees; complete substitution retains every
old inequality, acquired sign and target comparison. Both the residual
domain and the reduced target comparisons must be synchronous, unless
the chart is proved empty. Proposition 23.1 includes the synchronous
family, while Propositions 23.2–23.3 exhibit genuine coupled constructor-
offset inputs beyond its unchanged frontier test, with positive and
negative full-row answers. Those examples and the criterion are supplied
results, not consequences first obtained from canonical blocks.

The interface to this volume is (ABC.5.3)–(ABC.5.5). ARH Propositions
19.4 and 20.4 supply respectively bounded chart selection and both
original-prefix directions. Its Lemma 21.4 supplies finite productive
saturation of the exact Bad automaton, and Theorem 22.1 supplies the full
static/serial existence equivalence, effective positive consumer and
finite negative witnesses. Merely having an exact canonical source
bijection does not produce that automaton or its finite state bound.
Nor does a finite chart list remove the chart-selection obligation:
ARH Proposition 24.2 gives an exact finite disjoint presentation of all
native trees with synchronous chart domains and constant within-chart
rows, yet unbounded cross-chart disagreement for $Q=\{L,R\}$.
In that example equality versus disequality of the two children cannot
be selected by a bounded original prefix. A method without that selector
must account for cross-chart Bad as well. The canonical map $B$ and the
opaque trace correspondence preserve this failure as well as positive
instances; neither grants an observer the chart or code for free.

Thus recognized cases already have negative stopping arguments independent
of §7. Arbitrary residual cyclic decorated-constructor constraints,
unsupported target comparisons and the full unrestricted boundedness
question still lie beyond these supplied decisions. Failure of a
recognizer is not a negative answer on its whole acquired fiber.
Assumption 7.3 remains a separate proposed uniform domain interpretation;
even if supplied, Propositions 7.5–7.6 alone would not give the general
stopping or variable-address decision of Definition 8.1.

The use of Kuncak–Rinard is confined to its finite term-power language over
a decidable base, with same-shape pointwise comparisons and guarded
constructors.
Its [§6.6][KR] explicitly separates this language from an extension with
selection of the base element at an arbitrary leaf; over an infinite
base such extensions can be undecidable. That caution is a boundary on
transferring its theorem, not an undecidability theorem about (ABC.1.3).
No arbitrary subterm selection or inductive domain predicate is added
here under the name of that supplier.

Similarly [Klarlund–Møller, *MONA Version 1.4 User Manual*, §§7.1–7.2][MONA]
supplies decision and counterexamples for actual WS2S formulas: positions
in the binary successor tree and finite sets of positions. To use it for
(ABC.8.1), the native source, coupled morphic relations, original target
and variable physical addresses require formulas in that language with
the proved shared-source correspondence. An encoding of finite trees
alone is insufficient. Ginsburg–Spanier applies after a Presburger
formula is obtained; fixed-shape rank arithmetic in Proposition 7.4 does
not encode arbitrary unknown shapes by itself.

The [literal acquisition model][ACQUISITION] has the same four replies,
but its policies query a fixed source and its cost counts distinct
addresses. [Exact support pruning][SUPPORT] requires supplied support,
legality and its own allowed-source domain; [exact trace replay][REPLAY]
retains its fixed-source replay hypotheses. The [joint response-cost
normalization][COST] compares a finite family of positive prototypes
with distinct-address costs. These hypotheses do not supply the raw-call,
serial-update, entire-fiber contract in Assumption 1.2. The pinned
[free magma][FREE] and [term syntax and substitution][SYNTAX] supply
ordinary construction and substitution, not a decision of coupled native
morphic constraints.

The particular canonical block construction gives an all-source action
conjugacy, guarded original-address and whole-row interfaces, and exact
transport of the acquired cells. These structural conclusions are
unconditional under Assumption 1.2; the logical decisions of §7 additionally
require Assumption 7.3. The recognized ARH decisions and their finite
productive arguments, SCR's epoch-four raw normalization, JRF's epoch-five
joint dominance, and the cited ambient logical decisions retain the
hypotheses just specified. None implies unrestricted signed-fiber
boundedness, minimum raw price or joint optimization through source
encoding alone. The remaining boundary and memory recovery questions
are exactly those of Definition 8.1.

[ARH]: https://github.com/the-omega-institute/trureturing/blob/ce58f3e6607e4269821891c7ba7e7dad5e8066f9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SCR]: https://github.com/the-omega-institute/trureturing/blob/ebeec0b680e9584d1749fe60fefb98ee1044300a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md
[JRF]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[SLH]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[TRANSPORT]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[CENTRALIZER]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[ENCODING]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/D5/S0/History/Spacetime/SourceTreeEncoding.lean
[KR]: https://arxiv.org/html/cs/0408015v1
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[MONA]: https://www.brics.dk/mona/mona14.pdf
[ACQUISITION]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[SUPPORT]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.lean
[REPLAY]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.lean
[COST]: https://github.com/the-omega-institute/trureturing/blob/8629b924d8bd0e9d5156b933ee9947465c5aee06/D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore.lean
[FREE]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Free.lean
[SYNTAX]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/ModelTheory/Syntax.lean

## 追加锚（本行以下为增补区）

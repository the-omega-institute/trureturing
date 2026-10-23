# Recursive relational observation: exact boundary and memory for bounded suffix recuts

## 1. Linear prefixes and the common-input operation contract

**Definition 1.1 (one finite linear relation).** Let $\mathbb F_q$ be a finite
field, let $m,n\ge0$, and fix a matrix $H:\mathbb F_q^n\to\mathbb F_q^m$ with
columns $h_1,\ldots,h_n$. Put $C=\ker H$. For $0\le k\le n$, write

$$
H_P^{(k)}=[h_1\ \cdots\ h_k],\qquad
H_F^{(k)}=[h_{k+1}\ \cdots\ h_n],\qquad
r_P(k)=\operatorname{rank}H_P^{(k)},\quad
r_F(k)=\operatorname{rank}H_F^{(k)},\quad r=\operatorname{rank}H.
\tag{1.1}
$$

Empty blocks have rank zero. The full admissible prefix carrier at cut $k$ is

$$
U_k=\{u\in\mathbb F_q^k:\ \exists f\in\mathbb F_q^{n-k},\quad
                         H_P^{(k)}u+H_F^{(k)}f=0\}.
\tag{1.2}
$$

All source and completion equations use this same $H$. A type is $(k,d)$
with $0\le d\le k\le n$; its states are $(k,d,u)$ for all $u\in U_k$.
Here $k$ is the known current cut and $d$ is the remaining total deletion
budget. For any word $z$ of length at least $j$, $\operatorname{tail}_j(z)$
is its ordered last $j$ entries, and $\operatorname{tail}_0(z)=()$.
Juxtaposition of words denotes ordered concatenation. At this type split

$$
u=(v,t),\qquad v\in\mathbb F_q^{k-d},\quad t\in\mathbb F_q^d,\qquad
H=[H_A^{(k,d)}\ H_D^{(k,d)}\ H_F^{(k)}],
\tag{1.3}
$$

where $H_A^{(k,d)}$ has columns $1,\ldots,k-d$ and $H_D^{(k,d)}$ has columns
$k-d+1,\ldots,k$. Set $r_A(k,d)=\operatorname{rank}H_A^{(k,d)}$.
The tuple $t$ is the ordered last $d$ coordinates of the CURRENT prefix;
it is not the last $d$ coordinates of a fixed initial prefix after later
appends.

**Definition 1.2 (supplied inputs and strict partial actions).** For every
$a\in\mathbb F_q$, the same action names $\operatorname{append}_a$ and
$\operatorname{delete}_a$ are supplied as common inputs to every comparison.
They have the following partial semantics:

$$
\begin{aligned}
\operatorname{append}_a(k,d,u)&=(k+1,d,ua),
&&k<n\ \text{and}\ ua\in U_{k+1},\\
\operatorname{delete}_a(k,d,u)&=(k-1,d-1,u_1\cdots u_{k-1}),
&&d>0\ \text{and}\ u_k=a.
\end{aligned}
\tag{1.4}
$$

A false guard is a missing edge. There is no executable failure state,
no budget replenishment, no arbitrary old-coordinate deletion, and no
operation that reads a prescribed hidden next symbol. A successful edge's
label is its requested action name and supplied value. The root readout is
$(k,d,s)$, where $s=H_P^{(k)}u$. The entire prefix, a source identifier and
an ordered operation archive are not additional root readouts.

The state is an extendable current word. The input $a$ supplies a new value;
legality asks whether that value leaves an extendable word. No tagged full
codeword is carried through an execution. In particular, a deleted value
may be replaced by a different supplied value when the new word is
extendable. Existence of a completion in (1.2) does not give permission to
read, predict or replace the unseen coordinates of one fixed hidden source.

**Definition 1.3 (all-finite-word response).** Let $\Sigma$ be the finite
alphabet of action names in Definition 1.2. A word $w\in\Sigma^*$ is legal
from a state $z$ exactly when every requested edge exists in succession.
Write $T_wz$ for its terminal state when legal. Define the partial response
$R_z(w)$ to be the terminal root readout together with the successful edge
labels when $w$ is legal, and to be undefined otherwise. The empty word is
legal. Undefined means absence of the requested path, not a failure
transition. Since every prefix of a word is also a word, equality of these
partial response functions includes every intermediate root readout and the
first missing edge.

States of different public types are not compared. At the same type write
$z\simeq z'$ when $R_z(w)=R_{z'}(w)$ for every finite word. An exact boundary
is a representation on its actual image preserving root readout, every
edge's domain, its label and its successor. The strict descent and minimal
residual universal properties used here are those of
[Process Geometry, Theorems 3.2–3.3 and 6.2](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
They preserve missing edges and types; they do not enlarge the source
carrier to a free product or supply unperformed observations.

## 2. Exact descent and explicit separating words

**Definition 2.1 (budgeted boundary image).** Define

$$
B_{k,d}(u)=(s,t)=\bigl(H_P^{(k)}u,\operatorname{tail}_d(u)\bigr),\qquad
Q_{k,d}=B_{k,d}(U_k).
\tag{2.1}
$$

The full typed representation is $(k,d,B_{k,d}(u))$. Equivalently,

$$
Q_{k,d}=\{(s,t)\in\mathbb F_q^m\times\mathbb F_q^d:\quad
 s-H_D^{(k,d)}t\in\operatorname{im}H_A^{(k,d)},\quad
 -s\in\operatorname{im}H_F^{(k)}\}.
\tag{2.2}
$$

Indeed, the first condition supplies $v$ with $H_A^{(k,d)}v=s-H_D^{(k,d)}t$,
and the second supplies a completion $f$; together they give $(v,t,f)\in C$.
The converse follows from such a codeword. Thus $Q_{k,d}$ is the actual
linear image, rather than all formal pairs $(s,t)$.

**Theorem 2.2 (all-word sufficiency and exact minimality).** For every
$0\le d\le k\le n$, equality of $B_{k,d}$ is exactly $\simeq$. In fact it is
already exactly equality of the sets of legal finite words. The boundary
updates on their legal domains are

$$
\begin{aligned}
\operatorname{append}_a: (k,d,s,t)
 &\longmapsto
 (k+1,d,s+h_{k+1}a,\operatorname{tail}_d(ta)),\\
\operatorname{delete}_a: (k,d,s,(t_1,\ldots,t_d))
 &\longmapsto
 (k-1,d-1,s-h_ka,(t_1,\ldots,t_{d-1})).
\end{aligned}
\tag{2.3}
$$

The append guard is

$$
k<n\quad\text{and}\quad
-(s+h_{k+1}a)\in\operatorname{im}H_F^{(k+1)};
\tag{2.4}
$$

the delete guard is $d>0$ and $t_d=a$. For $d=0$ the append tail is the
empty tuple and every delete edge is absent. All resulting tuples lie in
the stated target images. Every exact representation of this full carrier
has a unique surjection from its actual image onto $Q_{k,d}$ intertwining
the representation maps; these surjections preserve the typed operations.
Consequently $Q_{k,d}$ has the least number of exact states at this type.

Proof. Equation (1.2) applied to $ua$ gives (2.4). Its new syndrome uses the
column $h_{k+1}$, not $h_k$. Its last $d$ coordinates are obtained by adding
$a$ to the existing tail and retaining the last $d$ entries. This remains
valid when $d=0$ or $d=k$. For deletion, $d>0$ implies $k>0$, and $u_k=t_d$.
Removing it changes the syndrome by $-h_ka$. The older block has unchanged
length

$$
(k-1)-(d-1)=k-d,
\tag{2.5}
$$

so the new tail is exactly $t_1,\ldots,t_{d-1}$; no forgotten older symbol is
needed. If $uf\in C$, the shorter prefix can be completed by $u_kf$, so it
is still admissible. Both operations preserve $0\le d\le k\le n$.
These facts prove domain, label, root and successor descent on $Q$.
Induction on word length then proves equality of every partial response:
if a prefix has no edge, all its extensions remain absent, and otherwise
the common successor boundary determines the next step.

For necessity, let $u,u'\in U_k$ have syndromes $s,s'$. If $s\ne s'$, choose
$f=(f_1,\ldots,f_{n-k})$ with $H_F^{(k)}f=-s$, and request

$$
\operatorname{append}_{f_1}\cdots\operatorname{append}_{f_{n-k}}.
\tag{2.6}
$$

Every step is legal from $u$ because $uf\in C$. The entire word cannot be
legal from $u'$, since at cut $n$ admissibility would imply
$s'+H_F^{(k)}f=0$, contradicting $s'\ne s$. At its first missing edge the
two legal-word sets differ. If $k=n$, every admissible syndrome is zero,
so this case does not arise.

If the syndromes agree but the tails differ, let $j\le d$ be the first
position of disagreement counted from the CURRENT right end. Request

$$
\operatorname{delete}_{u_k}
\operatorname{delete}_{u_{k-1}}\cdots
\operatorname{delete}_{u_{k-j+1}}.
\tag{2.7}
$$

It is legal from $u$. The first $j-1$ deletes also exist from $u'$, but the
$j$th has a different current-last value there and is absent. Each request
has remaining budget at least one; every shorter prefix is extendable.
This gives a separator of length at most $d$. Thus no two distinct boundary
points can merge, even if syndrome is omitted from the root readout and
only type, labels and path existence are observed.

Finally, if an exact representation $a$ assigns two prefixes the same
value, strict descent along every word gives the same partial responses.
The separating words force their $B$ values to agree. Define the map on
$a(U_k)$ by $a(u)\mapsto B_{k,d}(u)$; it is well-defined, onto and unique.
Equation (2.3) makes these maps commute with each legal operation, and the
same argument preserves domain and label. This is the precise instance of
the cited Process Geometry universal property. The explicit bounded
separators and updates are the specialization to (1.4). $\square$

**Theorem 2.3 (exact remaining path length).** From any state of type
$(k,d)$ the longest legal word has length

$$
V(k,d)=n-k+2d.
\tag{2.8}
$$

Every legal step reduces $V$ by exactly one. Hence all-finite-word equality
in Theorem 2.2 can also be tested mathematically by words of length at most
$V(k,d)$.

Proof. An append raises $k$ by one; a delete lowers both $k$ and $d$ by one.
Substitution in $V$ gives the asserted decrease in both cases. Since $V$
is nonnegative at every type, no legal word can be longer. Conversely,
delete all $d$ current-last entries with their actual values. This leaves
an extendable prefix at cut $k-d$ with budget zero. Choose any completion
and append its $n-k+d$ values. The total length is $d+(n-k+d)=V(k,d)$.
Words beyond this bound are absent from every state of the original type.
The count is a combinatorial path length; no physical clock or price is
specified by it. $\square$

## 3. Exact carrier size and least supplemental alphabet

**Theorem 3.1 (minimal boundary and conditional memory counts).** At a fixed
public type $(k,d)$ the exact minimal boundary has cardinality

$$
|Q_{k,d}|=q^{\mu_d},\qquad
\mu_d=d+r_A(k,d)+r_F(k)-r.
\tag{3.1}
$$

The forward summary has image

$$
S_k=\operatorname{im}H_P^{(k)}\cap\operatorname{im}H_F^{(k)},\qquad
|S_k|=q^{\mu_0},\qquad \mu_0=r_P(k)+r_F(k)-r.
\tag{3.2}
$$

Each attainable forward summary $s$ has exactly

$$
q^{\lambda_d}\quad\text{boundary points above it},\qquad
\lambda_d=d+r_A(k,d)-r_P(k)=\mu_d-\mu_0.
\tag{3.3}
$$

Suppose a finite alphabet $M$ and a label map $L:U_k\to M$ are required to
make $B_{k,d}(u)$ recoverable from $(H_P^{(k)}u,L(u))$ for every admissible
prefix. The least possible $|M|$ is exactly $q^{\lambda_d}$. This is the
supplement for the complete bounded-operation response, rather than a
label for restoring every prefix or full codeword. All formulas count the
full admissible carrier, with no initialized reachability restriction.

Proof. Apply rank–nullity as an intermediate calculation to the linear map

$$
\Phi_d:C\longrightarrow Q_{k,d},\qquad
(v,t,f)\longmapsto (H_A^{(k,d)}v+H_D^{(k,d)}t,t).
\tag{3.4}
$$

It is onto by Definition 2.1. Its kernel is precisely

$$
\{(v,0,f):H_A^{(k,d)}v=0,\ H_F^{(k)}f=0\},
\tag{3.5}
$$

of dimension $(k-d-r_A(k,d))+(n-k-r_F(k))$. Subtracting from
$\dim C=n-r$ yields (3.1). Theorem 2.2 supplies sufficiency and minimality,
so this is a minimal response count, not merely a projection cardinality.

The intermediate forward separator in (3.2) is the classical effective
state space of the past fragment: its trimmed projection is $U_k$, its
cross-section is $\ker H_P^{(k)}$, and

$$
U_k/\ker H_P^{(k)}\cong S_k.
\tag{3.6}
$$

This forward ingredient is the state-space theorem of G. David Forney Jr.,
[*Codes on Graphs: Fundamentals*, arXiv:1306.6264v2, §§5.5 and 6.3](https://arxiv.org/html/1306.6264v2).
The latter section requires a finite connected cycle-free normal linear
or group realization and internal trimness and properness. The present
past/future split uses its effective quotient; it does not import an
arbitrary cyclic realization's minimality or any delete permission.
Since $\operatorname{im}H_P^{(k)}+\operatorname{im}H_F^{(k)}=
\operatorname{im}H$, the intersection has dimension $\mu_0$.
The all-append separator (2.6) also identifies this forward behavior exactly.

The projection $Q_{k,d}\to S_k$, $(s,t)\mapsto s$, is a linear surjection.
Its fibers are affine translates of its kernel, of dimension
$\mu_d-\mu_0=\lambda_d$. Thus every attainable $s$ has the same count (3.3).
Equivalently, after fixing $s$, the allowable tails solve
$H_D^{(k,d)}t\equiv s$ modulo $\operatorname{im}H_A^{(k,d)}$; this map has
rank $r_P(k)-r_A(k,d)$, so its kernel has dimension $\lambda_d$.

The maximum-fiber alphabet principle used in this last step is
[MinimumRollbackAlphabet](../../../D5/S0/History/Coding/MinimumRollbackAlphabet.lean),
declaration `minimum_rollback_alphabet`,
applied to the finite carrier $X=Q_{k,d}$ and projection $X\to S_k$.
For a label map defined on prefixes, pick one prefix representative of each
of the $q^{\lambda_d}$ boundary points over a fixed $s$. Any sufficient
$L$ must give them distinct labels, proving $|M|\ge q^{\lambda_d}$.
For attainment, label the points separately in each fiber by a common
alphabet of this size, and pull those labels back along $B_{k,d}$.
The pair $(s,L(u))$ then determines the unique boundary point. Label reuse
between different syndrome fibers is allowed. This is an exact finite
alphabet statement, without a physical storage or acquisition model.
$\square$

**Theorem 3.2 (public budget and endpoint types).** In the present type
range, the ordered tail has length exactly $d$, so the budget is recoverable
from that length. Recording $d$ again does not multiply (3.1) by an
independent budget factor. If all remaining budgets at one known cut are
included as distinct public types, their total boundary count is

$$
\sum_{d=0}^k q^{d+r_A(k,d)+r_F(k)-r}.
\tag{3.7}
$$

The endpoint counts at a fixed type are

$$
\begin{aligned}
d=0:&\quad |Q_{k,0}|=q^{r_P(k)+r_F(k)-r},\quad |M|_{\min}=1,\\
d=k:&\quad |Q_{k,k}|=q^{k+r_F(k)-r},\quad |M|_{\min}=q^{k-r_P(k)},\\
k=n:&\quad |Q_{n,d}|=q^{d+r_A(n,d)-r},\\
n=0:&\quad k=d=0,\quad |Q_{0,0}|=1.
\end{aligned}
\tag{3.8}
$$

Proof. The tuple in $Q_{k,d}$ lies in $\mathbb F_q^m\times\mathbb F_q^d$
and its declared length is $d$. Distinct public budget types form a disjoint
union, giving the sum rather than a product with an independent factor.
For $d=k$, $H_A$ is empty; for $k=n$, $H_F$ is empty; for $n=0$, $H$ has no
columns and rank zero. Substitution in Theorem 3.1 gives all four formulas.
In particular $k=0$ forces $d=0$, and at $k=n,d=0$ the forward state is the
single zero syndrome although several full codewords can remain. $\square$

**Theorem 3.3 (initialized reachability is a separate restriction).** If
only $R_{k,d}\subseteq U_k$ is supplied by an initialized execution family,
the minimal count at that type is $|B_{k,d}(R_{k,d})|$. The full-carrier
count (3.1) applies to this restriction exactly when its boundary image is
all $Q_{k,d}$. It need not apply even when the initial state is admissible.

Proof. The separating words in Theorem 2.2 remain valid for every pair in
the restricted carrier, and equality of $B$ remains sufficient. Its exact
quotient is therefore its own boundary image. For strict inequality, take
$H=[1\ 0\ 1]$ over $\mathbb F_q$, initial prefix $00$, cut $k=2$ and
remaining budget $d=1$. Every length-two prefix is extendable, and (3.1)
gives $q^2$ full boundary points. A path returning to type $(2,1)$ cannot
contain a delete, because the budget never rises; with no delete, any
append strictly raises the cut. Hence this initialized family has only
its initial point at that type. This restriction does not remove the
possible continuation words from that point. $\square$

## 4. The budget filtration and exact recovery between summaries

**Definition 4.1 (comparison of budget presentations).** Fix $H$ and $k$.
For $0\le d\le e\le k$, compare $B_{k,d}$ and $B_{k,e}$ on the SAME carrier
$U_k$. The forgetful map is

$$
\rho_{e,d}:Q_{k,e}\longrightarrow Q_{k,d},\qquad
(s,\operatorname{tail}_e(u))\longmapsto(s,\operatorname{tail}_d(u)).
\tag{4.1}
$$

These maps compare information about one current prefix under different
declared budgets. They are not operations that replenish an exhausted
budget or identify the two operation menus. Recovering an $e$-tail from a
$d$-summary does not grant permission for $e$ deletions.

**Theorem 4.2 (uniform refinement fibers and exact recovery criterion).**
The map $\rho_{e,d}$ is onto. Every fiber has cardinality $q^{\delta_{d,e}}$,
where

$$
\delta_{d,e}=e-d+r_A(k,e)-r_A(k,d),\qquad
0\le\delta_{d,e}\le e-d.
\tag{4.2}
$$

The least supplemental alphabet needed to recover the $e$-summary from
the $d$-summary has size $q^{\delta_{d,e}}$. A decoder recovering $B_{k,e}(u)$
from $B_{k,d}(u)$ for ALL $u\in U_k$ exists if and only if

$$
\delta_{d,e}=0
\quad\Longleftrightarrow\quad
r_A(k,d)-r_A(k,e)=e-d.
\tag{4.3}
$$

Let $H_E$ be the columns $k-e+1,\ldots,k-d$, so
$H_A^{(k,d)}=[H_A^{(k,e)}\ H_E]$. The equivalent structural condition is that

$$
\overline H_E:\mathbb F_q^{e-d}\longrightarrow
\mathbb F_q^m/\operatorname{im}H_A^{(k,e)}
\tag{4.4}
$$

is injective. The refinement increments add:
$\delta_{d,f}=\delta_{d,e}+\delta_{e,f}$ for $d\le e\le f\le k$.

Proof. Both maps in (4.1) come from the same $u$, proving surjectivity.
It is a linear map between the actual linear images. Their dimensions
from (3.1) differ by (4.2), so rank–nullity gives the uniform fiber size.
Adding $e-d$ columns changes rank by an integer between zero and $e-d$,
which proves the two bounds. The finite maximum-fiber principle cited in
Theorem 3.1 gives the exact supplemental alphabet, now with
$X=Q_{k,e}$ and $U=\rho_{e,d}$.

If a decoder exists, two prefixes with the same $d$-summary must have the
same $e$-summary. Since every point of $Q_{k,e}$ has a prefix representative,
$\rho_{e,d}$ must be injective. Conversely a bijective $\rho_{e,d}$ supplies
its inverse as a decoder. This is the injective-record recovery principle of
[ExactRollbackInjectivityCriterion](../../../D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion.lean),
declaration `exact_rollback_iff_joint_record_injective`,
used on the nonempty finite carrier $Q_{k,e}$; here the constant extra record
asks whether the $d$-summary alone suffices. By the fiber size, injectivity
is exactly $\delta_{d,e}=0$. The rank of (4.4) is
$r_A(k,d)-r_A(k,e)$, proving the structural equivalence.

For an explicit decoder when this condition holds, write the $e$-tail as
$(w,t)$ with $t$ the known $d$-tail and put

$$
y=s-H_D^{(k,d)}t.
\tag{4.5}
$$

In the quotient of (4.4), the equation for the older part is
$\overline y=\overline H_Ew$. Since $\overline H_E$ is injective, its inverse
on its image gives the unique $w$, hence $(s,(w,t))$ is the desired
$e$-summary, with $(w,t)$ the concatenated $e$-tail.
For $\delta_{d,e}>0$, the same equation has $q^{\delta_{d,e}}$ choices of $w$;
each is realized by an older part and a completion, so a decoder cannot
choose correctly for every prefix. Finally the displayed rank differences
telescope, proving additivity. The algebraic decoder changes the
presentation of a current prefix, not its legally remaining resource.
$\square$

**Theorem 4.3 (sharp one-step memory increments).** For $0\le d<k$,

$$
\mu_{d+1}-\mu_d=\lambda_{d+1}-\lambda_d
=1+r_A(k,d+1)-r_A(k,d)\in\{0,1\}.
\tag{4.6}
$$

The increment is zero exactly when the column $h_{k-d}$ is independent
modulo the span of columns $1,\ldots,k-d-1$. It is one exactly when that
column belongs to their span. Thus an additional permitted suffix recut
can require either no extra alphabet symbols or an exact factor $q$.
Both cases occur in one nontrivial admissible prefix family.

Proof. Removing $h_{k-d}$ from $H_A^{(k,d)}$ reduces rank by zero or one.
Equation (4.6) and the span criteria follow from (3.1) and (3.3). If the
column is independent modulo the older columns, its newly retained value
is already determined by the syndrome and known tail through (4.4).
If it is dependent, a nonzero change in that value can be compensated by
older coordinates, so its new distinction was previously lost.

For sharpness take $H=[1\ 0\ 1]$ at $k=2$ over any $\mathbb F_q$.
Every prefix $(u_1,u_2)$ has completion $-u_1$. The successive boundaries are

$$
B_{2,0}(u)=(u_1,()),\qquad
B_{2,1}(u)=(u_1,(u_2)),\qquad
B_{2,2}(u)=(u_1,(u_1,u_2)).
\tag{4.7}
$$

Their dimensions are $1,2,2$, and their supplemental dimensions over the
forward summary are $0,1,1$. The first new value $u_2$ costs a factor $q$;
the second new value $u_1$ is already determined. Hence both bounds are
attained without a singleton prefix family. $\square$

## 5. Recovery of the current prefix and of a full source snapshot

**Definition 5.1 (distinct reconstruction questions).** Current-prefix
recovery asks for $D:Q_{k,d}\to U_k$ with
$D(B_{k,d}(u))=u$ for every $u\in U_k$. Full-source snapshot recovery asks
for $E:Q_{k,d}\to C$ with

$$
E(B_{k,d}(x_1,\ldots,x_k))=x\qquad(x\in C).
\tag{5.1}
$$

The latter tests a static map on full codewords, and does not add a hidden
source to the action semantics of Definition 1.2. No ordered execution
history is an input to either decoder.

**Theorem 5.2 (exact hidden fibers and recovery boundaries).** Every point
of $Q_{k,d}$ has exactly

$$
q^{k-d-r_A(k,d)}\quad\text{current-prefix preimages},
\tag{5.2}
$$

and exactly

$$
q^{(k-d-r_A(k,d))+(n-k-r_F(k))}\quad\text{full-codeword preimages}.
\tag{5.3}
$$

Consequently current-prefix recovery is possible exactly when

$$
\operatorname{rank}H_A^{(k,d)}=k-d,
\tag{5.4}
$$

whereas full-source snapshot recovery is possible exactly when BOTH

$$
\operatorname{rank}H_A^{(k,d)}=k-d,
\qquad \operatorname{rank}H_F^{(k)}=n-k.
\tag{5.5}
$$

If supplemental records are allowed in addition to $B$, their least
alphabet sizes for these two tasks are respectively the quantities in
(5.2) and (5.3). At $d=k$ the prefix is always recoverable, but the unseen
completion is recoverable only when $H_F^{(k)}$ is injective. At $k=n$ the
two recovery questions coincide. At $n=0$ both decoders are the unique maps
between singleton carriers.

Proof. For $(s,t)\in Q_{k,d}$, the older prefix block satisfies

$$
H_A^{(k,d)}v=s-H_D^{(k,d)}t.
\tag{5.6}
$$

There is at least one solution and its solution set is an affine translate
of $\ker H_A^{(k,d)}$. Every such $v$ gives an admissible prefix with the
same $s,t$, because a completion of $s$ also completes this prefix. This
proves (5.2). For a full codeword, independently solve

$$
H_F^{(k)}f=-s.
\tag{5.7}
$$

Its nonempty solution set has $q^{n-k-r_F(k)}$ elements. Every pair of a
solution of (5.6) and a solution of (5.7), together with $t$, is a codeword;
there is no additional joint constraint. Multiplication gives (5.3).
These fiber dimensions are nonnegative. The injective-record recovery
principle cited in Theorem 4.2 yields (5.4) and (5.5); its finite
maximum-fiber counterpart yields the two least supplemental alphabets.
For $d=k$ the older block is empty, and for $k=n$ the completion block is
empty, proving the endpoints. These are ordinary exact reconstruction
conditions, not claims that a decoder or its input has been acquired.
$\square$

**Theorem 5.3 (least budget presentation recovering the prefix).** At a
fixed cut define

$$
\ell_k=\max\{j\in\{0,\ldots,k\}:\operatorname{rank}[h_1\ \cdots\ h_j]=j\}.
\tag{5.8}
$$

Then the least $d$ for which $B_{k,d}$ recovers every current prefix is
$d_{\min}=k-\ell_k$. If $H_F^{(k)}$ has full column rank, this is also the
least budget presentation recovering every full source snapshot. If it
does not, no $d\le k$ recovers every full source snapshot.

Proof. Linear independence of an initial set of columns implies
independence of every smaller initial set. Thus the indices satisfying
the condition in (5.8) are exactly $0,\ldots,\ell_k$. Equation (5.4) holds
exactly when $k-d\le\ell_k$, giving the least $d$. Equation (5.5) supplies
the independent completion condition. This is a threshold for summaries
under declared budgets; it does not create deletion credit or recover
past operations. $\square$

## 6. Finite countermodels to stronger operation contracts

**Theorem 6.1 (fixed hidden-source reads do not descend).** There is a
finite linear source for which the boundary at an empty cut identifies two
full sources but their next hidden-source read differs. Therefore the
common-input append theorem cannot be transferred to a read of the actual
next coordinate of a fixed hidden codeword without an additional condition.

Proof. Over $\mathbb F_2$ let $H=[1\ 1]$, so $C=\{00,11\}$. At $k=d=0$
both full sources have the same empty prefix and the same boundary
$(s,t)=(0,())$. Define a read action on a tagged state $(x,k)$ that returns
$x_{k+1}$ and advances the cut without changing $x$. Its first response is
zero for $x=00$ and one for $x=11$. If instead a requested
$\operatorname{read}_a$ is legal only when $x_{k+1}=a$, then
$\operatorname{read}_0$ exists at one source and is absent at the other.
Neither version is constant on the proposed boundary fiber.

In Definition 1.2, $\operatorname{append}_0$ is legal from the empty prefix
because $0$ has completion $0$. It supplies that prefix value; it does not
report the first value of the tagged source $11$. The countermodel
separates the two contracts even though the same $H$, source relation,
cut and static image count are used. A fixed-source read requires its value
and guard to be constant on the actual observed source fiber, the strict
criterion of Process Geometry Theorem 3.2. $\square$

**Theorem 6.2 (an index map cannot supply omitted old values).** Retaining
an index map together with $(s,t)$ is insufficient for arbitrary
old-coordinate actions whose guard tests the value at the requested index.
The obstruction persists for unguarded deletion when the new syndrome or
the removed value is a response.

Proof. Over $\mathbb F_2$ take

$$
H=[1\ 1\ 0\ 0],\qquad k=3,\quad d=1,\qquad
u=000,\quad u'=110.
\tag{6.1}
$$

Both prefixes have completion zero, syndrome zero and current tail zero.
Their retained index map is the same ordered set $I=(1,2,3)$. Extend the
operation language to $\operatorname{erase}_{i,a}$, which deletes the
assigned coordinate $i$ only when $i\in I$, credit remains and its CURRENT
value is $a$. All surviving coordinate labels are preserved, and
admissibility means extendability of the surviving assignment in the same
relation $C$. Removing an assignment always leaves an extendable
assignment. For $i=1,a=0$, the guard holds at $u$ and fails at $u'$, despite
equal $(I,d,s,t)$.

For unguarded erasure of index 1, both states have the same survivor index
set $(2,3)$, but the survivor values are respectively $(0,0)$ and $(1,0)$.
Their syndrome, formed using the original labeled columns $h_2,h_3$, is
respectively zero and one; their removed values also differ. Thus an index
map specifies WHICH coordinates survive and cannot restore WHAT values
were omitted. Suffix descent used the stored current-last value and
(2.5); neither supplies the old value at index 1. This countermodel does
not assert that arbitrary erasure must retain every prefix coordinate in
every relation; it disproves sufficiency of the stated summary. $\square$

**Theorem 6.3 (replenishment destroys the bounded-tail guarantee).** A
reset operation that replenishes the deletion budget can require older
values absent from the bounded boundary, even when its cut and new budget
are public.

Proof. Let $H=0$ over $\mathbb F_2$, $n=2$, and compare type $(2,1)$ prefixes
$00$ and $10$. They have equal syndrome and last-one tail. Both execute
$\operatorname{delete}_0$, reaching cut 1 and budget 0 with equal boundary.
Add a reset edge that raises the budget there to 1, without changing the
prefix. Its successor must support $\operatorname{delete}_0$ at prefix $0$
but not at prefix $1$. Thus the common old boundary cannot determine the
reset successor behavior. The two-deletion experiment was forbidden by
the original total budget; treating the budget as a reusable window
changes the required residual relation. $\square$

**Theorem 6.4 (even full current recovery does not recover ordered history).**
An exact current boundary can uniquely determine the entire current source
snapshot and still fail to determine the ordered operation history, its
intermediate cut sequence or its intermediate states.

Proof. Let $H=I_2$ over $\mathbb F_2$, so the sole codeword is $00$. Start at
$(k,d,u)=(2,2,00)$. The two words

$$
\begin{aligned}
w_1&=\operatorname{delete}_0\operatorname{append}_0
      \operatorname{delete}_0\operatorname{append}_0,\\
w_2&=\operatorname{delete}_0\operatorname{delete}_0
      \operatorname{append}_0\operatorname{append}_0
\end{aligned}
\tag{6.2}
$$

are both legal and end at $(2,0,00)$ with the same boundary. Their cut
sequences are respectively $(2,1,2,1,2)$ and $(2,1,0,1,2)$, so their ordered
histories and intermediate prefixes differ. At the terminal type,
$H_A=I_2$ and $H_F$ is empty; (5.5) holds, giving exact recovery of the unique
full source. Nonetheless no function of this terminal boundary can return
both distinct words or cut sequences. An explicitly retained path archive
would be a different input and a different task, as in
[Process Geometry, Theorems 6.4–6.5](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
$\square$

## 7. Relational expressions and their precise mutual recovery

**Definition 7.1 (four presentations in this contract).** The interface
presentation is the known cut, remaining credit and the strict tree of all
legal future action words with their labels and root readouts. The process
presentation is one realized ordered word and its evolving typed states.
The boundary presentation is $(k,d,s,t)$ in the actual images $Q_{k,d}$.
The finite memory presentation is a forward syndrome together with a
supplemental label sufficient for that boundary. These terms refer to the
relation and operations of Definitions 1.1–1.3, not to physical space,
physical time or an undeclared native source.

**Theorem 7.2 (interface-to-memory equivalence with reconstruction limits).**
For the full carrier of Definition 1.1, at each fixed known type the
interface, minimal boundary and an optimal memory presentation are
mutually recoverable. The required memory supplement has exactly
$q^{\lambda_d}$ labels above the forward syndrome, and changing the declared
budget refines that presentation by exactly $q^{\delta_{d,e}}$ points per
fiber. This correspondence recovers every legal continuation response;
it recovers the current prefix only under (5.4), a full source snapshot
only under (5.5), and does not in general recover a realized ordered past.

Proof. The boundary gives the entire interface recursively through the
root readout, guards and typed updates in Theorem 2.2. Conversely, two
boundary points with equal interface would have the same legal words;
(2.6)–(2.7) force the points to agree. Thus the correspondence from $Q$ to
the actual interface image is bijective. Choose the fiberwise label map of
Theorem 3.1, defined on $Q$, rather than an arbitrary prefix label carrying
extra distinctions. Then $(s,L)$ determines $(s,t)$, and $(s,t)$ determines
that chosen label, giving both directions for the optimal memory
presentation. Theorem 4.2 gives exactly the refinement count and its
zero-increment recovery criterion; different physical costs or
operation menus are not identified by that count.

The prefix and snapshot qualifications are necessary and sufficient by
Theorem 5.2. Theorem 6.4 excludes recovery of ordered history even when
full snapshot recovery holds. Theorem 6.1 excludes a general transfer from
supplied inputs to actual hidden-source reads, and Theorem 6.2 excludes a
transfer from suffix operations to value-guarded old-coordinate actions.
This interface-to-memory bridge is the repo-derived bounded-operation
specialization of the cited strict residual, forward trellis and
finite-fiber principles. Those intermediate principles retain their
original attribution; no assertion of literature originality is required
for the specialization. $\square$

**Definition 7.3 (conditions for a further source or physical interpretation).**
A source-faithful interpretation in another relational system requires a
specified common source carrier and a map preserving the compared states,
root readouts, operation names and parameters, each strict legal domain,
labels and successors. If inverse recovery of that source is sought, the
map must additionally be injective on the declared source carrier. An
interpretation of an ordered past must also carry the requisite history
record. An interpretation in physical space or time must specify spatial
and temporal readouts and their relationship to those same transitions;
any acquisition, precision, storage or energy assertion needs its own
resource relation. Without these additional data the finite-field
interface correspondence of Theorem 7.2 is not a recovery map for another
source, an ordered past or a physical realization.

## 追加锚（本行以下为增补区）

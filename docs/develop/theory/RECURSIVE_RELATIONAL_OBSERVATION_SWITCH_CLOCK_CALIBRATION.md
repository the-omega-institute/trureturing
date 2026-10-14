# Recursive Relational Observation: Exact Retained Calibration for Reference Switches

## 1. Native sources and the complete service input

**Assumption 1.1 (separated original ages and authentic captures).**
Fix integers $D,H\ge0$, put $r=2^D$, $q=H+1$, and let
$I=\{0,\ldots,r-1\}$. Write $W_D=(w_0,\ldots,w_{r-1})$ for the
lexicographically ordered words of length $D$ in $\{L,R\}$, so
$w_0=L^D$. Sources are actual finite nonempty ordered full trees with
leaf labels $\alpha,\beta$ and the substitution

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

Let $T_n=\rho^n\alpha$ and let $\mathcal B_D$ be the complete
ordered depth-$D$ skeleton. The source domain is the independent box

$$
\mathcal A=\{0,\ldots,H\}^{I},\qquad
X_a=\mathcal B_D[(T_{iq+a_i})_{i\in I}].
\tag{SCC.1}
$$

This is the family of [Native Alpha Recut Memory, Assumption 16.1][NAR].
Its complete initial literal row is acquired before any future edge or
epoch is selected. The right clock is

$$
c(\alpha)=0,\qquad c(\beta)=1,\qquad
c(\langle u,v\rangle)=2+c(v).
$$

At an authentic stationary capture of $\rho^s X_a$, an acquisition
procedure obtains the right clock at the original slot $w_i$:

$$
K_i^a(s)=c((\rho^s X_a)|_{w_i})=iq+a_i+s.
\tag{SCC.2}
$$

Original-slot transport and `right_clock_iterate` supply (SCC.2);
all these slots are reached already at epoch zero. In particular the
initial acquired tree computes $a_i=c(X_a|_{w_i})-iq$. Distinct age
vectors give distinct native trees, since a differing slot has a
differing right clock.

**Definition 1.2 (an early source code and a later switch).**
Fix a public directed graph $G\subseteq I\times I$. Loops are allowed.
An encoder is any function $E:\mathcal A\to\mathcal L$ with effective
finite labels on its image. Because $\mathcal A$ is finite and its
coordinates are acquired, every such function is available as a finite
table; its installation and evaluation costs are separate resources.
The code is chosen from the initial acquisition, before both the
future edge $i\to j$ and the epochs are known.

After a complete handoff, the entire source-dependent service input is

$$
(E(a),i,K_i^a(s),j,K_j^a(t)),
\qquad (i,j)\in G,\quad 0\le s\le t\le2H.
\tag{SCC.3}
$$

The epochs are integers and authentic indices of the same pure-$\rho$
history rooted at $X_a$; neither $s$ nor $t$ is an input. One uniform
deterministic decoder must return $t-s$ for every displayed choice.
No further source port is available to this decoder. The old address
and old clock in (SCC.3) are explicit retained operands, not part of
$E$'s separately measured alphabet.

Complete handoff means that all other accessible source-dependent
state has been discarded. This includes initial literals, subtree
handles, source identities, acquisition transcripts, epochs, timing
advice, allocation choices and source-dependent control state.
Surviving state must be a function of (SCC.3) and public parameters.
A saved pointer whose contents remain readable is an additional port
and changes this contract. Authentication of the captures and the
common history is a premise, not information extracted from their
numerical agreement.

**Assumption 1.3 (legal acquisition and the price being measured).**
The full initial tree can be acquired by a finite traversal during a
stationary capture. Each later clock can be acquired by following the
right spine from the materialized original address $w_i$ until its
terminal leaf, and returning twice that suffix length plus its label
bit. Each request is an actual literal-address Read with reply
$\alpha$, $\beta$, branch or absent. No clock or subtree is a primitive
native reply. A concurrent acquisition may instead use a separately
justified common-version capture; the mathematical contract still
requires the resulting operand to come from that version.

After acquisition, the raw trace and every extra distinction are
removed as in Definition 1.2. All acquiring Reads, their literal
lengths, descriptor production, source capture, storage, parsing,
arithmetic and cleanup remain costs. The quantity minimized below is
only the number of possible early source-summary labels, conditional
on any explicitly retained old code. It is neither the total memory
of (SCC.3) nor an acquisition or physical-resource optimum.

**Definition 1.4 (actual restrictions and extra retained information).**
A public nonempty subset $A\subseteq\mathcal A$ restricts the possible
initial sources but retains every edge and epoch allowed in (SCC.3)
for each member. An already retained code is an arbitrary effective
function $B:A\to\mathcal B$, acquired before those future choices.
Its nonempty actual fibers are

$$
A_b=\{a\in A:B(a)=b\},\qquad b\in B(A).
\tag{SCC.4}
$$

When $B$ is present, the complete entry is (SCC.3) together with $B(a)$;
all other state is still excluded. An additional code $E$ is computed
while the initial source is available. Its labels may be reused on
different $B$-fibers because the decoder receives $B$.

The case without $B$ means constant $B$. A purported restriction on
sources that also forbids some future epochs is a different domain;
Theorem 2.2 uses the full specified epoch window on each actual fiber.

## 2. Native indistinguishability and all encoders

**Definition 2.1 (edge calibration and reference components).**
For $a\in A$ put

$$
Q_G(a)=(a_j-a_i)_{(i,j)\in G},\qquad
\Delta_{ij}(a)=(j-i)q+a_j-a_i.
\tag{SCC.5}
$$

Let $\mathcal C(G)$ be the components of the underlying undirected
graph, including isolated vertices. For each component $C$, define

$$
v_i(a)=a_i-\min_{h\in C}a_h\quad(i\in C),\qquad
V_G(a)=(v_i(a))_{i\in I}.
\tag{SCC.6}
$$

Thus every component has minimum zero. $V_G$ records relative ages,
not the component's common age. The known slot term $(j-i)q$ is kept
in $\Delta$ because spatial comparisons use actual clock readings.

**Theorem 2.2 (exact native criterion for arbitrary early encoders).**
For every nonempty $A\subseteq\mathcal A$ and every $B,E$ as above,
uniform recovery from the complete input of Definition 1.4 is possible
if and only if

$$
\forall a,b\in A:\quad
 B(a)=B(b)\ \land\ E(a)=E(b)
 \ \Longrightarrow\ Q_G(a)=Q_G(b).
\tag{SCC.7}
$$

Equivalently, on each joint retained-code fiber, $a_i-b_i$ must be
constant on every $C\in\mathcal C(G)$. Equivalently, $V_G$ is constant
there. The criterion includes all arbitrary encoders, not only codes
that explicitly store addresses or reference differences.

Proof. If (SCC.7) holds, a finite table recovers the common calibration
of each nonempty joint fiber. On an actual input write $k=K_i^a(s)$
and $l=K_j^a(t)$. Return

$$
\mathsf{Dec}(B(a),E(a),i,k,j,l)
 =l-k-\Delta_{ij}(a)=t-s.
\tag{SCC.8}
$$

This reuses the signed calibration mechanism of [AAR, Proposition
6.3][AAR]. The unknown epochs are not evaluated by the decoder.
Inputs outside its actual image may be rejected or assigned an
arbitrary value; no accuracy there is required.

For necessity take $a,b$ in the same joint fiber and an allowed edge
with $a_j-a_i\ne b_j-b_i$. Put

$$
\begin{aligned}
d_i&=b_i-a_i,&d_j&=b_j-a_j,\\
s&=H+\min(0,d_i),&t&=H+\max(0,d_j),\\
s'&=s-d_i=H-\max(0,d_i),&
t'&=t-d_j=H-\min(0,d_j).
\end{aligned}
\tag{SCC.9}
$$

Each $d$ lies in $[-H,H]$. Consequently

$$
0\le s\le H\le t\le2H,\qquad
0\le s'\le H\le t'\le2H.
$$

The two histories are the actual trajectories of $X_a$ at epochs
$s,t$ and of $X_b$ at epochs $s',t'$. Equation (SCC.2) gives

$$
K_i^a(s)=K_i^b(s'),\qquad K_j^a(t)=K_j^b(t'),
\qquad (t'-s')-(t-s)=d_i-d_j\ne0.
\tag{SCC.10}
$$

Their entire decoder inputs agree, including the explicitly retained
old address and clock, but the required outputs differ. Each history
separately has one genuine native source and correctly ordered
captures. This does not splice endpoints from different sources into
one purported history. Extra differences in the producers' discarded
traces are unavailable precisely by the complete-handoff premise.
A deterministic decoder cannot serve both histories.

Finally, equality of edge differences propagates along an undirected
path, reversing signs when an edge is traversed backwards. It is
therefore equivalent to componentwise constancy of $a-b$. Subtracting
each component minimum gives equivalence to equality of $V_G$.
The reverse implications follow by subtraction on each edge. $\square$

**Theorem 2.3 (a concrete collision on a fixed-minimum source fiber).**
For $D=H=1$, $G=\{(0,1)\}$, take

$$
a=(0,0),\qquad b=(0,1),\qquad
X_a=\langle T_0,T_2\rangle,\qquad
X_b=\langle T_0,T_3\rangle.
\tag{SCC.11}
$$

Both sources have the same phase-sensitive minimum $z=2$. If their
retained codes agree, no service in Definition 1.2, even with that $z$
retained, can recover every lag.

Proof. The two actual capture pairs are

$$
\begin{array}{c|c|c|c|c}
\text{source}&(s,t)&K_0(s)&K_1(t)&t-s\\\hline
X_a&(1,2)&1&4&1\\
X_b&(1,1)&1&4&0.
\end{array}
$$

Here $T_2=\langle\beta,\alpha\rangle$ and
$T_3=\langle T_2,\beta\rangle$. Thus the old slot in both histories
is $T_1$, and the later slot in both is $T_4$. Their queried right
spines and clock values are genuine. The minimum recurrence in
Definition 4.1 gives $m(X_a)=m(X_b)=2$; their required lags still differ.
$\square$

**Theorem 2.4 (the time-window premise has content).**
If the only allowed captures are $s=t=0$, uniform lag recovery needs
one source-summary label for every $G$, even when $Q_G$ varies.
Thus (SCC.7) need not remain necessary after arbitrary restrictions
on future epochs.

Proof. The constant output zero is correct on that restricted service
domain. For $D=H=1$ and the sources in (SCC.11), the edge differences
are zero and one. This violates (SCC.7) for a constant code, without
violating the restricted service. $\square$

## 3. Exact alphabets, including an arbitrary retained code

**Theorem 3.1 (attained conditional supplemental count).**
For every $A,B$ of Definition 1.4, the minimum cardinality of a single
supplemental alphabet is

$$
M(A,B,G)=\max_{b\in B(A)}|Q_G(A_b)|
       =\max_{b\in B(A)}|V_G(A_b)|.
\tag{SCC.12}
$$

An alphabet of that size suffices with one early encoder and one
uniform decoder. For a known fixed fiber $A_b$ its exact count is
$|Q_G(A_b)|$. A fixed-width binary supplement therefore needs and
suffices with $\lceil\log_2 M(A,B,G)\rceil$ bits. This is zero bits
when $M=1$.

Proof. Within one fiber, choose one source for each distinct $Q_G$
value. Theorem 2.2 forces all their supplement labels to differ,
although the conflicting edge and epochs may depend on the pair.
Hence every alphabet has at least the displayed maximum size.
Conversely, order the distinct $V_G$ values within each fiber and
encode the rank of $V_G(a)$ in its own fiber. A public table indexed
by $b$ and that rank recovers its calibration. Label ranks can be
reused across different $b$'s. Theorem 2.2 proves correctness.
Finite tables give an effective attainment; their cost is not zero.
The bit claim is the finite-alphabet pigeonhole bound and binary
encoding of its ranks. $\square$

In particular an existing code need not itself recover any reference
coordinate. The answer is not the ratio of the unrestricted minimum
to the number of old labels: different old fibers can contain
different numbers of still-conflicting relative profiles.

**Theorem 3.2 (closed count on the full independent box).**
Let $n_C=|C|$ for $C\in\mathcal C(G)$. With no other retained
source information, the exact source-summary alphabet is

$$
M_{\rm box}(G,H)=
 \prod_{C\in\mathcal C(G)}\bigl((H+1)^{n_C}-H^{n_C}\bigr).
\tag{SCC.13}
$$

Proof. A component profile $v$ in (SCC.6) is exactly a vector in
$\{0,\ldots,H\}^{C}$ with at least one zero. Every such vector is
realized by taking $a_i=v_i$ on $C$. There are $(H+1)^{n_C}$ vectors
in the box and $H^{n_C}$ with no zero. Independent components give
the product. Theorem 3.1 gives necessity and attainment. $\square$

The factor of an isolated vertex is one. With no edges the empty
calibration needs one label. When $H=0$ all factors are one. A
connected graph needs $(H+1)^r-H^r$ labels, regardless of its edge
orientations, because its edge differences determine every relative
coordinate. This is an information statement; it supplies no legal
reverse switch when only the forward edge belongs to $G$.

**Theorem 3.3 (equal old alphabet sizes can leave unequal supplements).**
For $D=H=1$ and $G=\{(0,1)\}$, the two old encodings
$B_1(a)=a_0$ and $B_2(a)=(a_0+a_1)\bmod2$ both have two labels,
but their conditional fibers have different calibration counts.
Those of $B_1$ have counts $(2,2)$; those of $B_2$ have counts
$(1,2)$. A third two-label code $B_3(a)=\mathbf1_{a=(0,0)}$
has counts $(3,1)$ on its fibers zero and one. Thus neither the
supplement on a particular fiber nor the worst-case supplemental
alphabet is determined by the old alphabet cardinality alone.

Proof. The possible edge differences are $-1,0,1$. On $a_0=0$ they
are $0,1$ and on $a_0=1$ they are $-1,0$. On even parity both
sources have difference zero; on odd parity the differences are
$-1,1$. The nonsingleton $B_3$ fiber contains $(0,1),(1,0),(1,1)$,
whose differences are $1,-1,0$. Apply (SCC.12). $\square$

## 4. The retained minimum pins one reference component

**Definition 4.1 (phase-sensitive minimum).**
For a finite tree $u$, with leaf-address set $F(u)$ and label bits
$e(\alpha)=0$, $e(\beta)=1$, put

$$
m(u)=\min_{p\in F(u)}(2|p|+e(u|_p)).
\tag{SCC.14}
$$

The recurrence and orbit law supplied by [AAR, Definition 3.1 and
Lemma 3.2][AAR] are
$m(\langle u,v\rangle)=2+\min(m(u),m(v))$ and
$m(\rho^n u)=m(u)+n$. In particular $m(T_n)=n$.

**Theorem 4.2 (the actual intersection with an AAR fixed-$z$ fiber).**
For every $a\in\mathcal A$,

$$
z(a)=m(X_a)=2D+a_0.
\tag{SCC.15}
$$

Consequently the intersection of this family with AAR's
$\mathcal T_z=\{u:m(u)=z\}$ is empty unless
$c=z-2D\in\{0,\ldots,H\}$. When it is nonempty it is precisely

$$
A_c=\{a\in\mathcal A:a_0=c\}.
\tag{SCC.16}
$$

Proof. Applying the minimum recurrence through the complete skeleton
gives $m(X_a)=2D+\min_i(iq+a_i)$. At $i=0$ the candidate is
$a_0\le H$. Every $i\ge1$ has $iq+a_i\ge H+1>a_0$. Hence the
minimum is $a_0$. The formula also holds at $D=0$, where there is
only that slot. The fiber description follows. $\square$

**Theorem 4.3 (sharp counts with the pinned component).**
Let $C_0$ be the component of $G$ containing zero. For every
$c\in\{0,\ldots,H\}$, with $z=2D+c$ retained, the exact additional
source-summary alphabet on $A_c$ is

$$
M_{\rm pin}(G,H)=
 (H+1)^{|C_0|-1}
 \prod_{C\ne C_0}\bigl((H+1)^{|C|}-H^{|C|}\bigr).
\tag{SCC.17}
$$

For any other retained code $B$, its exact supplement on this fiber
is instead

$$
\max_{b\in B(A_c)}|Q_G(A_c\cap B^{-1}(b))|.
\tag{SCC.18}
$$

If $z$ varies but remains an explicit decoder operand, one alphabet
of size (SCC.17) works for all $c$. If the combined retained pair
$(z,E)$ is counted, its minimum number of distinct values is

$$
(H+1)M_{\rm pin}(G,H).
\tag{SCC.19}
$$

Proof. On $C_0$, equality of relative profiles implies that two age
vectors differ by a constant. Their common value at vertex zero
makes that constant zero. Hence every choice of the other
$|C_0|-1$ ages has a different relative profile, giving
$(H+1)^{|C_0|-1}$. All other components remain independent,
with the counts of Theorem 3.2. Theorem 3.1 gives (SCC.17) and
(SCC.18), and permits label reuse between different $z$ values.
Distinct $z$'s distinguish the pairs in (SCC.19); summing their
identical fiber minima proves that count and its attainment.
$\square$

Thus the unrestricted product (SCC.13) cannot be imported as a
conditional lower bound into the fixed-$z$ handoff. Conversely, the
smaller supplemental count does not make the retained $z$ free.
For a connected graph the two counts are $(H+1)^r-H^r$ without $z$
and $(H+1)^{r-1}$ conditional on $z$, whereas the combined pair
$(z,E)$ has $(H+1)^r$ values. On this connected finite family that
pair identifies the whole initial age vector; this statement is not
whole-source recovery on all finite native trees.

AAR §10 quantifies over all of $\mathcal T_z$ and gives the later
service a paid native current-source port. Its acquisition bounds
and all-source correctness requirement are not replaced by this
restricted-family, already-acquired two-clock contract. Formula
(SCC.15) is their source-fiber correspondence, not an equivalence of
the two service models.

## 5. Exact information when two reference components are joined

**Definition 5.1 (the residual translations in an actual old fiber).**
Suppose an old retained input $B$ already meets Theorem 2.2 for $G$.
Fix a nonempty fiber $A_b$ and its known profile $v=V_G(a)$. For
each component put

$$
w_C=\max_{i\in C}v_i,\qquad L_C=H-w_C,\qquad
u_C=\min_{i\in C}a_i.
\tag{SCC.20}
$$

Then $a_i=v_i+u_C$ and $0\le u_C\le L_C$. Define the actual residual
set

$$
\Lambda_b=\{(u_C)_C:\ a_i=v_i+u_C\text{ defines }a\in A_b\}.
\tag{SCC.21}
$$

This set includes every constraint imposed by the old code, public
source restrictions and any retained $z$. It need not be a product.
For the full box with exactly $V_G$ retained, it is
$\prod_C\{0,\ldots,L_C\}$. On $A_c$ with exactly $V_G$ retained,
it is that product with the coordinate

$$
u_{C_0}=c-v_0
\tag{SCC.22}
$$

fixed. A profile is present on $A_c$ precisely when this integer lies
in $[0,L_{C_0}]$.

**Theorem 5.2 (actual-fiber joining law for arbitrary old information).**
Add one edge $x\to y$ between distinct old components $C$ and $F$,
and let $G'=G\cup\{(x,y)\}$. On the fiber of Definition 5.1 the
exact additional alphabet is

$$
J_b(C,F)=
\left|\{u_F-u_C:u\in\Lambda_b\}\right|.
\tag{SCC.23}
$$

For a single supplement serving all old fibers, its exact alphabet
is $\max_b J_b(C,F)$. If $x,y$ are already in one component the
answer is one. These conclusions apply to supplements acquired
before erasure while the initial source is still available.

Proof. The newly required difference is

$$
a_y-a_x=(v_y-v_x)+(u_F-u_C).
\tag{SCC.24}
$$

The profile $v$ is fixed in the old fiber. Distinct values of
$u_F-u_C$ therefore give distinct $Q_{G'}$ values; equal ones,
together with the old calibration, give identical $Q_{G'}$ values.
Theorem 3.1 gives exactly (SCC.23), with attainable per-fiber ranks
and globally reusable labels. If the endpoints were already
connected, their old differences already determine this edge.
$\square$

**Theorem 5.3 (closed joining prices and the fixed-$z$ correction).**
For the full box with exactly the old relative profile $v$ retained,
joining distinct components $C,F$ requires exactly

$$
J_v(C,F)=L_C+L_F+1=2H-w_C-w_F+1
\tag{SCC.25}
$$

labels on that fiber. Its maximum over old profiles is $2H+1$.
On the fixed-$z$ fiber $A_c$, with exactly $v$ additionally retained,
the count remains (SCC.25) if neither component contains zero.
If $C=C_0$, it becomes

$$
J_{c,v}(C_0,F)=L_F+1=H-w_F+1;
\tag{SCC.26}
$$

if $F=C_0$, exchange $C,F$. The maximum in either pinned joining
case is $H+1$.

Proof. In the full independent residual box, every integer in
$[-L_C,L_F]$ is a value of $u_F-u_C$: use $(u_C,u_F)=(0,d)$
for $d\ge0$ and $(-d,0)$ for $d\le0$. No other value is possible.
This proves (SCC.25), and profiles zero on both components attain
its maximum.

If neither joined component contains zero, pinning $u_{C_0}$ leaves
their two intervals independent. If $C=C_0$, write the fixed value
as $h=c-v_0$. The new differences are exactly
$\{-h,1-h,\ldots,L_F-h\}$, of size $L_F+1$. Setting $v=0$
on both joined components is feasible for every $c\in[0,H]$ and
attains $H+1$. The reversed case has the negated interval and the
same size. $\square$

An arbitrary old code may already encode all or part of the bridge
translation. Then (SCC.23), rather than the product-box formula,
is the answer, possibly one. Even when its size is known, the
missing difference cannot be synthesized from the old profile:
if (SCC.23) exceeds one, Theorem 2.2 supplies actual indistinguishable
histories for any code that still merges two of its values.
A later paid common-version acquisition of both references can
supply the offset by AAR 6.3, but it changes the port and cost
contract. Alternatively the larger switch graph must be supported
by the early export.

**Theorem 5.4 (several components joined at once).**
Suppose a group $\mathcal J$ of $k\ge1$ old components is joined
into one by added edges. On a fixed old profile in the unrestricted
box, the number of new relative calibrations is

$$
\prod_{C\in\mathcal J}(L_C+1)-\prod_{C\in\mathcal J}L_C.
\tag{SCC.27}
$$

If this group contains the pinned component $C_0$ on $A_c$, the
number is instead

$$
\prod_{C\in\mathcal J\setminus\{C_0\}}(L_C+1).
\tag{SCC.28}
$$

For disjoint joined groups these counts multiply when the residual
set is the independent box with at most the one pinned coordinate.
For an arbitrary $\Lambda_b$, the exact count is the number of its
classes under equality of the residual differences inside each
joined group.

Proof. In a joined group, equality of every new calibration means
that two residual vectors differ by one common integer translation.
Every such class in the unequal box $\prod_C[0,L_C]$ has a unique
representative with minimum coordinate zero: subtracting its
minimum keeps every coordinate within its own interval. The total
number of vectors minus those with every coordinate positive is
(SCC.27). With one coordinate fixed, a common translation must be
zero, so all choices of the remaining residuals are distinct;
this gives (SCC.28). Different groups have independent residuals
under the stated hypothesis. The final assertion is Theorem 3.1
on the actual set. $\square$

These formulas do not equate worst-case sequential storage with an
optimal one-shot encoding. For example three singleton components
with $H=1$ have $2^3-1=7$ final relative profiles, although the
product of two separately maximized two-component bridge alphabets
is $3^2=9$. The second bridge's actual choices depend on the first
bridge and its retained joint fiber.

## 6. Relative spatial readings and calibrated temporal readings

**Definition 6.1 (the actual image of acquired endpoint data).**
For a fixed actual retained fiber $A_b$, an allowed edge $(i,j)$ and
numbers $k,l$, define

$$
\begin{aligned}
A_b(i,k,j,l)=\{a\in A_b:\quad
s_a&=k-iq-a_i,\\
t_a&=l-jq-a_j,\quad 0\le s_a\le t_a\le2H\}.
\end{aligned}
\tag{SCC.29}
$$

All quantities are integers. A supplied tuple belongs to the actual
service image exactly when this set is nonempty. Its calibration and
lag supports are

$$
\begin{aligned}
\mathcal D_b(i,k,j,l)&=\{\Delta_{ij}(a):a\in A_b(i,k,j,l)\},\\
\mathcal L_b(i,k,j,l)&=\{t_a-s_a:a\in A_b(i,k,j,l)\}.
\end{aligned}
\tag{SCC.30}
$$

The relative spatial observable here is the difference of native
slot clocks at a common epoch. It is not a Euclidean distance or a
metric on physical space; it is signed and includes the known
address-dependent band offset $(j-i)q$.

**Theorem 6.2 (exact inverse on the actual compatible image).**
On every nonempty set (SCC.29), the maps

$$
\delta\longmapsto l-k-\delta,\qquad
\lambda\longmapsto l-k-\lambda
\tag{SCC.31}
$$

are mutually inverse bijections between $\mathcal D_b(i,k,j,l)$ and
$\mathcal L_b(i,k,j,l)$. Thus, conditional on these endpoints and
this actual retained fiber, a unique calibration is equivalent to a
unique lag. Neither support is declared uniquely determined when
the compatible set is empty.

For a finite collection of allowed actual endpoint pairs, all from one source
and history and covering a spanning tree of each component of $G$,
its $V_G$ and its vector of calibrated lags determine one another,
provided the endpoint indices and acquired readings are also kept.
Only the actual image of that collection is the domain of this
mutual recovery.

Proof. For every compatible $a$, subtraction of (SCC.29) gives
$t_a-s_a=l-k-\Delta_{ij}(a)$. Conversely each supported lag comes
from such an $a$, whose calibration is the inverse expression.
Reflection about $l-k$ is injective, proving the first assertion.

Given $V_G$, compute each $\Delta_{ij}$ and then its lag by
(SCC.31). In the other direction each retained pair and its lag
gives $\Delta_{ij}$. Subtract $(j-i)q$ and integrate these signed
edge differences along a spanning tree. The potential is determined
up to a component constant; subtracting its component minimum gives
exactly $V_G$. Common-source realizability ensures consistency with
any other retained edges. These are deterministic inverse maps on
the joint actual image, not a claim that a lag alone identifies a
relative coordinate or that endpoint numbers establish provenance.
$\square$

The one-input supports in (SCC.30) can be singletons even for an
encoder that fails uniform recovery. Theorem 2.2 is stronger because
each missing edge distinction admits the specific overlapping legal
inputs (SCC.9); it does not claim that every input is ambiguous.

**Theorem 6.3 (explicit joint-image and gluing feasibility).**
Fix a candidate component profile $v$ with minimum zero in each
component and $0\le v_i\le H$. Consider a finite ordered record
list $(i_h,k_h)_{h=1}^N$, $N\ge1$, of acquired slot clocks. This list and $v$
are realized by one source in a specified nonempty retained fiber
$A_b$, at epochs $0\le\tau_1\le\cdots\le\tau_N\le2H$, if and
only if there exist integers $u_C$ satisfying

$$
\begin{gathered}
0\le u_C\le H-\max_{i\in C}v_i,\qquad
 a_i=v_i+u_C\ (i\in C),\qquad a\in A_b,\\
\tau_h=k_h-i_hq-v_{i_h}-u_{C(i_h)},\qquad
0\le\tau_1\le\cdots\le\tau_N\le2H.
\end{gathered}
\tag{SCC.32}
$$

If $z=2D+c$ is retained, the additional equality is
$u_{C_0}=c-v_0$. If proposed signed relative differences are given
instead of $v$, they must first admit a component potential:
closed-walk signed sums must vanish, and the resulting normalized
profile must lie in $[0,H]^I$. Any prescribed new bridge differences
must also be satisfied by these same $u_C$.

Proof. A realizing source supplies $u_C=\min_{i\in C}a_i$ and its
actual epochs; (SCC.2), normalization and box membership give every
condition. Conversely take one solution of (SCC.32), form its single
$X_a$, and capture $\rho^{\tau_h}X_a$ at each specified original
slot. The right-clock supplier returns exactly $k_h$. The epochs
have the required common chronological order; the old fiber and
all bridges use the same $a$. For differences, path integration is
well defined precisely when signed closed-walk sums vanish. An
allowed profile has width at most $H$ and a feasible common shift;
the remaining membership and epoch constraints are still (SCC.32).
$\square$

This is the finite-family specialization of the common-source
obligation emphasized in [Native Cross-Epoch Relations, §§5–6][NCE].
It does not replace that volume's all-source signed-row feasibility
construction. Independent feasibility of each bridge, or just zero
cycle sums, is insufficient when retained-code constraints couple
the residual translations: all equations must have one solution in
the same $\Lambda_b$.

**Theorem 6.4 (separately attainable bridges need not glue).**
For $D=2$, $H=1$, take an old graph with four isolated vertices and
retain $z=4$ and $B(a)=a_1+a_2$. On the nonempty fiber $a_0=0$,
$B(a)=1$, each of the proposed bridges $a_1-a_0=1$ and
$a_2-a_0=1$ is attainable separately. They are not simultaneously
attainable, even though their proposed edge graph is a tree and
has no nontrivial cycle constraint.

Proof. Sources $(0,1,0,0)$ and $(0,0,1,0)$ respectively realize the
two bridge values. Every old component profile is zero. The joint
values would force $a_1=a_2=1$, contradicting the actual retained
fiber $B(a)=1$. Hence (SCC.32) has no joint solution. Both marginal
witnesses are genuine $X_a$ sources with $z=4$; they cannot be
combined into one source. $\square$

**Theorem 6.5 (endpoint equality is not authentication, even at fixed $z$).**
For $D=H=1$, let $a=(0,1)$ and $b=(0,0)$. A reading at slot one
of $X_a$ at epoch zero and a reading at slot one of $X_b$ at epoch
one are both three; both initial sources have $z=2$. Treating these
two readings as one same-source comparison would return zero,
although their displayed epoch indices differ by one.

Proof. Here $q=2$, so $K_1^a(0)=2+1+0=3$ and
$K_1^b(1)=2+0+1=3$. The old and new slot trees are both $T_3$.
But the whole first source is $\langle T_0,T_3\rangle$, whereas
the second captured tree is $\langle T_1,T_3\rangle$. It is not
$\rho\langle T_0,T_3\rangle=\langle T_1,T_4\rangle$.
Thus equality of endpoint values, even of these endpoint subtrees,
does not certify the presumed continuation. This pair is outside
the common-history contract, not a counterexample to Theorem 6.2.
$\square$

## 7. Memory boundaries and mathematical suppliers

**Definition 7.1 (separate resource coordinates).**
A source-summary alphabet count is $|E(A)|$, or the supplemental
maximum on actual fibers in (SCC.12). The combined retained state
also includes any $B(a)$, $z$, old slot index, old clock, control,
framing and address materialization required by the declared service.
For example, the uncompressed old slot index has $D$ bits, and its
clock lies between zero and $(r-1)(H+1)+3H$ under the present epoch
window. Those bounds only describe operands; their correlations,
encoding and acquisition costs are not optimized by the source-code
count. New endpoint inputs, local arithmetic space, installed tables,
peak acquisition storage, provenance validation and all paid Reads
are additional coordinates.

A quotient by component translations removes exactly the distinction
irrelevant to every allowed future switch in this finite service.
When $z$ pins a component, that translation is no longer free. When
a new bridge joins components, their relative translation becomes
relevant. This is task-relative memory; neither the quotient nor its
price is asserted to encode arbitrary tree geometry, full histories
or physical spacetime.

**Mathematical citation 7.2 (exact supplier correspondence).**
The following ingredients have the displayed roles.

| Supplier | Correspondence and limit |
| --- | --- |
| [GenealogicalFiberTransport][SOURCE], `Source`, `substitution` | Finite ordered full trees and the actual alpha/beta substitution used in (SCC.1). |
| [DelayedOriginalReadout][CLOCK], `rightClock`, `right_clock_iterate`, `right_clock_readout`, `rights` | $c(T_n)=n$, clock transport, and physical right-spine queries. `original_decoder_service` requires a given epoch and supplies no unknown epoch to this service. |
| [NativeDepthPatterns][DEPTH], `original_present_transport` | The subtree at each original $w_i$ remains its pure iterate. No claim about a previously absent address is substituted for this premise. |
| [ActualCutPartitionDecoder][ROW], `literalRecord`, `canonicalRow_record_iff` | A complete acquired row includes the literal exterior and every hidden comparison. The initially acquired empty-cut row is literal source information. No later complete row is silently added to (SCC.3). |
| [Native Alpha Recut Memory][NAR], §§10–16, especially Assumption 16.1 and Reuse 16.2 | The separated-age native family and initial acquisition of $a_i$. Its reference-code results concern their stated cut-row and current-port inputs, not this two-clock switch contract. |
| [Adaptive Acquired Reference Frontier][AAR], Proposition 6.3, Counterexample 8.2, Definition 10.1 | Signed calibration is reused; a free outside switch already fails; the retained $m(X_a)$ must be respected via (SCC.15). Its all-source acquisition frontier is a different resource statement. |
| [Native Cross-Epoch Relations][NCE], Theorem 5.1, Theorem 6.2, Corollary 6.3 | Common-source existence precedes uniqueness, and identified signed differences form potentials. Those graph facts are reused, not claimed as new graph algebra. |

**Mathematical citation 7.3 (literature and the remaining scope).**
Charpenay, Le Treust and Roumy, [*Optimal Zero-Error Coding for
Computing under Pairwise Shared Side Information*, arXiv:2211.03649v2][ZERO],
Definition III.1, joins two source inputs when a shared compatible
side-information value requires different target outputs. Theorem
III.4's proof outline uses proper colorings as exactly the feasible
zero-error encoders. That separation principle is
`literature-attested`; its probabilistic block model, expected coding
lengths and asymptotic rate are not the adversarial one-export
alphabet objective here.

In the present service, the source symbol is $a$, side information is
$(i,k,j,l)$ together with any old code, and the target on a compatible
pair is $l-k-(j-i)q-a_j+a_i$. Equations (SCC.9)–(SCC.10) establish
which pairs really share a chronological native realization. They
show that inside each retained fiber the characteristic graph has
exactly all edges between distinct relative profiles and none within
one profile. The finite cardinality arguments exploit that special
structure; a generic characteristic-graph quotation does not supply
it. No probability law, entropy or asymptotic equipartition is used.

The all-encoder native characterization, its fixed-minimum actual
fibers, the closed independent-box and pinned joining counts, and
their common-history recovery correspondence are `repo-derived`
ordinary mathematical deductions from these suppliers. This attribution
makes no globally original-mathematics claim. The already documented
signed calibration identity and graph-potential calculus remain
reused ingredients.

**Open problem 7.4 (extensions beyond this service).**
The exact all-encoder criterion for shorter or source-dependent epoch
windows requires its actual native conflict relation; (SCC.9) need
not be legal there. For all finite native trees, or for later services
that receive cut rows or paid current-source Reads, one must determine
their complete compatible observations before transferring any
alphabet count. Joint optimization of retention, acquisition,
materialized addresses and total or peak memory is also not supplied
by (SCC.12). These are distinct missing interfaces; none follows by
forgetting the source, history or retained-$z$ restrictions above.

[NAR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CROSS_EPOCH_RELATIONS.md
[SOURCE]: ../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[CLOCK]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[ROW]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[ZERO]: https://arxiv.org/html/2211.03649v2

## 追加锚（本行以下为增补区）

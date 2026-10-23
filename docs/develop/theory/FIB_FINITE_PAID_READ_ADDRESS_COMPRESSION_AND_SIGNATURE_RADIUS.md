# FIB finite paid reads: explicit address compression and the exact whole-signature radius

For a total hard budget of $k\ge1$ paid reads, put $M=2^k-1$.
Every admissible rule for the original stationary XOR source has a lawful
representative using only integer addresses in
$[j-2M,j+2M+1]$, with exactly the same joint law of its unchanged seed,
actual hidden endpoint, output, finite-return indicator, and paid count.
A single relabeling of a supplied finite policy tree works at every
allowed bias. The resulting radius $2M+1$ about $j$ is exactly optimal
for preserving the entire oriented whole-tree signature. That stronger
requirement has an exponential obstruction; the weaker joint-law-only
problem is left open at polynomial radius.

The quantitative component packing and this signature sharpness are the
increment relative to [Original]. General finite representative existence,
signature sufficiency, same-seed representation, compact attainment, and
the budgeted-return projection already belong to that source. The proofs
below include the interfaces needed to establish the quantitative claims
without importing a risk inequality as an address argument. All proofs
are ordinary mathematical arguments, without kernel certification.

## 1. The original law, fixed target, and paid-read semantics

**Definition 1.1 (One stationary source on all integer coordinates).** Fix
$0<p<1$, $p\ne1/2$, and $j\in\{0,1\}$. Let $\varphi$ be uniform on
$\{0,1\}$, independently of iid Bernoulli$(p)$ spins
$(S_\ell)_{\ell\in\mathbb Z}$. On the original integer emitted-bit clock,
set

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

This is exactly $J_p$ of [Original, Proposition 2.1 and (2.2)][Original]. To
identify the joint law, write $\pi_0=1-p$, $\pi_1=p$. An active
transition goes from $a_s$ to $b_t$ with probability $\pi_t$, emitting
$s\oplus t$; the next transition copies $b_t$ to $a_t$ and emits zero.
Each $a_s$ and $b_s$ has mass $\pi_s/2$. Indeed the incoming mass at
$b_t$ is $\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and copying gives that same
incoming mass at $a_t$. The realization (1.1) has these transition factors
on every finite interval, including intervals starting in either state
class. It therefore has the original ordered hidden-visible cylinder
law, with its stationary initial row. Uniform phase and reindexing of iid
spins preserve that law under an integer shift. There is no rescaling of
time or replacement of its separator coordinates.

**Definition 1.2 (The actual endpoint and its target spin).** The target
is the unchanged $H_j$ from (1.1). Write
$H_j=h_{j,\varphi,S_{q_{j,\varphi}}}$, where
$q_{j,0}=j$, $q_{j,1}=0$, and the state labels are given by the full table

$$
\begin{array}{c|c|c|c|c}
j&\phi&q_{j,\phi}&h_{j,\phi,s}&2q_{j,\phi}+\phi\\ \hline
0&0&0&a_s&0\\
0&1&0&b_s&1\\
1&0&1&b_s&2\\
1&1&0&a_s&1
\end{array}
\tag{1.2}
$$

For example, when $j=0$ and $\phi=1$, the integer $0$ is the separator
position after the active address $-1$, so its hidden state is $b_{S_0}$.
This checks the negative-index case directly. The table is precisely
[Original, (9.4)][Original]. In particular
$2q_{j,\phi}+\phi\in\{j,j+1\}$, but the endpoint itself remains $j$.

**Definition 1.3 (Admissible acquisition).** Retain [Original, Definition
9.1][Original] and [Paid-return, Definition 1.2][Paid-return]. Fix an arbitrary probability space
$(\mathsf U,\mathcal U,\nu)$ independent of the entire $J_p$ source.
All auxiliary and random public data are included in the same variable
$u$ with exactly this unchanged law. The next event is a measurable
function only of the fixed public data, $u$, and the finite ordered
acquired record

$$
r=((t_1,x_1),\ldots,(t_n,x_n))
\in(\mathbb Z\times\{0,1\})^n.
\tag{1.3}
$$

Its type is a read at an integer address, a finite return of a state in
$\mathcal A=\{a_0,a_1,b_0,b_1\}$, or indefinite internal continuation
without further read or return. A finite event may follow internal
waiting; its occurrence, kind, address or output, and finite waiting time
are measurable functions of precisely those available data. Thus timing
supplies no additional source observation. A requested address $t$ returns
only the actual $X_t$ of (1.1).

Every read occurrence costs one, including repetitions, separator zeros,
negative or positive addresses, remote addresses, and disconnected sets.
No phase, spin, half-line or tail observation, reset, law switch,
source-dependent seed or timing, moving endpoint, erased-coordinate
substitution, or extra random coin is available. A return before reading
and an output state from the wrong phase are both permitted. Null records
and the usual measurable completion versions are included.

**Definition 1.4 (Total budget and the preserved statistics).** Let $N$
count all actual reads, and let $\tau$ be the return time, with
$\tau=\infty$ on every nonreturn. These are different quantities. A
pathwise hard total budget $k\in\mathbb N_0$ means $N\le k$ on every
execution, including nonreturns and exceptional source/seed paths. It
does not merely bound costs on returning executions. Set

$$
D=\mathbf1_{\{\tau<\infty\}},\qquad
O=\begin{cases}A&D=1,\\\bot&D=0,\end{cases}
\qquad Z=(H_j,O,D,N),\qquad \bot\notin\mathcal A.
\tag{1.4}
$$

Under the cap, $Z$ has the finite alphabet

$$
\mathcal Z_k=\{(h,o,d,n):h\in\mathcal A,\
o\in\mathcal A\cup\{\bot\},\
d=\mathbf1_{\{o\ne\bot\}},\ 0\le n\le k\}.
\tag{1.5}
$$

Preservation means equality of the joint laws of $(u,Z)$ under
$J_p\otimes\nu$. It retains correlations with every measurable seed
event. A nonreturn with count $n$ remains internal nonreturn after $n$
paid calls. Neither numerical return times nor literal address names are
coordinates of the preserved law. Equality of laws does not mean equality
on each original source sample.

## 2. Finite trees and the complete oriented signature

**Lemma 2.1 (Semantic normalization with every paid depth retained).** A
pathwise-hard-total-budget-$k$ rule can be represented, at each fixed
seed, by a finite binary read tree of height at most $k$. Its leaves have
labels in $\mathcal A\cup\{\bot\}$, and their depths are the exact paid
counts, including at $\bot$ leaves. It can be capped on every formal
binary reply branch without changing $Z$ on any actual execution.

Proof. Replace every finite internal delay by one fixed finite delay,
keeping finite read events, finite returns, and indefinite internal
continuation distinct. At any record of length $k$, replace a next read
request by indefinite internal continuation without making that call.
Keep a return or an existing internal nonreturn at that boundary. These
choices depend only on the same available data as the original rule.

On an execution already satisfying $N\le k$, the boundary replacement
suppresses no actual call or return. A finite number of finite waits is
still finite, and internal nonreturn remains nonreturn. Thus its output,
return indicator, and exact paid count are unchanged; only finite timing
values can change. The modified rule also caps formal branches whose
replies are inconsistent or have source probability zero.

At fixed $u$, unfold this semantic next-event rule. A read node has its
integer address and two ordered children, for replies $0$ and $1$.
A return is a leaf with its actual state label; internal nonreturn is a
$\bot$ leaf. No read occurs at depth $k$, so there are at most

$$
1+2+\cdots+2^{k-1}=2^k-1
\tag{2.1}
$$

read nodes when $k\ge1$, and none when $k=0$. Every visited read node
costs one, even if its address repeats an earlier label. A leaf at depth
$n$ therefore has $N=n$, with no padding and no conversion of nonreturn
into return. This is the normalization used in [Original, Theorem 12.2][Original].
It is a semantic finite-tree representation, not an algorithm for deciding
whether arbitrary internal code eventually has a next event. $\square$

**Definition 2.2 (Whole-tree oriented spin-slot signature).** Fix a
normalized tree $T$ and its read-node positions $v$. Write $t_v$ for a
node's integer address and $\epsilon_v\in\{0,1\}$ for its parity. For
each $\phi\in\{0,1\}$ introduce the slots

$$
\mathcal I_\phi=\{*\}\cup
\{(v,-),(v,+):\epsilon_v=\phi\},
\tag{2.2}
$$

with actual integer indices

$$
\iota_\phi(*)=q_{j,\phi},\qquad
\iota_\phi(v,-)=\frac{t_v-\phi}{2},\qquad
\iota_\phi(v,+)=\frac{t_v-\phi}{2}+1.
\tag{2.3}
$$

The signature records the ordered binary tree shape, its leaf labels,
all node parities, and, separately in each $\mathcal I_\phi$, the
complete equivalence relation of equality of these indices. The slot
$*$ is distinguished, and the minus and plus slots are not
interchangeable. Leaf depths are retained by the shape. This is the
entire signature of [Original, Theorem 12.2][Original], over all potential nodes
at once, including mutually incompatible reply branches. It contains no
relation between slots from different phase alternatives.

**Lemma 2.3 (Finite-product sufficiency and adaptive execution).** Two
integer address assignments on the same tree having the signature of
Definition 2.2 have the same $Z$-law for every allowed $p$.

Proof. Fix a phase $\phi$. The distinct indices in (2.3) form a finite
set $V$. If $s:V\to\{0,1\}$ is a spin assignment, its probability under
the actual source conditional on that phase is

$$
\prod_{z\in V}p^{s(z)}(1-p)^{1-s(z)}.
\tag{2.4}
$$

Equal signatures identify these vertices bijectively by their slots,
sending the target index to the target index. Transporting $s$ along
this bijection gives the identical product mass. The target state is
$h_{j,\phi,s(q_{j,\phi})}$. Each node of parity $\phi$ has potential
reply equal to the XOR of its minus and plus spins, and each other node
has potential reply zero. Consequently the complete node-indexed arrays
and the target have the same conditional law:

$$
\left(H_j,(X_{t_v})_{v\text{ a read node}}\right).
\tag{2.5}
$$

This compares finite-coordinate distributions of the same $J_p$; it
grants the protocol no access to the spins or to potential replies at
unvisited nodes. Average the two conditional laws using their original
weights $1/2,1/2$. Execution is a deterministic function of this whole
array: use the potential reply at each visited node to select its child.
The reached leaf label and depth give $(O,D,N)$, with $D=0$ and $O=\bot$
only at a $\bot$ leaf and with its actual depth still giving $N$.
Applying that function to the equal array laws proves the assertion.
The argument is a product identity for every $p$, not a fit to a chosen
numerical bias. It restates the sufficiency interface in [Original,
Theorem 12.2][Original]. $\square$

## 3. Quantitative packing of actual integer-line components

**Lemma 3.1 (Two capacities for detached components).** Suppose a finite
collection of $C$ nonempty paths has positive integer edge lengths
$\ell_1,\ldots,\ell_C$ and total edge count $d$. Its vertex sizes
$s_i=\ell_i+1$ can be split into two groups with respective total sizes

$$
x\le d,\qquad y\le d+1.
\tag{3.1}
$$

The split can be specified deterministically from any fixed ordering.

Proof. If $C=0$, then $d=0$ and use two empty groups. If $C=1$, put the
only component, of size $d+1$, in the second group. Suppose $C\ge2$.
The other $C-1$ paths each have at least one edge, so for every $i$,

$$
s_i\le d-(C-1)+1=d-C+2.
\tag{3.2}
$$

In the fixed order, take the shortest initial segment with size sum
$x\ge C-1$. It exists since the full sum is $d+C$. Before its final
term the integer sum is at most $C-2$, so

$$
C-1\le x\le(C-2)+(d-C+2)=d.
\tag{3.3}
$$

The remaining size is $y=d+C-x\le d+1$. This proves both capacities
by a finite specified split. $\square$

**Lemma 3.2 (Packing with the actual target fixed).** Let $E\subset\mathbb Z$
be a finite set of $m$ distinct edge left endpoints, and
adjoin a distinguished vertex $q\in\mathbb Z$ to the graph with edges
$\{e,e+1\}$, $e\in E$. There is an injective map $f$ from its occupied
vertices into $\mathbb Z$ which fixes $q$, translates each component
without reversing it, and sends every queried edge to an edge whose left
endpoint belongs to $[q-m,q+m]\cap\mathbb Z$. Thus it preserves exactly
all equalities of target and oriented edge slots, including repeated
occurrences of an edge.

Proof. Each component is a finite integer interval with all consecutive
edges inside it present: a missing edge separates its two sides on the
integer line. The component of $q$ is
$[q-l,q+r]\cap\mathbb Z$, with $a=l+r$ edges; $l=r=0$ is allowed.
Keep this entire component fixed. Every other component has positive
edge length $\ell_i$ and vertex size $s_i=\ell_i+1$. Put

$$
d=\sum_{i=1}^C\ell_i=m-a.
\tag{3.4}
$$

Order these detached components by their least original vertex. Lemma
3.1 gives a first group of total size $x\le d$ and a second group of
total size $y\le d+1$. Place the first group, in that order, in the
consecutive vertex blocks occupying
$[q-l-x,q-l-1]\cap\mathbb Z$, and the second group in the blocks
occupying $[q+r+1,q+r+y]\cap\mathbb Z$. Empty groups occupy nothing.
For a component with least original vertex $a_i$ and chosen new least
vertex $b_i$, define $f(z)=z-a_i+b_i$ on that component. The new least
vertices are determined by the indicated starting index plus the sum of
preceding sizes in the same group. This completely specifies $f$.

Each component is translated in its original orientation. Its internal
vertex equalities and every edge's ordered pair of endpoints are
preserved. Different blocks, including the fixed target component, are
disjoint, so $f$ is injective and introduces no equality between
originally different indices. Two blocks may have nearest vertices
one unit apart. The edge between those blocks is not a mapped queried
edge; adjacency alone imposes no constraint on distinct iid spins.
Thus this placement preserves exactly the slot equivalence relation,
without needing to preserve unqueried gaps. Every occurrence of a
repeated edge uses the same translated pair of vertices, while remaining
a separate paid node.

The smallest occupied index satisfies

$$
q-l-x\ge q-l-d\ge q-m,
\tag{3.5}
$$

because $l+d=m-r\le m$. The largest satisfies

$$
q+r+y\le q+r+d+1\le q+m+1,
\tag{3.6}
$$

because $r+d=m-l\le m$. A mapped queried edge has consecutive endpoints
in this occupied set; its left endpoint is consequently at least $q-m$
and at most $q+m$. If $m=0$, only the distinguished vertex is present,
and there is no queried edge to bound. $\square$

## 4. An explicit window with exactly the same given-seed joint law

**Theorem 4.1 (Uniform finite-paid-read address compression).** For
$k\ge1$, define

$$
M=2^k-1,\qquad
W_{k,j}=[j-2M,j+2M+1]\cap\mathbb Z,\qquad
R_k=2M+1=2^{k+1}-1.
\tag{4.1}
$$

Every rule of Definition 1.3 with pathwise hard total budget $k$ has a
lawful representative on the same unchanged independent seed space
whose read addresses all belong to $W_{k,j}$ and whose cap holds on
every formal reply branch. Its joint law of $(u,H_j,O,D,N)$ is exactly
the original one. For a supplied normalized finite integer-labeled tree
of height at most $k$, one relabeling independent of $p$ preserves its entire Definition 2.2
signature, ordered shape, leaf labels, and all paid terminal depths;
its law identity holds for every allowed $p$ simultaneously. For $k=0$
the address set is empty.

Proof. First fix a supplied normalized tree $T$. For each phase label
$\phi$, collect the distinct active edge left endpoints

$$
E_\phi=\{(t_v-\phi)/2:\epsilon_v=\phi\},\qquad
m_\phi=|E_\phi|\le M,
\tag{4.2}
$$

and adjoin the actual target index $q_{j,\phi}$. This uses all nodes of
that parity in the whole tree. Apply Lemma 3.2 to obtain $f_\phi$ fixing
that target, and let $e'_v=f_\phi((t_v-\phi)/2)$ for a node of parity
$\phi$. Define its one new actual address by

$$
t'_v=2e'_v+\epsilon_v.
\tag{4.3}
$$

This is one assignment of integers to all nodes. It does not ask the
runtime protocol for the hidden phase. In actual conditional phase
$\phi$, nodes of parity $\phi$ are active and have exactly the packed
slot relation, while all other nodes remain compulsory zero separators.
Each node has an active-edge constraint in only its own parity. There
is no cross-phase slot relation in Definition 2.2, because the two phases
are mutually exclusive alternatives in the source mixture. In particular,
adjacent even and odd original addresses supply no omitted conditional
shared-spin constraint: in each fixed phase one of those addresses is
inactive. Thus the two packings are simultaneously realized by (4.3),
with exactly the full original signature in each phase.

Lemma 3.2 gives

$$
2q_{j,\phi}+\phi-2m_\phi
\le t'_v\le
2q_{j,\phi}+\phi+2m_\phi
\qquad(\epsilon_v=\phi).
\tag{4.4}
$$

The actual target table (1.2), rather than a shifted target, puts the
base $2q_{j,\phi}+\phi$ at $j$ or $j+1$. Since $m_\phi\le M$, (4.4)
lies inside $W_{k,j}$; hence $|t'_v-j|\le R_k$. Negative and remote
original addresses, incidence on either side of the target, disconnected
components, overlaps, and repeated reads are all included in the graph
and its injective map. Lemma 2.3 now proves equality of the complete
finite potential-reply law and then of $Z$. The tree shape and leaf
labels are unchanged, so terminal paid depth is retained also on
nonreturn. The packing uses integer geometry and $j$, without using $p$.
This proves the fixed-tree assertion for all allowed $p$ with the same
relabeling.

It remains to construct one measurable rule for the arbitrary given
seed, rather than choosing unrelated deterministic laws. Normalize the
original rule by Lemma 2.1 and denote its fixed-seed tree by $T(u)$. The
space $\mathcal T_k$ of all such trees is countable: there are finitely
many binary shapes through depth $k$, finitely many leaf-label patterns,
and a finite tuple of integer labels for each shape. Give it the discrete
sigma-algebra.

The map $u\mapsto T(u)$ is measurable. For each potential node position,
its previous acquired record has countable range. If that record is
$r(u)$ and $F(u,r)$ is a measurable next-event condition, the event in
question is the countable union

$$
\bigcup_r\bigl(\{u:r(u)=r\}\cap\{u:F(u,r)\}\bigr).
\tag{4.5}
$$

Thus evaluation at a varying record is measurable. Induction through the
finitely many possible node positions proves the assertion; a position
absent because of an earlier leaf can be assigned a fixed dummy label
for this induction. Finite event type and indefinite continuation are
already measurably distinguished by the contract. No decision procedure
for internal divergence is being presumed.

Use exactly the ordering, split, and placement in Lemmas 3.1--3.2.
They make the relabeling a specified map $C_j:\mathcal T_k\to\mathcal T_k$.
Any map between these countable discrete tree spaces is
measurable, so $u\mapsto C_j(T(u))$ is measurable. At seed $u$, run that
compressed tree using its actual source replies. On acquired records
inconsistent with it, choose internal nonreturn to make the next-event
rule total. This is a measurable rule: partition the seed space into
its countably many selected-tree cells, and on each cell test the finite
record against that fixed tree. All its reads are actual addresses from
$W_{k,j}$ and every formal branch is capped. The initial tree selection
uses only $u$ and public data, with no added random variable or source
access.

For a fixed tree $T$ let

$$
a_{T,p}(z)=J_p(Z^T=z),\qquad z\in\mathcal Z_k.
\tag{4.6}
$$

The finite-product argument proves $a_{T,p}(z)=a_{C_j(T),p}(z)$ for each
$T$ and $z$. Independence of the source and the original seed, followed
by product-measure integration, therefore gives for every
$B\in\mathcal U$,

$$
\begin{aligned}
\mathbb P_p(u\in B,Z^{\mathrm{original}}=z)
&=\int_B a_{T(u),p}(z)\,d\nu(u)\\
&=\int_B a_{C_j(T(u)),p}(z)\,d\nu(u)\\
&=\mathbb P_p(u\in B,Z^{\mathrm{compressed}}=z).
\end{aligned}
\tag{4.7}
$$

In the first equality normalization retains $Z$ for the pathwise-capped
input. These are integrations of source sections, not regular conditional
probabilities given singleton seeds. Since $\mathcal Z_k$ is finite,
equality on all such rectangles is exactly equality of the full joint
laws on $\mathsf U\times\mathcal Z_k$. This works for arbitrary atomic
or nonstandard seed spaces. For the permitted completion versions,
choose measurable versions together over the countably many acquired
records; null changes do not affect the integrated identities. The
constructed tree rule still has its formal cap on every branch.

When $k=0$, normalization has no read nodes. Its seed-dependent return
state or internal nonreturn can be kept directly with the same joint
law, and it uses no address. $\square$

**Boundary 4.2 (Public bias and the optional almost-sure total cap).** The
relabeling of a fixed supplied tree is independent of $p$. If a rule uses
$p$ as fixed public data, Theorem 4.1 applies to its tree separately at
each fixed $p$; it does not assert that the tree selection is independent
of $p$ or impose a joint measurability requirement in $p$.

The same construction also gives an optional variant for an input with
$\mathbb P_p(N\le k)=1$ at a specified allowed $p$. Indeed normalization
changes its $Z$ only on $\{N>k\}$, a product-null event. The normalized
tree map is measurable, its compression is formally capped, and product
integration in (4.7) preserves the original joint law. This is an
almost-sure input hypothesis and an everywhere-capped output, rather
than a claim that those requirements coincide for individual rules.

A budget only on returns cannot replace either total-cap hypothesis.
For example, a rule can make exactly $k+1$ repeated actual reads and
then continue internally forever. It has no returning path, so satisfies
any bound restricted to returns, but its $N=k+1$ law cannot be preserved
by a total-cap-$k$ representative. More generally, the truncation used in
[Original, Theorem 14.1][Original] preserves its stated budgeted-return projection;
it need not preserve an unrestricted rule's whole law or its costs above
$k$. No such stronger conclusion is used in Theorem 4.1.

## 5. Exact universal radius for the whole signature

**Definition 5.1 (The stronger radius objective).** For $k\ge1$, let
$\rho_{k,j}^{\mathrm{sig}}$ be the least nonnegative integer $R$ such
that every normalized integer-labeled tree of height at most $k$ has an
address assignment with all addresses satisfying $|t-j|\le R$ and with
exactly the same Definition 2.2 signature. The original target index,
ordered reply branches, node-slot positions and orientations, parities,
leaf labels, and depths are retained. This is a requirement on the
whole tree, beyond equality of its executed $Z$-law.

**Theorem 5.2 (Exact signature radius and a lawful witness).** For every
$k\ge1$ and either $j\in\{0,1\}$,

$$
\rho_{k,j}^{\mathrm{sig}}=2^{k+1}-1=2M+1,
\qquad M=2^k-1.
\tag{5.1}
$$

The lower-bound witness is a lawful deterministic protocol making
exactly $k$ paid calls on every branch. Its joint-law-only objective
nevertheless has a radius-zero realization.

Proof. Theorem 4.1 gives the upper bound for every tree. For the lower
bound, take the complete binary read tree of depth $k$, with its $M$
read nodes enumerated $v_0,\ldots,v_{M-1}$ in any fixed order. Set

$$
\phi_*=1-j,\qquad q=q_{j,\phi_*}=j,
\qquad 2q+\phi_*=j+1,
\tag{5.2}
$$

and give node $v_i$ the actual integer address

$$
t_i=2(q+1+i)+\phi_*,\qquad 0\le i<M.
\tag{5.3}
$$

In phase $\phi_*$, the whole-tree queried edges form one path on the
vertices $q+1,\ldots,q+M+1$, and the distinguished target $q$ is isolated.
Every node is a separator in the other phase. Label every leaf by the
finite return state $a_0$. This is a lawful fixed tree on actual integer
addresses, ignoring the seed and making exactly $k$ paid calls on every
formal branch. A one at a separator can occur on a formal branch only;
the rule is still defined there.

Consider any assignment preserving its entire signature. Parities are
fixed, so write $b_i$ for the active edge left endpoint of $v_i$ in
phase $\phi_*$. For each $0\le i<M-1$, the original signature identifies
the plus slot of $v_i$ with the minus slot of $v_{i+1}$. Preservation
therefore forces

$$
b_i+1=b_{i+1}.
\tag{5.4}
$$

The occupied vertices are consequently the complete consecutive interval
$[b_0,b_0+M]\cap\mathbb Z$. The distinguished target was separate from
every one of these slots, so $q$ cannot belong to that interval. Hence

$$
b_0\ge q+1\qquad\text{or}\qquad b_0+M\le q-1.
\tag{5.5}
$$

In the first case the last node address is at least

$$
2(b_0+M-1)+\phi_*\ge2(q+M)+\phi_*=j+2M+1.
\tag{5.6}
$$

In the second case the first node address is at most

$$
2b_0+\phi_*\le2(q-M-1)+\phi_*=j-2M-1.
\tag{5.7}
$$

Thus some address has distance at least $2M+1$ from the unchanged $j$.
When $M=1$, there is no equation (5.4) to impose, but the single edge's
two vertices still form the stated interval and (5.5)--(5.7) still apply.
The oriented slots force (5.4); reflecting an edge by interchanging its
slots does not preserve the required signature. Translating the target
with the path is also forbidden. Formula (5.2) checks both endpoints:
$j=0$ uses phase $1$ and target spin $S_0$, while $j=1$ uses phase $0$
and target spin $S_1$. This proves the lower bound and hence (5.1).

Finally this witness always has $O=a_0$, $D=1$, and $N=k$. Its joint
law of $(u,H_j,O,D,N)$ can instead be realized by reading the actual
address $j$ exactly $k$ times, paying for every occurrence, ignoring all
replies, and returning $a_0$. This replacement uses radius zero, keeps
the original $J_p$ and actual $H_j$, and leaves those three statistics
constant with their same values, jointly with every unchanged independent
seed. It need not have the witness signature. The example establishes
no positive lower bound for the joint-law-only objective. $\square$

**Open question 5.3 (Polynomial radius for law alone).** Theorem 4.1
gives an exponential universal window for preserving $(u,Z)$.
Theorem 5.2 rules out a polynomial-in-$k$ universal radius only when
the complete oriented whole-tree signature must be preserved. That
signature retains potential-reply relations even between nodes on
incompatible branches; equality of the executed joint law can discard
those relations. Whether every total-budget-$k$ rule admits an exact
joint-law-preserving representative in a polynomial-in-$k$ radius, or
whether this weaker objective has a superpolynomial obstruction, remains
unresolved here. The complete tree has $M$ potential read nodes, although
an execution has only $k$ paid calls; those two counts are not
interchangeable.

## 6. Effectivity, scope, and attribution

**Boundary 6.1 (What the construction computes).** Given a complete
finite integer-labeled tree with its return and divergence terminals
already specified, Lemmas 3.1--3.2 and (4.2)--(4.3) give a finite explicit
relabeling: find the components, keep the target component fixed, split
the detached sizes in the specified order, translate the blocks, and
convert their edge indices to actual addresses. No value of $p$ is
needed for that operation. It constructs one simultaneous two-phase
address assignment, rather than separate runtime phase-conditioned
protocols.

The reduction from an arbitrary measurable next-event rule to $T(u)$
is semantic. Neither unfolding arbitrary code, deciding internal
divergence, recognizing an arbitrary measurable seed cell effectively,
nor obtaining an algorithm on arbitrary presentations of seed spaces
follows. The countable-tree integration establishes measurable existence
on the given space. It changes neither the seed law nor the permitted
acquisition operations. It does not assert equality of original and
compressed replies on a fixed realized spin sequence, numerical timing
preservation, a minimal representative dictionary, an optimal adaptive
rule, or a numerical larger-budget risk frontier.

**Attribution 6.2 (Prior interfaces and the quantitative increment).**
The owning sources and their exact roles are as follows.

| Source | Reused content and boundary |
| --- | --- |
| [Original, Proposition 2.1, (2.2), Definition 9.1 and (9.4)][Original] | The one stationary law, paid-read contract, original clock, and actual target table. |
| [Original, Theorems 12.2--12.3][Original] | Complete whole-tree slot signature, its law sufficiency, general finite representative existence, and measurable same-given-seed representation. The interfaces in Section 2 and the measurable lift in Section 4 are included with their ordinary arguments; these existence conclusions are not counted as new. |
| [Original, Sections 13--14][Original] | Exact seed-partition image, compact attainment, and the budgeted-return projection. These remain existing conclusions; no new compactness or numerical optimum is claimed. |
| [Paid-return, Definitions 1.2--1.3 and Section 6][Paid-return] | The unchanged acquisition contract, distinction between total cost and return-restricted quantities, and resource boundaries. Its risk bounds supply no address-packing proof. |
| Lemmas 3.1--3.2 and the quantitative part of Theorem 4.1 | `repo-derived`: the component capacities, injective packing fixing the actual target, and the explicit bias-independent window $W_{k,j}$. |
| Theorem 5.2 | `repo-derived`: the exact universal whole-signature radius and its law-only limitation, with the explicit lawful witness. |

The relative mathematical increment is precisely quantitative packing
and signature sharpness. Finite iid products, elementary path geometry,
and product-measure integration retain their usual mathematical meaning.
This comparison is with the supplied owning sources; it asserts no
external-literature absence or global priority.

**Boundary 6.3 (Unsettled and excluded conclusions).** The claims retain
the specified biased interior parameter range; they add neither fairness
nor endpoint parameters to the contract. They concern finite total hard
budgets, with the explicitly stated optional almost-sure variant. They
provide no unbounded-history, expected-cost-only, or general numeric risk
result and do not settle [Original, Open Problem 6.4][Original]. Internal work,
address encoding, persistent state, physical storage, finite precision,
and memory are separate resources, with no bound asserted here. There
is no empirical learning, neural, or whole-domain attainment conclusion.
The proofs use ordinary finite probability and geometry, with no
mathematical execution or formal certification as evidence.

[Original]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[Paid-return]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md

## 追加锚（本行以下为增补区）

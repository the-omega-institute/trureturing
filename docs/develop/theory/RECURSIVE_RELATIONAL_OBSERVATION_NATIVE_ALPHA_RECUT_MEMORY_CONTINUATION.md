# Native alpha recut memory continuation: exact fixed-reference reading

## 1. A fixed acquired reference and the entire two-slot input

**Assumption 1.1 (causal reference, whole rows and stationary access).**
Use the native source and complete-row semantics of [NAR, Definitions
1.1--1.2][NAR], and the acquire, export and discard conditions of [NAR,
Assumptions 11.1 and 13.1][NAR]. Specialize [NAR, Definition 11.4][NAR] to $P=\varnothing$, $D=1$, public
$H\ge0$, $q=H+1$, and the actual independent-age sources

$$
X_{a_0,a_1}=\langle T_{a_0},T_{q+a_1}\rangle,
\qquad (a_0,a_1)\in\{0,\ldots,H\}^2,
\qquad T_n=\rho^n\alpha.
\tag{NARC.1.1}
$$

The original offsets are zero and $q$; they are not renumbered after a cut.
The initial complete $P$ row is genuinely acquired. From its literal
left subtree the encoder computes and retains exactly $E=a_0$, before
the future cut and lag are known, and discards the old row. Every other
source-bearing datum is inaccessible after that discard. The supplied
right clock $c(T_n)=n$ in [NAR, (NAR.10.11) and (NAR.13.9)][NAR] computes this code
from acquired data; it is not an additional source port.

Fix publicly $\lambda_0\in\{0,1\}$, requiring $\ell\ge\lambda_0$;
these are respectively nonnegative and strictly positive lags. The later
complete row is genuinely acquired from this same fixed source after
its own $\ell$ homomorphic substitutions. Permitted future cuts are
$\varnothing,\{L\},\{R\}$, precisely the noncovering depth-one cuts.
After this capture, a deterministic decoder may query any finite literal
word on the stationary current tree. The new port has no updates,
subtree, age, origin or epoch oracle. Every submitted word costs one
chronological call, even the empty word. The peak is the maximum length
of a submitted whole-tree word, with value zero if none is submitted.
Correctness is required on every compatible history, with no source
distribution. Acquisition, parsing, local work, address construction,
retained representation, workspace and physical time are separate
quantities.

**Theorem 1.2 (the exact complete-row and code fiber).** Fix a retained
$a_0\in[0,H]$ and a promised later input with cut $Q=\{L\}$. Its entire
row has the form

$$
Y_z=\bigl(\langle\square_L,T_{q+z}\rangle,\{\{L\}\}\bigr),
\qquad z\ge\lambda_0.
\tag{NARC.1.2}
$$

The reached-hole set is $\{L\}$ and its partition is the displayed
singleton. Put $b=\max(\lambda_0,z-H)$. The compatible lags and hidden
current ages are exactly

$$
\ell\in[b,z],\qquad
n_0=a_0+\ell\in I_0=[a_0+b,a_0+z],\qquad
N=|I_0|=z-b+1\le q.
\tag{NARC.1.3}
$$

Every member of this fiber is realized by its own fixed original
$X_{a_0,z-\ell}$ and that original's pure-$\rho$ continuation. The
equalities refer to the entire row, including all exterior labels and
brackets, cut guards and hidden partition.

**Proof.** Homomorphism preserves the root pair and gives the current tree
$\langle T_{a_0+\ell},T_{q+a_1+\ell}\rangle$. Both slot addresses
remain reached, including when the left filling is $\alpha$. Replacing
the entire left subtree gives exactly the exterior in (NARC.1.2).
There is only one hidden hole; its partition is $\{\{L\}\}$ whatever
the filling. No hidden-visible comparison is supplied by [NAR, Definition 1.2][NAR].
The complete literal right tree determines $z=a_1+\ell$ by its supplied
clock, and any history yielding this row must have this same $z$ because
the $T_n$ are distinct. Thus $0\le a_1=z-\ell\le H$ and the lag
condition give precisely $b\le\ell\le z$.

Conversely, for each integer $\ell\in[b,z]$, set $a_1=z-\ell$.
The inequalities give $0\le a_1\le H$ and $\ell\ge\lambda_0$.
This legal fixed original has current tree
$\langle T_{a_0+\ell},T_{q+z}\rangle$ after its own $\ell$ updates.
Its retained code is the same $a_0$. Its whole right exterior, reached
left guard and singleton partition give exactly $Y_z$. Each alternative
has one original throughout its continuation and reads; the alternatives
are not segments of a spliced history. This proves both fiber directions.
Finally $b\le z$ on a promised input and $b\ge z-H$, so
$1\le z-b+1\le H+1$. $\square$

## 2. Exact conditional calls and whole-tree address peak

**Theorem 2.1 (all-address reduction and jointly attained prices).**
Under Assumption 1.1, fix $(a_0,Q=\{L\},Y_z)$ and the interval $I_0$
of Theorem 1.2. Write $K(l,u)$ and $M(l,u)$ for the stationary native
interval prices of [AOF, Definition 8.1 and Theorems 8.3, 9.2][AOF].
The exact conditional minima over all deterministic whole-tree decoders
are

$$
\begin{aligned}
\mathsf{Calls}(a_0,Y_z)&=K(a_0+b,a_0+z),\\
\mathsf{Peak}(a_0,Y_z)&=
\begin{cases}
0,&N=1,\\
1+\left\lfloor\dfrac{a_0+z-1}{2}\right\rfloor,&N\ge2.
\end{cases}
\end{aligned}
\tag{NARC.2.1}
$$

One finite literal decoder attains both minima. Its call price is
$K_0(N)$ when $a_0+b=0$ and $K_+(N)$ otherwise, with both zero at
$N=1$. If $Q=\varnothing$ or $Q=\{R\}$, both new prices are zero.
The conditional worst cases are over all histories with this same code
and entire later input, rather than over an already known actual lag.

**Proof.** On the exact fiber, every whole-tree query is one of
$\varepsilon,Lp,Rp$. The root reply is constantly branch. At $Rp$ the
reply is exactly the constructor read of $p$ in the supplied literal
$T_{q+z}$, including failure at a leaf, and is fixed across the fiber.
At $Lp$ it is

$$
r_{\langle T_{a_0+\ell},T_{q+z}\rangle}(Lp)
=r_{T_{a_0+\ell}}(p).
\tag{NARC.2.2}
$$

Hence every potentially informative query is left-prefixed, although
some left-prefixed queries are themselves constant. Simulate any proposed
whole-tree decoder's root and right-cone queries locally from the common
input, and replace each $Lp$ query by the one paid relative query $p$.
For each $n_0\in I_0$, Theorem 1.2 supplies an actual history, so this
simulation preserves the proposed decoder's replies, choices and lag
output. Adding $a_0$ to that output gives an interval reader for $n_0$,
with no more calls. Pointwise finite termination transfers. This proves
the call lower bound against all whole-tree addresses.

If $N\ge2$, a decoder with no nonempty informative address cannot
distinguish its compatible lags. In particular a whole-word cap of zero
is impossible. For a cap $B\ge1$, the same simulation submits only
suffixes of length at most $B-1$. The interval peak lower bound therefore
forces $B-1\ge M(I_0)$. This also covers $M(I_0)=0$, where at least
the one-letter slot address must be submitted. Root and right queries
cannot relax the bound because their replies are fixed.

For the upper bounds, use the single AOF reader attaining both interval
minima and submit each of its actual literal words $p$ as $Lp$. Its
replies are (NARC.2.2), the current source remains stationary, and the
answer $n_0$ gives $\ell=n_0-a_0$. A relative root query costs one paid
whole-tree call at $L$; it has whole-word length one. The prefix adds
exactly one letter to the peak of a nontrivial reader. For $N=1$ the
unique lag is already determined, and no word is submitted.

For the other permitted cuts, the entire acquired left subtree is
visible. Its clock is $a_0+\ell$, whose difference from the retained
$a_0$ is the lag. This calculation uses acquired literal data and no
new source call. The initial full row remains discarded. $\square$

## 3. Lag conventions and the fixed-encoder boundary

**Theorem 3.1 (worst calls for the retained left reference).** For the
fixed encoder $E=a_0$ of Assumption 1.1, the exact worst fresh-call price
over all promised inputs and permitted depth-one cuts is

$$
\begin{cases}
K_+(q)=\min\{k\ge0:q\le3\cdot2^k-2\},&\lambda_0=1,\\
K_0(q)=\min\{k\ge0:q\le A_k\},&\lambda_0=0,
\end{cases}
\qquad A_0=1,\quad A_k=3\cdot2^k-3\ (k\ge1).
\tag{NARC.3.1}
$$

Both prices are zero for $q=1$. At $H=3,q=4$ they are respectively one
and two, with a jointly optimal whole-word peak two on the attaining
inputs below. For $q\ge2$, the required conditional peak is unbounded
over legal lag inputs despite the uniform finite call bound.

**Proof.** Theorem 1.2 gives at most $q$ consecutive hidden ages.
Positive lags force a positive lower endpoint. In the nonnegative
contract, a positive interval is no harder in calls than a zero-origin
interval of the same size, since $A_k\le C_k$ at every budget. AOF
Theorem 8.3 and Theorem 2.1 give the asserted upper bounds. They are
attained with $a_0=0,z=H+1$ for positive lags, yielding $I_0=[1,q]$,
and $a_0=0,z=H$ for nonnegative lags, yielding $I_0=[0,H]$.
Theorem 1.2 realizes every candidate as a complete-input alternative,
so the interval lower bounds apply. Cuts displaying the left slot add
no larger price. At $H=0$ every interval is a singleton.

For $H=3$, the nonnegative attaining input is
$Y_3=(\langle\square_L,T_7\rangle,\{\{L\}\})$, with originals
$X_{0,3-\ell}$ for $\ell=0,1,2,3$. Read physical $L$: alpha and beta
identify lags zero and one; on branch read physical $LR$, whose replies
alpha and beta identify two and three. The zero-origin obstruction
precludes one call. The positive attaining input is
$Y_4=(\langle\square_L,T_8\rangle,\{\{L\}\})$, with originals
$X_{0,4-\ell}$ for $\ell=1,2,3,4$. One physical $LR$ returns absent,
alpha, beta and branch respectively. Both have the peak two of
(NARC.2.1); the source-relative suffix in this latter example is $R$.

For unbounded peaks, keep $a_0=0$ and let $z\ge H+\lambda_0$ increase.
Then $I_0=[z-H,z]$ has size $q\ge2$ and its exact peak in (NARC.2.1)
diverges. Each such row is a finite promised acquired input. This is an
address-length statement, not a physical-time or workspace law. $\square$

**Theorem 3.2 (a different retained coordinate changes the call price).**
At $H=3,q=4$, with the same source, acquisition, discard, nonnegative-lag
and future-cut conditions, the causal encoder $E'=a_1$ has exact worst
fresh-call price one. On one attaining complete-input fiber its exact
whole-word peak is four. Thus the two-call price for $E=a_0$ is qualified
by that fixed encoder; it is not a minimum over all four-value encoders.

**Proof.** Compute $a_1=c(T_{4+a_1})-4$ from the genuinely acquired
original right subtree before the future choice. If the later right
slot is visible, its normalized clock $z_1=a_1+\ell$ and $E'$ give
$\ell$ without a new query. If only the left slot is visible, let
$z_0=a_0+\ell$ be its acquired clock. For fixed $a_1,z_0$, put
$b'=\max(0,z_0-3)$. Exactly the lags $[b',z_0]$ are realized by
fixed originals $X_{z_0-\ell,a_1}$, each with current tree
$\langle T_{z_0},T_{4+a_1+\ell}\rangle$. Their entire row is
$(\langle T_{z_0},\square_R\rangle,\{\{R\}\})$; the right guard
is reached and the partition is singleton. The hidden right-age interval
is $[4+a_1+b',4+a_1+z_0]$, has at most four members, and has positive
lower endpoint. If it is nontrivial, one actual $P_{l+1}$ query at the
right slot, where $l=4+a_1+b'$, separates its members: the replies at
$l,l+1,l+2,l+3$ are absent, alpha, beta and branch. Use the supplied
shortest literal representative; singleton intervals require no query.
The empty cut displays both slots. This gives a uniform one-call bound.

For attainment, fix $a_1=0,z_0=3$ and the entire later row
$(\langle T_3,\square_R\rangle,\{\{R\}\})$. The four fixed
originals $X_{3-\ell,0}$ at lags $\ell=0,1,2,3$ all give this code
and row; their current right ages are $4,5,6,7$. Zero calls cannot
distinguish the lags. Physical $RLRR$ reads relative $LRR=P_5$ and
gives absent, alpha, beta and branch, attaining one call and peak four.
For the exact peak lower bound, root and left-cone queries are fixed
by this acquired input; right-prefixed queries reduce to the interval
$[4,7]$. The all-address argument of Theorem 2.1 with left and right
exchanged gives $1+M(4,7)=4$. The encoder's call improvement and this
fiber's deeper address cost are separate coordinates, not a global
Pareto-frontier assertion. $\square$

**Mathematical citation 3.3 (scope of the correspondence).** The source,
complete-row syntax, clock, causal retention and original offsets are
the suppliers in [NAR, Definitions 1.1--1.2 and §§11, 13][NAR]. The resource proof
is [AOF §§8--9][AOF], whose stationary interval contract requires neither
an encoder nor a future cut. The complete-input realization and
all-address lower-bound transfer here are `repo-derived` deductions.
They fix one retained coordinate and a two-slot source promise; they do
not assert a retained-alphabet minimum or arbitrary-encoder/menu optimum.
Additional hidden slots can give additional query information, so a
many-slot lower bound would require its own entire-fiber correspondence.

For the common-side-information obstruction, compare N. Charpenay,
M. Le Treust and A. Roumy, *Optimal Zero-Error Coding for Computing under
Pairwise Shared Side Information*, [arXiv:2211.03649v2, Definitions II.1
and IV.5](https://arxiv.org/html/2211.03649v2). Their adjacency requires
different target values at a common compatible side-information value.
That is the role played here by the same code and entire later row.
Their expected prefix-code length per i.i.d. block and asymptotic rate
are different objectives and provide no native call or address formula.
These bounded mathematical comparisons make no worldwide priority claim.

[NAR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[AOF]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md

## 追加锚（本行以下为增补区）

## 4. Counted internal Moore recovery at one fixed acquired input

**Assumption 4.1 (conditional installed table and complete entry).**
Keep Assumption 1.1, including its fixed causal encoder $E=a_0$, actual
acquisition and export before the future cut, discard of the original
row, same-source pure-$\rho$ continuation, genuine acquisition of the
entire later row and lawful stationary fresh-Read access. Fix one
promised acquired input $(a_0,Q=\{L\},Y_z)$, with the whole $Y_z$ of
(NARC.1.2), not merely its scalar clock. By Theorem 1.2 its complete
compatible fiber has

$$
I_0=[l,u]=[a_0+b,a_0+z],\qquad
b=\max(\lambda_0,z-H),\qquad N=z-b+1.
\tag{NARC.4.1}
$$

Use the finite Moore restriction of [AOF, Definition 10.1][AOF], with
literal whole-tree addresses and fixed complete lag outputs in
$\mathbb N$. A table has one common initial state on this conditional
fiber, one fully materialized address per running state, a total
four-reply transition row, and a fixed numeric output per halt. All
installed running and halting states count. After entry its current
state is its entire changing accessible configuration; there is no
additional retained $a_0,z$, row, reply, history, address or output
register and no external decoder or mutable table selector.

The public parameters are the declared source family, $H,\lambda_0$
and cut. The fixed code value $a_0$ and entire $Y_z$ are genuinely
acquired source-bearing compilation inputs, common only within this
conditional fiber. A separately supplied finite computation may use
them to determine $b,I_0$, literal table entries and complete output
constants, followed by installation and a complete entry cut. It
cannot use the unknown actual lag to select a table within the fiber.
The resulting one table must work for every compatible history of
Theorem 1.2. Input capture, export, access, representation, parsing,
table construction and installation are separate services and costs;
none is a free fresh-source or current-age port. Immutable installed
table and complete-output storage remain separate from state count.
This is a family indexed by fixed acquired inputs, not a declaration
that one fixed finite table handles every later input without change.

**Theorem 4.2 (exact conditional Moore states and common attainment).**
For Assumption 4.1 let $J(l,u)$ be (AOF.31). The exact minimum running
and total state counts over arbitrary whole-tree literal controllers
are respectively

$$
J(l,u),\qquad N+J(l,u).
\tag{NARC.4.2}
$$

One such controller has exactly those counts, exactly $N$ fixed-output
halts, the minimum fresh-call price $K(l,u)$, and the minimum physical
whole-word peak

$$
\begin{cases}
0,&N=1,\\
1+M(l,u)=1+\left\lfloor\dfrac{u-1}{2}\right\rfloor,&N\ge2.
\end{cases}
\tag{NARC.4.3}
$$

These are the same conditional call and peak minima as Theorem 2.1,
now simultaneously attained with the minimum counted state set and
no external mutable input or decoding field. For $Q=\varnothing$ or
$Q=\{R\}$, each fixed promised complete input instead has one initial
fixed-lag halt, zero running states, zero fresh calls and zero peak.

**Proof.** Use the exact whole-row/code fiber in Theorem 1.2 and the
all-address identity (NARC.2.2) in Theorem 2.1. Every $n\in[l,u]$
is realized by the one actual original $X_{a_0,z-(n-a_0)}$ and its own
$n-a_0$ updates, with current tree
$\langle T_n,T_{q+z}\rangle$. Every compatible history has exactly
one of those ages. These are the supplied two fiber directions; no
source or acquisition proof is replaced by a new scalar promise.

For the state lower bound, take any successful installed whole-tree
Moore table on this entire fiber. Its one fixed word at each running
state is $\varepsilon$, $Rp$ or $Lp$. By Theorem 2.1 the first two
forms have a constant reply $c_s$ over the fiber, determined by the
fixed whole input. The third form returns exactly $r_{T_n}(p)$.
Construct an interval table on the identical installed state set,
partition and initial state. At an $Lp$ state store $p$ and keep its
transition row. At a constant-reply state store the actual relative
root word $E$ and set

$$
\operatorname{next}'(s,a)=\operatorname{next}(s,c_s)
\quad(a\in\mathcal A).
\tag{NARC.4.4}
$$

This interval state really performs one paid root query and ignores
its reply through a constant table row; there is no free control step
or runtime simulation register. Relabel each fixed halt output $v$
by the fixed integer $a_0+v$. The shift is in the output table itself,
not an after-halt arithmetic decoder. For each $n$, induction along
the corresponding actual source's run gives exactly the same state
path, number of invocations and halt, now outputting $n$. Thus this
is an interval Moore controller of AOF Definition 10.1 with the same
running and total state counts. Its correctness is on every $n$ of
the supplied fiber, so AOF Theorem 10.2 gives (NARC.4.2)'s lower bounds.

This is an application of the paid state-local recoding method of
[NBP, Theorem 12.3 and (NBP.12.7)][NBP-NARC-Moore]. The required reply
correspondence here is the actual all-address reduction of Theorem
2.1, including every root query and arbitrarily deep or absent right
query. It depends only on the installed state and fixed acquired input,
so merging histories and cycles in the union of different source runs
do not require copied states. Unused states remain counted. In the
zero-origin case the two sources with hidden ages zero and one agree
on root and right queries and on every $Lp$ with nonempty $p$. A
successful table must therefore reach the physical word $L$, whose
at most three actual replies supply precisely the root-arity defect
of the interval lower bound.

The same paid correspondence preserves call count, and hence transfers
the interval call lower bound. It also makes the physical peak boundary
explicit. If $N\ge2$, peak zero permits only the constant physical
root and cannot recover all lags. For any physical peak cap $B\ge1$,
the interval table above submits suffixes of length at most $B-1$;
the replacement constant-query root has length zero. The interval peak
bound therefore forces $B\ge1+M(l,u)$. These lower bounds are exactly
those supplied in Theorem 2.1, now realized within the counted table
contract rather than with an external simulation payload.

For common attainment, take AOF Theorem 10.2's one interval table.
Replace every stored word $p$ by the stored physical word $Lp$, keep
every transition row and the initial state, and change the halt at
age $n$ to the fixed complete lag output $n-a_0$. Equation (NARC.2.2)
preserves every state path and call count on its corresponding actual
history. No subtraction, address construction or access to $a_0$
occurs during this run. The output constants and prefixes are already
in the installed table. It has $J(l,u)$ running states and $N$ halts.
For $N\ge2$, each submitted word has one more letter than its interval
word, so its peak is exactly $1+M(l,u)$ and its calls exactly $K(l,u)$.
A relative root read is the paid physical word $L$. For $N=1$ install
the sole halt with the unique compatible lag, with no query. These
witnesses meet all three minima together. When the cut displays the
left slot, Theorem 2.1 already determines the unique lag from its
genuinely acquired whole subtree and $a_0$. This computation supplies
the one fixed-output halt before entry; it is not an online clock or
an uncharged output decoder. $\square$

**Proposition 4.3 (conditional examples and the uniform-table boundary).**
At $H=3,a_0=0$ the fixed complete inputs of Theorem 3.1 have the
following simultaneous minima under Assumption 4.1:

| Lag convention and entire row | Hidden interval | Running states | Halts | Worst calls | Physical peak |
| --- | --- | --- | --- | --- | --- |
| $\lambda_0=0$, $Y_3=(\langle\square_L,T_7\rangle,\{\{L\}\})$ | $[0,3]$ | $2$ | $4$ | $2$ | $2$ |
| $\lambda_0=1$, $Y_4=(\langle\square_L,T_8\rangle,\{\{L\}\})$ | $[1,4]$ | $1$ | $4$ | $1$ | $2$ |

Even at fixed $H$, no single finite table with fixed numeric halts
returns every unbounded allowed lag over all genuine acquired inputs.
Fixed conditional state count and call price do not bound the static
literal/output representation or physical memory of this table family.

**Proof.** Apply Theorem 4.2 to the exact inputs and histories of
Theorem 3.1. In the first row the two running states read physical $L$
and, on its branch reply, $LR$; alpha and beta at the first go to
fixed lags zero and one, and alpha and beta at the second go to fixed
lags two and three. Fill the other entries with the halt zero. In
the second row one state reads $LR$, with absent, alpha, beta and
branch leading directly to the respective complete lags $1,2,3,4$.
These are the prefixed tables of AOF Proposition 10.3.

For the uniform obstruction take the legal original $X_{0,0}$ and
cut $\{L\}$. Its fixed code is zero, and after each permitted lag
$\ell$ its genuine entire later row is $Y_\ell$ of (NARC.1.2), with
right tree $T_{q+\ell}$. Correct outputs include arbitrarily large
$\ell$, whereas one finite halt set has finite numeric image. A
varying conditional table or external output field cannot be identified
with that one fixed table. For $H=0$ each conditional fiber is a
singleton but the same infinite-output obstruction persists across
inputs. For $H\ge1$ and $z\ge H+\lambda_0$, (NARC.4.1) is the
translated interval $[a_0+z-H,a_0+z]$ of fixed size $H+1$, with
unbounded physical peak by (NARC.4.3). Thus the separately charged
literal and complete numeric constants cannot be absorbed into the
abstract state cardinality or chronological call count. $\square$

**Mathematical citation 4.4 (fixed-reference correspondence).** The
whole-row/code fiber, each actual original and its pure-$\rho$ history,
and the all-address reduction are Theorems 1.2 and 2.1 at immutable
[revision 1f90f2ec304615c711e1ab2cdef401881881fcc9](https://github.com/the-omega-institute/trureturing/blob/1f90f2ec304615c711e1ab2cdef401881881fcc9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md#1-a-fixed-acquired-reference-and-the-entire-two-slot-input).
Their NAR source, acquisition, clock, causal-export and complete-cut
premises remain unchanged; no duplicate source or acquisition theorem
is asserted here. AOF Theorem 10.2 supplies the sharp interval state
bound and its common native witness. NBP12 at immutable
$\mathtt{0ec296c8f9cfd78898ea44f5faf5d1eaa49aa656}$ supplies paid
state-local reply recoding on shared graphs. Equations (NARC.2.2) and
(NARC.4.4) validate its method in this fixed-input task; its inverse-fiber
state frontier and joint encoder choices supply no numerical bound
for this fixed $E=a_0$.

The repo-derived application is the exact conditional state price
with the already exact calls and physical peak, including installed
lag outputs and all changing state. It asserts neither a minimum
over encoders nor a retained-alphabet minimum, an arbitrary menu or
an all-query $D>1$ bound. Acquisition, parsing, construction and
installation, immutable tables, complete output representation,
summed submitted length and physical service costs remain separate
from the three conditional coordinates. No global originality or
programme-wide recovery theorem follows from this correspondence.

[NBP-NARC-Moore]: https://github.com/the-omega-institute/trureturing/blob/0ec296c8f9cfd78898ea44f5faf5d1eaa49aa656/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md#12-exact-joint-record-total-moore-state-and-call-transfer-on-every-full-fiber

## 追加锚（本行以下为增补区）

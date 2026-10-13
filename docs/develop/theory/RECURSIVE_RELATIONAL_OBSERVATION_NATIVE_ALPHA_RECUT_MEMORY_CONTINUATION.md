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

## 5. Arbitrary acquired codes and complete singleton-cut fibers

**Assumption 5.1 (two independent ages and one exported alphabet).**
Specialize [NAR, Assumption 16.1 and Reuse 16.2][NAR] to two slots,
with public $q\ge1$, $H=q-1$, and the Cartesian source family

$$
\begin{aligned}
X_{a,b}&=\langle T_a,T_{q+b}\rangle,
&0\le a,b\le H,\\
T_0&=\alpha,&T_1&=\beta,
&T_{n+2}&=\langle T_{n+1},T_n\rangle.
\end{aligned}
\tag{NARC.5.1}
$$

Here $T_n=\rho^n\alpha$ for the actual homomorphic substitution of
[NAR, Definition 1.1][NAR]. Independence means that every pair in the
square is allowed; no probability distribution is imposed. The original
offsets are zero and $q$ throughout. The complete original empty-cut row
$R_{\varnothing}(X_{a,b})$ is genuinely acquired. A deterministic encoder
computes and exports a label $e(a,b)$ solely from that row, before the
future visible region and lag are chosen. The attained label set has
exactly $q$ members. The row and every other source-bearing field are
then discarded. All surviving source-bearing distinctions are counted
in this one label; a source-dependent table selection or a retained
origin is not an additional channel. Public controls common to every
source may include the finite encoder table.

Fix a public lag convention $\lambda\in\{0,1\}$. Correctness is required
for every $\ell\ge\lambda$, separately under each convention. The same
original undergoes its own pure-$\rho$ continuation, giving the current
tree

$$
Y(a,b,\ell)=\langle T_{a+\ell},T_{q+b+\ell}\rangle.
\tag{NARC.5.2}
$$

Both possible future singleton visible regions are required. Write
$V=R$ for a visible right slot and cut $Q=\{L\}$, and $V=L$ for a
visible left slot and cut $Q=\{R\}$. After the continuation, its complete
later row $R_Q(Y)$ is genuinely acquired, including the full literal
exterior, reached hole and its singleton partition. The row has no
hidden-visible comparison. The decoder receives this row, $V$ and the
exported label. It must return $\ell$ using at most one fresh chronological
native Read at a finite literal original-root word of this same stationary
current tree. The actual replies are $\mathsf{absent},\alpha,\beta,
\mathsf{branch}$. No update occurs during capture or reading, and no age,
subtree, epoch, old-source or hidden-visible comparison oracle is supplied.

The address must be determined by the received label, public $q$, selected
region and genuinely acquired row. Every letter is materialized before
the request. Arbitrary finite local parsing and computation are allowed,
with their own costs. Initial and later acquisition, retained-label
representation, row storage, workspace, arithmetic, word production and
lag-output representation are separate resources from chronological
Read count. This assumption varies the encoder; it does not impose the
fixed reference $e=a_0$ or the installed Moore-table restriction of §§1--4.

The supplied right clock $c$ has $c(T_n)=n$. In particular the original
acquired row computes $a=c(T_a)$ and $b=c(T_{q+b})-q$ before discard.
This is [NAR, (NAR.16.4)][NAR], not access to an unacquired age profile.
Later parsing of a visible literal computes its normalized clock, also
by the same supplier. These computations grant no clock of a hidden tree.

**Theorem 5.2 (the entire arbitrary-code input and its targets).**
Let $C=e^{-1}(\gamma)$ be any attained code class of Assumption 5.1;
no geometric condition on $C$ is assumed. Put $d(a,b)=a-b$. A promised
right-visible input has, for an integer $z\ge\lambda$, the entire row

$$
\mathcal R^R_z=
 \bigl(\langle\square_L,T_{q+z}\rangle,\{\{L\}\}\bigr).
\tag{NARC.5.3}
$$

Its complete code/row fiber, hidden left age and required lag are exactly

$$
\begin{aligned}
F_R(C,z,\lambda)&=\{(a,b)\in C:b\le z-\lambda\},\\
n_R(a,b)&=z+d(a,b),&\ell_R(a,b)&=z-b.
\end{aligned}
\tag{NARC.5.4}
$$

A promised left-visible input has the entire row

$$
\mathcal R^L_z=
 \bigl(\langle T_z,\square_R\rangle,\{\{R\}\}\bigr),
\qquad z\ge\lambda,
\tag{NARC.5.5}
$$

with exact fiber and targets

$$
\begin{aligned}
F_L(C,z,\lambda)&=\{(a,b)\in C:a\le z-\lambda\},\\
n_L(a,b)&=q+z-d(a,b),&\ell_L(a,b)&=z-a.
\end{aligned}
\tag{NARC.5.6}
$$

Each member is realized by its own fixed original and its indicated lag.
Equality here includes every exterior label and bracket, the reached
hole and the whole partition. On a nonempty fiber, zero fresh calls are
possible exactly when its visible-origin coordinate ($b$ for $V=R$,
$a$ for $V=L$) is constant.

Every original-root query is the empty word or has a slot prefix $L$ or
$R$. The empty-root reply and all visible-prefixed replies are constant
on this whole input fiber. A hidden-prefixed query returns precisely
the relative native reply on $T_{n_R}$ or $T_{n_L}$. Thus a nonconstant
target can be recovered with one call only by a target-constant partition
of these hidden-age replies, with the word selected before that call
from the common acquired entry.

**Proof.** Homomorphism gives (NARC.5.2). The two slots remain reached
even if a filling is a leaf. For the right-visible cut, replacement of
the entire left filling gives (NARC.5.3). The single hole has exactly its
singleton partition, independently of its value. The acquired right
literal has clock $q+b+\ell$; subtracting $q$ gives $z=b+\ell$.
Since the clock distinguishes the $T_n$, any history with this whole
row must satisfy that equation. Its lag is therefore $z-b$, and the
lag restriction is exactly $b\le z-\lambda$. Substitution in the hidden
age $a+\ell$ gives $z+a-b$.

Conversely, take any $(a,b)\in C$ with $b\le z-\lambda$ and set
$\ell=z-b$. This is a legal lag on the one fixed original $X_{a,b}$.
Its actual current tree is $\langle T_{z+a-b},T_{q+z}\rangle$.
Its code is $\gamma$, and its complete later row is (NARC.5.3), including
all its labels, brackets, reached guard and singleton partition. This
proves both directions of (NARC.5.4) and shows that $n_R\ge0$ on the
fiber. For the left-visible cut, the same argument starts with the
acquired clock $z=a+\ell$. Each pair with $a\le z-\lambda$ is realized
at $\ell=z-a$ by $\langle T_z,T_{q+z-a+b}\rangle$, with exactly
(NARC.5.5); its hidden right age is at least $q$. These are complete
histories, each using the same original through its own continuation.
Their whole-row equality is also the specialization of [NAR,
(NAR.16.6)][NAR].

If the visible origin is a common $v$, return $z-v$. If it varies, the
same received entry requires two different lags, so a deterministic
zero-call output fails. Finally every current source is a branch at
the original root, giving a constant empty-root reply. A word entering
the visible slot is evaluated on the same acquired literal for every
fiber member, including words that return absence. A word entering the
hidden slot is evaluated on its indicated actual filling. This exhausts
all original-root words. With at most one call there is no previous
fresh reply on which to base its selection; all members of the entry
receive the same selected word. Correctness is exactly constancy of
the required target on each realized reply cell. $\square$

**Definition 5.3 (supplied native partitions and literal realization).**
Reuse [AOF, Definition 8.2, (AOF.24)][AOF]. Denote absence by $\bot$
and branch by $\mathsf b$. For nonnegative ages the supplied relative
response functions are

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\ \hline
E&\text{never}&n=0&n=1&n\ge2\\
P_t\ (t\ge2)&n<t&n=t&n=t+1&n>t+1\\
S_t\ (t\ge2)&n<t&\text{never}&n=t&n>t.
\end{array}
\tag{NARC.5.7}
$$

Every finite relative word has one of these response functions, by the
supplier's proper-prefix guard. $S_t$ is a coarsening of $P_t$: send
$\bot$ to $\bot$, $\alpha$ to $\beta$, and both $\beta$ and
$\mathsf b$ to $\mathsf b$. Hence a target recovered
by $S_t$ can also be recovered by the legal $P_t$. The relative root
experiment $E$ may be denoted $P_0$ as a response function. The native
menu has no $P_1$.

The following supplied literal representatives will be used:

$$
w_0=\varepsilon,\qquad
w_{2m}=R^m\ (m\ge1),\qquad
w_{2m+1}=LR^m\ (m\ge1).
\tag{NARC.5.8}
$$

For $t=0$ they realize $E$; for $t\ge2$ they realize $P_t$.
At a right-visible entry submit $Lw_t$; at a left-visible entry submit
$Rw_t$. In particular $w_0$ is an empty suffix, but $Lw_0=L$ and
$Rw_0=R$ each cost one original-root call. They are distinct from the
uninformative original-root empty word. Powers in (NARC.5.8) mean actual
finite sequences of letters.

## 6. The seven-point equality geometry and universal obstruction

**Theorem 6.1 (class bound and complete large-row equality geometry).**
For any encoder and successful at-most-one-call decoder in Assumption
5.1, $d=a-b$ is injective in every class $C$, and

$$
|C|\le7.
\tag{NARC.6.1}
$$

If one coordinate is constant on $C$, then $|C|\le4$. At $|C|=7$,
the class is exactly a union of four-point row and column arms sharing
one corner:

$$
C=(\{A\}\times B_*)\ \cup\ (A_*\times\{B\}).
\tag{NARC.6.2}
$$

Here $A_*,B_*$ each have four distinct integer values and contain $A,B$.
Either $A=\min A_*$ and $B=\min B_*$, or $A=\max A_*$ and
$B=\max B_*$. In the increasing ordering $x_0<x_1<x_2<x_3$ of
each arm's coordinate set, its two interior values satisfy

$$
x_2=x_1+1.
\tag{NARC.6.3}
$$

There is no requirement that either outer gap be one. Conversely every
such seven-point class contained in the source square has both its full
large-$z$ coordinate targets separated by one legal native call under
each singleton cut. This converse concerns all sufficiently large full
fibers, rather than every small-$z$ truncated fiber.

**Proof.** First reuse the common-translation obstruction of [NAR,
Theorem 16.3][NAR]. Its specialization can be seen directly: if distinct
$(a,b),(a',b')\in C$ have the same $d$, then $b\ne b'$. Choose
$z\ge q+2$. Both belong to the right-visible fiber of Theorem 5.2 for
either lag convention. At lags $z-b$ and $z-b'$ their entire current
trees are the same $\langle T_{z+d},T_{q+z}\rangle$. Their code and
entire later row also agree, but the required outputs differ. Every
native reply is identical. Deterministic transcript induction therefore
precludes recovery even with arbitrarily many current reads. Thus $d$
is injective. This does not assume any particular code shape.

Fix this same $z\ge q+2$ for each of the two visible regions. Both
fibers contain all of $C$, and all hidden ages are at least two.
List its $m$ points as $p_1,\ldots,p_m$ in strictly increasing $d$,
writing their coordinates $a_i,b_i$ and $d_i=a_i-b_i$. Let

$$
D_a=\{i<m:a_i\ne a_{i+1}\},\qquad
D_b=\{i<m:b_i\ne b_{i+1}\}.
\tag{NARC.6.4}
$$

Every successive pair of distinct points changes at least one
coordinate, so $D_a\cup D_b=\{1,\ldots,m-1\}$.
For the right-visible entry the target is $b$. If it is constant,
$D_b=\varnothing$. Otherwise Theorem 5.2 forces an informative hidden
query. Its $E$ reply is constant on these ages, so Definition 5.3 lets
us take a successful $P_t$ with $t\ge2$, refining $S_t$ if necessary.
Since $n_R=z+d$ increases with $d$, this partitions the ordered points
into a lower tail, at most one point at $n=t$, at most one at $n=t+1$,
and an upper tail. Each nonempty cell is an interval of this order,
and $b$ is constant in it. Consequently $|D_b|\le3$. For the
left-visible entry $n_L=q+z-d$ reverses the order, but its successful
partition has the same two tails and at most two singleton cells.
The identical reasoning gives $|D_a|\le3$. Thus

$$
m-1=|D_a\cup D_b|\le |D_a|+|D_b|\le6,
\tag{NARC.6.5}
$$

proving the bound. When $a$ is constant, injectivity of $d$ makes all
$b$ values distinct, so recovering them with one four-reply call
requires $m\le4$. The argument with $a,b$ exchanged proves the other
constant-coordinate case. All these deductions use the actual tests
chosen at the fixed complete entries, not an assumed uniform threshold
across different entries.

Suppose now $m=7$. Equality in (NARC.6.5) forces $D_a,D_b$ to be
disjoint sets of size three covering the six gaps. For either successful
refined $P_t$, all four cells must be nonempty: fewer cells permit fewer
than three changes. Every cell boundary must change its target, and
there are no changes inside a cell. If its lower tail ends at position
$j$, its middle cells are exactly positions $j+1,j+2$. Its three
change gaps are therefore $j,j+1,j+2$. This remains true on reversing
the order for the left-visible query. Two disjoint consecutive
three-gap blocks covering $1,\ldots,6$ must be $\{1,2,3\}$ and
$\{4,5,6\}$.

If $D_b=\{1,2,3\}$, then $a$ is constant on points $1,\ldots,4$,
while $b$ is constant on points $4,\ldots,7$. Along the first arm,
strictly increasing $d$ and constant $a$ force strictly decreasing $b$;
along the second, constant $b$ forces strictly increasing $a$. Their
common point $p_4=(A,B)$ is the minimum of both arm coordinate sets.
The $b$ query has its singleton middle cells at $p_2,p_3$, so
$d_3-d_2=1$, and hence $b_2-b_3=1$. These are the interior values of
the four-element $B_*$ in increasing order. The $a$ query has its
singleton middle cells at $p_5,p_6$, so $d_6-d_5=1$ and
$a_6-a_5=1$. These are the interior values of $A_*$. This proves
(NARC.6.2)--(NARC.6.3) in the minimum-corner case.

If $D_a=\{1,2,3\}$, points $1,\ldots,4$ have constant $b$ and
strictly increasing $a$, and points $4,\ldots,7$ have constant $a$
and strictly decreasing $b$. The shared point $p_4$ is now the maximum
of both sets. The singleton middle cells are again $p_2,p_3$ for
the first varying coordinate and $p_5,p_6$ for the second. Their
consecutive ages prove the two interior adjacencies in (NARC.6.3).
These two cases exhaust the equality possibilities. They impose no
condition on the distances from the interior values to the endpoints.

For the converse, consider first a minimum-corner class. Its $d$ order
has four constant-$a$ row points followed by four constant-$b$ column
points, sharing $p_4$. The two interior $b$ values give consecutive
$d_2,d_3$; the two interior $a$ values give consecutive $d_5,d_6$.
For a sufficiently large $z$, query $P_{z+d_2}$ on the hidden left
slot. Its lower tail is $p_1$, its middle cells are $p_2,p_3$, and its
upper tail is $p_4,\ldots,p_7$, where $b$ is constant. Query
$P_{q+z-d_6}$ on the hidden right slot. In increasing hidden-age
order its cells are $p_7$, $p_6$, $p_5$, and $p_4,\ldots,p_1$,
the last having constant $a$. Both targets are thus recovered. In the
maximum-corner case the $a$ variation is first and $b$ variation last:
use $P_{z+d_5}$ for $b$ and $P_{q+z-d_3}$ for $a$.
All selected thresholds are at least two once $z$ is large; both
fibers are then full. Definition 5.3 supplies literal representatives
and Theorem 5.2 supplies every corresponding actual history. This
proves precisely the claimed large-row converse. $\square$

**Theorem 6.2 (no seven-label partition, including gapped arms).**
Assumption 5.1 admits no successful at-most-one-call encoder/decoder
with exactly $q$ attained labels when $q\ge7$, for either lag convention.

**Proof.** Each of the $q$ classes has size at most seven by Theorem 6.1.
For $q\ge8$, $q^2>7q$ precludes their covering the $q^2$ original
pairs. It remains to exclude $q=7$.

In a partition of the $7\times7$ square by seven feasible classes,
all classes would have size seven. Each has the two four-point arms
of (NARC.6.2), with a minimum or maximum corner. Two corners cannot
share a row: their disjoint four-point row arms would require eight
cells in a row of length seven. Likewise two corners cannot share a
column. Thus there is one corner per row and per column; write them
as $(i,\pi(i))$ for a permutation $\pi$ of $0,\ldots,6$. Call the
class with this corner the row-$i$ class. A cell $(i,j)$ can belong
only to the row-$i$ class's row arm or to the class with corner in
column $j$'s column arm.

A minimum corner has three distinct larger values on each arm, so
both its coordinates are at most three. A maximum corner has three
distinct smaller values on each arm, so both are at least three.
The corners in rows $0,1,2$ are therefore minimum corners, and those
in rows $4,5,6$ are maximum corners. If row three has a maximum
corner, the four maximum corners occupy exactly columns $3,4,5,6$,
leaving columns $0,1,2$ for the minimum corners. If row three has a
minimum corner, the four minimum corners occupy exactly columns
$0,1,2,3$. Consequently, for $m\in\{3,4\}$, the minimum corners
match rows and columns $0,\ldots,m-1$, and the maximum corners match
the complementary rows and columns.

We next force $\pi$ to be the identity. In the minimum-corner block,
proceed upward. Suppose rows less than $i$ are already fixed. If
$\pi(i)\ne i$, then $\pi(i)>i$, because every smaller column has
its fixed corner. The corner in column $i$ also has row
$\pi^{-1}(i)>i$. The row-$i$ minimum arm reaches only columns at
least $\pi(i)$, and the column-$i$ minimum arm reaches only rows
at least $\pi^{-1}(i)$. Neither covers $(i,i)$, and no other class
can cover it. This contradiction gives $\pi(i)=i$. In the maximum
block, proceed downward. If the larger rows are fixed and
$\pi(i)\ne i$, then $\pi(i)<i$ and $\pi^{-1}(i)<i$. The two
maximum arms reach only columns or rows at most these respective
values, leaving $(i,i)$ uncovered. Thus this block too is fixed.

There are now two middle-corner cases. If $m=3$, class three has
maximum corner $(3,3)$; both four-value arm sets are forced to be
$\{0,1,2,3\}$. It contains $(1,3)$. The cell $(1,2)$ cannot be
on the column arm of minimum-corner class two, since that arm has
rows at least two. It must be on the row arm of minimum-corner
class one. That arm has its minimum value one, contains two, and
has two further values $2<u<v$. Its ordered values are
$\{1,2,u,v\}$. Interior adjacency (NARC.6.3) forces $u=3$.
Hence class one also contains $(1,3)$, contradicting disjointness.

If $m=4$, class three has minimum corner $(3,3)$, so both its arm
sets are $\{3,4,5,6\}$. It contains $(5,3)$. The cell $(5,4)$
cannot be on the column arm of maximum-corner class four, whose
rows are at most four. It must be on the row arm of maximum-corner
class five. That arm has ordered values $\{u,v,4,5\}$, where
$u<v<4$. Interior adjacency forces $v=3$, so class five also
contains $(5,3)$, again a contradiction.

Neither argument restricted the outer arm gaps. The class bound
and all its equality constraints were derived from full entries
realized at positive lags. The obstruction therefore applies to
$\ell\ge1$ and, using the same histories, to $\ell\ge0$. $\square$

## 7. One acquired relational code and a literal all-lag decoder

**Definition 7.1 (one prefix-compatible encoder).** Let the public
matrix, with rows indexed by $a$ and columns by $b$, be

$$
M=\begin{pmatrix}
0&1&2&1&1&5\\
0&1&2&3&3&3\\
0&1&2&0&0&0\\
2&2&2&3&4&5\\
4&4&4&3&4&5\\
5&1&5&5&4&5
\end{pmatrix}.
\tag{NARC.7.1}
$$

For $1\le q\le6$, set $e_q(a,b)=M_{a,b}$ on the upper-left
$q\times q$ block, and write $C_{q,\gamma}=e_q^{-1}(\gamma)$.
The encoder computes the two coordinates from the genuinely acquired
original row as in Assumption 5.1, exports this entry, and discards
the row and both coordinates. The public matrix is the same for
every original in the declared family.

**Definition 7.2 (one-call selection and reply decoding).** At a promised
entry parse $z$ from the acquired row and form the exact fiber of
Theorem 5.2 with $C=C_{q,\gamma}$. If its visible-origin coordinate
is constant $v$, halt with $z-v$ without a call. Otherwise select the
following relative experiment; the subscript is a threshold, not an
oracle-supplied age:

| Code $\gamma$ | Right visible, hidden left | Left visible, hidden right |
| --- | --- | --- |
| $0$ | $P_{\max(2,z-2)}$ | $P_{q+z-1}$ |
| $1$ | $E$ if $z\le4$; $P_{z-3}$ if $z\ge5$ | $P_{q+z-1}$ |
| $2$ | $P_{z+2}$ | $P_{q+z}$ |
| $3$ | $E$ if $z\le4$; $P_{z-3}$ if $z\ge5$ | $P_{q+z-1}$ |
| $4$ | $P_{z+2}$ | $P_{q+z-1}$ |
| $5$ | $P_{z+2}$ | $P_{q+z+1}$ |

Materialize its representative (NARC.5.8), prefixed by $L$ for right
visibility or $R$ for left visibility, and submit that one whole word.
After its actual reply, keep the candidates in the exact fiber whose
predicted relative reply in (NARC.5.7) is that reply. Output $z-v$,
where $v$ is their common visible origin. Theorem 7.3 establishes
that this set is nonempty and its origin is constant for every actual
reply on a promised input. For an input or reply outside the promise,
one may assign output zero; no correctness there is required.

**Theorem 7.3 (attained alphabet and all-lag native reply certificate).**
For every $1\le q\le6$, Definition 7.1 attains exactly the $q$ labels
$0,\ldots,q-1$. Definitions 7.1--7.2 satisfy Assumption 5.1 for both
visible regions and every $\ell\ge0$. The same encoder and query
schedule work for every $\ell\ge1$ with that convention's exact
fiber. Every actual queried reply determines a unique lag, even when
it leaves more than one possible original pair. Every nonconstant
fiber uses one legal literal call, and every constant fiber uses zero.

**Proof, the finite class identities.** Every entry of the upper-left
$q$ block is less than $q$: the new border of sizes two and three uses
only labels up to one and two, and the new borders of sizes four,
five and six use only labels up to three, four and five. The diagonal
entries are $M_{t,t}=t$ for $0\le t\le5$. Hence all and only the
declared labels are attained. Assumption 5.1's acquired clock
computations give a causal evaluation of this finite table.

For clarity, all six full-square classes are displayed here in
increasing $d=a-b$ order:

| Code | Ordered original pairs | Ordered differences |
| --- | --- | --- |
| $0$ | $(2,5),(2,4),(2,3),(0,0),(1,0),(2,0)$ | $-3,-2,-1,0,1,2$ |
| $1$ | $(0,4),(0,3),(0,1),(1,1),(2,1),(5,1)$ | $-4,-3,-1,0,1,4$ |
| $2$ | $(0,2),(1,2),(2,2),(3,2),(3,1),(3,0)$ | $-2,-1,0,1,2,3$ |
| $3$ | $(1,5),(1,4),(1,3),(3,3),(4,3)$ | $-4,-3,-2,0,1$ |
| $4$ | $(3,4),(4,4),(5,4),(4,2),(4,1),(4,0)$ | $-1,0,1,2,3,4$ |
| $5$ | $(0,5),(3,5),(4,5),(5,5),(5,3),(5,2),(5,0)$ | $-5,-2,-1,0,2,3,5$ |

In particular $d$ is injective within each class. Define the signed
threshold offsets

$$
(r_0,\ldots,r_5)=(-2,-3,2,-3,2,2),\qquad
(s_0,\ldots,s_5)=(0,0,-1,0,0,-2).
\tag{NARC.7.2}
$$

For each class the following table gives the common $b$ value on
the four difference cells $d<r_\gamma$, $d=r_\gamma$,
$d=r_\gamma+1$, $d>r_\gamma+1$:

| Code | $d<r_\gamma$ | $d=r_\gamma$ | $d=r_\gamma+1$ | $d>r_\gamma+1$ |
| --- | --- | --- | --- | --- |
| $0$ | $5$ | $4$ | $3$ | $0$ |
| $1$ | $4$ | $3$ | $\varnothing$ | $1$ |
| $2$ | $2$ | $1$ | $0$ | $\varnothing$ |
| $3$ | $5$ | $4$ | $3$ | $3$ |
| $4$ | $4$ | $2$ | $1$ | $0$ |
| $5$ | $5$ | $3$ | $2$ | $0$ |

The corresponding common $a$ values on the reversed difference cells
are

| Code | $d>s_\gamma+1$ | $d=s_\gamma+1$ | $d=s_\gamma$ | $d<s_\gamma$ |
| --- | --- | --- | --- | --- |
| $0$ | $2$ | $1$ | $0$ | $2$ |
| $1$ | $5$ | $2$ | $1$ | $0$ |
| $2$ | $3$ | $2$ | $1$ | $0$ |
| $3$ | $\varnothing$ | $4$ | $3$ | $1$ |
| $4$ | $4$ | $5$ | $4$ | $3$ |
| $5$ | $5$ | $4$ | $3$ | $0$ |

Here $\varnothing$ denotes an empty candidate cell. These identities
follow directly from the displayed ordered pairs: each tail has the
stated common coordinate, and each present middle difference occurs
once. They certify the entire 36-point square; the tables specify
origin values, rather than identifying every original pair.

**Proof, regular right-visible inputs.** Since $n_R=z+d$, the
experiment $P_{z+r_\gamma}$ has exactly the four $b$ cells of the
first table in actual reply order $\bot,\alpha,\beta,\mathsf b$.
For code zero it is legal when $z\ge4$; for codes one and three
when $z\ge5$; and for codes two, four and five at every $z\ge0$.
These are the regular cases of Definition 7.2. Restricting to
$b\le z$ preserves coordinate constancy in each cell. Thus the
certificate handles all regular right-visible fibers without an
upper bound on $z$.

**Proof, every exceptional right-visible input.** It suffices first
to take $q=6$ and $\lambda=0$. In code zero the only $b$ values are
$0,3,4,5$, the last three occurring at $a=2$. For $z\le2$, every
nonempty fiber has $b=0$ and halts. At $z=3$, the pair $(2,3)$ has
hidden age two, whereas $(0,0),(1,0),(2,0)$ have ages three, four,
five. The legal $P_2$ returns $\alpha$ for $b=3$, and $\beta$ or
$\mathsf b$ for $b=0$. In particular replacing the unavailable
$P_1$ by $E$ would not work at this entry; Definition 7.2 uses $P_2$.

In code one, the $b=3,4$ pairs have $a=0$, and every other pair
has $b=1$. For $z\le2$ a nonempty fiber has only $b=1$ and halts.
At $z=3$, $E$ returns $\alpha$ on $(0,3)$ and $\mathsf b$ on
the $b=1$ pairs, whose ages are two, three, four, seven. At $z=4$,
$E$ returns $\alpha$ on $(0,4)$, $\beta$ on $(0,3)$, and
$\mathsf b$ on every $b=1$ pair. Thus each reply again determines
one origin. In code three the exceptional $b=4,5$ pairs have $a=1$,
and all other pairs have $b=3$. For $z\le3$ any nonempty fiber
has only $b=3$. At $z=4$, $E$ returns $\beta$ on $(1,4)$,
and $\mathsf b$ on the $b=3$ pairs, whose ages are two, four, five.
The complete exceptional reply assignment is therefore

| Code and clock | Relative experiment | $\bot$ origin | $\alpha$ origin | $\beta$ origin | $\mathsf b$ origin |
| --- | --- | --- | --- | --- | --- |
| $0,z=3$ | $P_2$ | $\varnothing$ | $3$ | $0$ | $0$ |
| $1,z=3$ | $E$ | $\varnothing$ | $3$ | $\varnothing$ | $1$ |
| $1,z=4$ | $E$ | $\varnothing$ | $4$ | $3$ | $1$ |
| $3,z=4$ | $E$ | $\varnothing$ | $\varnothing$ | $4$ | $3$ |

Together with the constant-fiber halts and the regular cases, this
exhausts every $z\ge0$ for all six right-visible classes, including
hidden ages zero and one. Every $E$ listed is one paid physical $L$
request.

**Proof, every left-visible input.** Put
$t=q+z-s_\gamma-1$, precisely the left-column schedule of
Definition 7.2. The hidden age $n_L=q+z-d$ obeys

$$
\begin{aligned}
n_L<t&\Longleftrightarrow d>s_\gamma+1,\\
n_L=t&\Longleftrightarrow d=s_\gamma+1,\\
n_L=t+1&\Longleftrightarrow d=s_\gamma,\\
n_L>t+1&\Longleftrightarrow d<s_\gamma.
\end{aligned}
\tag{NARC.7.3}
$$

Thus the second certificate table is in actual reply order
$\bot,\alpha,\beta,\mathsf b$, with a common $a$ in every
occupied cell. For $q\ge3$, all $s_\gamma\le0$ make $t\ge2$.
For $q=2$ only codes zero and one occur. A nonconstant $a$ fiber
must include $a=1$, and consequently has $z\ge1$, giving
$t=q+z-1\ge2$. For $q=1$ every fiber is constant. This proves
availability at every queried left-visible input; no $P_1$ or small
clock exception is omitted.

**Proof, prefix restrictions, positive lags and causal output.** For
each smaller $q$, its class is exactly the intersection of the displayed
six-square class with $[0,q-1]^2$. Right-hidden ages $z+d$ and the
right schedule do not change; deleting pairs cannot put different
origins into one reply cell. On the left, both hidden ages and regular
thresholds shift by $q-6$, so (NARC.7.3) continues to give the same
reply cells. The preceding legality argument covers even $q=1,2$.
Restricting either fiber further to visible origin at most $z-1$
gives exactly the strictly positive-lag fiber. It only deletes
candidates, so the same queries still have constant origins on their
actual reply cells. If a deletion makes the target constant, the
initial zero-call rule applies instead. In particular both conventions
retain all their singleton and other constant-target fibers.

The actual original belongs to the exact fiber by Theorem 5.2. Its
reply leaves that candidate in the filtering step. Every remaining
candidate has the same visible origin by the regular or exceptional
certificate, so $z-v$ is a unique correct lag. A cell marked empty
cannot be an actual reply on a promised queried input. The selected
address uses only code, $q$, region and the acquired $z$; it never
uses the actual hidden age or lag. The threshold computations are
finite predictions on public candidate pairs. They are not reads
of candidate sources. Clock parsing on a finite acquired tree,
enumeration of at most $q^2$ pairs and materialization of one finite
word all terminate. There is at most one chronological native call,
and no original row or unexported origin is accessed. $\square$

**Proposition 7.4 (gapped equality and the zero-origin distinction).**
The feasible code-five class at $q=6$ has row-arm coordinate set
$B_*=\{0,2,3,5\}$, column-arm coordinate set
$A_*=\{0,3,4,5\}$, maximum corner $(5,5)$, and differences
$\{-5,-2,-1,0,2,3,5\}$. Thus neither consecutive differences
nor consecutive arm endpoints are necessary for all-lag one-call
service. In contrast, the minimum-corner class

$$
C_*=(\{0\}\times\{0,1,2,3\})\ \cup\
     (\{0,1,2,3\}\times\{0\})
\tag{NARC.7.4}
$$

fits the large-row equality geometry but cannot recover its
right-visible nonnegative-lag fiber at $z=3$ with one native call.
This second statement applies to any source square with $q\ge4$
containing this class; it is a class obstruction, not a rejection of
the encoder of Definition 7.1.

**Proof.** Code five's ordered pairs in Theorem 7.3 give its two stated
arm sets and differences. Its row interior values are two and three;
its column interior values are three and four. Both satisfy
(NARC.6.3), while their outer gaps and difference gaps are not all
one. Theorem 7.3 provides actual one-call service for this entire
class at every permitted input under both lag conventions.

For $C_*$ and $z=3$, Theorem 5.2 gives all seven pairs as actual
complete-input alternatives. In increasing hidden-age order their
ages are $0,1,2,3,4,5,6$, with respective $b$ targets
$3,2,1,0,0,0,0$. $E$ merges ages two and three, whose targets
differ. Every $P_t$ with $t\ge2$ merges ages zero and one in its
absent cell, also with different targets. $S_t$ is coarser and
cannot help; root and visible words are constant by Theorem 5.2.
The conceptual $P_1$ partition would separate the targets, but is
unavailable by Definition 5.3. Hence the large-row converse of
Theorem 6.1 cannot be extended to all nonnegative-lag fibers from
arm geometry alone. $\square$

**Theorem 7.5 (the exact minimum-alphabet one-read boundary).**
Under Assumption 5.1, a deterministic encoder with exactly $q$
attained labels and an all-lag decoder using at most one chronological
fresh native original-root Read for both singleton visible regions
exist if and only if

$$
1\le q\le6.
\tag{NARC.7.5}
$$

This holds separately for $\ell\ge0$ and for $\ell\ge1$.
The alphabet is the inherited minimum retained alphabet even if
arbitrary finite current querying were allowed. At this alphabet,
the exact worst fresh-call minimum is zero for $q=1$ and one for
$2\le q\le6$.

**Proof.** Theorems 7.3 and 6.2 prove the two directions of
(NARC.7.5), including both lag conventions. The minimum-alphabet
lower bound is the supplied [NAR, Theorem 16.3][NAR]: the $q$
diagonal originals $X_{t,t}$ at positive lags $q-t$ have the same
whole current tree $\langle T_q,T_{2q}\rangle$, the same later
row for either selected region, and different required lags. They
need distinct retained labels regardless of subsequent querying.
[NAR, Theorem 16.4][NAR] already attains this $q$-label minimum
with finite current recovery for the declared two-slot menu. Theorem
7.3 refines its fresh-call resource through $q=6$.

At $q=1$ the only original pair is $(0,0)$, so either normalized
visible clock is already $\ell$. For $q>1$, suppose zero calls
worked with $q$ labels. At $z\ge q+2$ each right-visible fiber
is its full class, so Theorem 5.2 forces $b$ constant on that class.
The full left-visible fiber forces $a$ constant there. Every class
would therefore be a singleton, requiring $q^2>q$ labels. Thus
the one-call upper bound for $2\le q\le6$ is sharp. This is
also the two-slot specialization of the supplied zero-read memory
criterion [NAR, Theorem 11.6 and Reuse 16.2][NAR]. $\square$

## 8. Mathematical correspondence and the retained-resource boundary

**Mathematical citation 8.1 (supplies and the precise new deduction).**
The carriers, homomorphic continuation and complete-row interpretation
are [NAR, Definitions 1.1--1.2][NAR]. Its Reuse 16.2 supplies the
acquired original coordinates, normalized visible clocks and complete
later-row equality; Theorems 16.3--16.4 supply the common-translation
obstruction and exact minimum alphabet $q$. [AOF, Definition 8.2][AOF]
supplies the all-word $E/P/S$ law with its proper-prefix guard,
unavailable $P_1$ and literal representatives. These supplies and
the fixed-reference results of §§1--3 are available at immutable
[revision 1f90f2ec304615c711e1ab2cdef401881881fcc9](https://github.com/the-omega-institute/trureturing/tree/1f90f2ec304615c711e1ab2cdef401881881fcc9).
Theorem 3.1's retained-left call prices and Theorem 3.2's retained-right
$q=4$ improvement remain statements about those specified encoders.
The installed-table restrictions and conditional state prices of §4
are separate from Assumption 5.1's finite local computation.

The native source correspondences are `Source` and `substitution` in
[GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
`Address`, `Reply` and `readout` in
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean),
`rightClock`, `rights`, `right_clock_iterate` and `right_clock_readout`
in [DelayedOriginalReadout](../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean),
and `literalRecord`, `actualPartition` and `canonicalRow_record_iff`
in [ActualCutPartitionDecoder](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean).
The orbit recurrence used here is also the local recurrence in
[ActualFibonacciSupportChain](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.lean).
These are semantic suppliers. The distinct-address payment convention
in ActualTreeReadoutAcquisition is not the chronological call objective
of Assumption 5.1, and a supplied epoch in `original_decoder_service`
does not supply this unknown-lag output.

The bounded primary correspondence for zero-error target separation is
Charpenay, Le Treust and Roumy,
[*Optimal Zero-Error Coding for Computing under Pairwise Shared Side
Information*, arXiv:2211.03649v2, Definition III.1 and Theorem III.4's
proof outline](https://arxiv.org/html/2211.03649v2). Adjacency there
requires two inputs with different function targets at a common
compatible side-information value. This is the role of different
required lags at the same code and entire later row in Theorem 5.2.
Their Definition II.1 concerns prefix-free encodings, expected length
per i.i.d. block and support-restricted zero-error decoding; Theorem
III.4 gives an asymptotic chromatic-entropy rate. No source distribution,
entropy formula or pairwise-shared single-letter hypothesis is
transferred to this attained-alphabet, worst-call problem.

For the importance of the permitted reply geometry, compare Nowak,
[*The Geometry of Generalized Binary Search*, arXiv:0910.4397v5,
§§I--II and V.A](https://arxiv.org/html/0910.4397v5). Its hypotheses
are a finite family of binary-valued functions on an allowed query
space. Theorem 1's bound depends on neighborliness and coherence;
§V.A contrasts point tests with the stronger dyadic-subinterval tests.
That correspondence preserves the distinction between an allowed
native word and an arbitrary partition. It grants no four-way age
oracle or numerical bound used here.

These separation and restricted-query methods are literature-attested
ingredients. The complete arbitrary-code two-slot fibers, seven-point
class bound with gapped equality geometry, seven-square obstruction
and attained relational encoder with its all-lag literal reply decoder
are `repo-derived` ordinary deductions under Assumption 5.1. The
compared sources do not supply this exact joint one-read boundary.
This correspondence is bounded and makes no worldwide priority claim.

**Proposition 8.2 (finite words and the scope of the resource result).**
The construction in Definition 7.2 has a finite address at every
promised input. Its worst submitted length over all inputs is unbounded
for every fixed $2\le q\le6$. Theorems 6.2 and 7.5 concern exactly
$q$ attained labels and the two singleton visible regions; they give
no exact call minimum for $q\ge7$, no larger-alphabet tradeoff and no
arbitrary-menu optimum. Local computation and literal/output storage
remain separate resources.

**Proof.** When queried, $E$ has whole-word length one; a $P_t$
representative has whole-word length $1+\lceil t/2\rceil$. Every
threshold in Definition 7.2 is a finite integer computed from the
finite acquired row. For unbounded lengths fix $q\ge2$, take
code one, left visibility and $z\ge q+2$. Its full class contains
$(0,1)$ and $(1,1)$ in every prefix square. Their distinct $a$
values prevent a constant-fiber halt, and the schedule submits the
threshold $t=q+z-1$. Both histories are legal at their respective
lags $z$ and $z-1$ under either convention, and its length diverges
with $z$. This is a property of the specified construction, not a
new address optimum.

The lower proof partitions the declared square into exactly $q$
classes and uses both declared regions; changing either condition
changes its premises. The upper proof enumerates its finite acquired
fiber and constructs an input-dependent literal word and numeric
output. A bound on chronological calls alone does not bound the
lengths of those objects or the storage and work needed to obtain
them. Assumption 5.1 imposes no finite Moore restriction, fixed state
set, physical service law or uniform address cap. The result is
therefore precisely an alphabet and native-call boundary for this
acquired-input contract. $\square$

## 追加锚（本行以下为增补区）

## 9. Adaptive native calls and a joint-coordinate obstruction

**Assumption 9.1 (the acquired-code contract at a general call budget).**
Keep every source, acquisition, causal export, discard, complete-row,
original-offset and stationarity premise of Assumption 5.1. Replace only
its at-most-one-call restriction by at most $k$ fresh chronological Reads,
where $k\ge0$ is public. After a reply, the next finite literal word or
halt decision may depend on that reply and the earlier replies. The
controllers for the two visible regions may be different. Every repeated
request is another call. All local computation must terminate on a
promised input; its cost is separate from calls. No restriction to a
fixed finite Moore controller or uniformly bounded address is imposed.

Write $C_\gamma=e^{-1}(\gamma)$ for an attained class, and $d=a-b$.
The complete fibers, targets and all-address correspondence are exactly
Theorem 5.2, used also at later adaptive nodes by restricting its fiber
to the origins producing the preceding replies. The native $E/P/S$
law and literal representatives are Definition 5.3. These statements
and Theorem 7.5 are the published suppliers at
[revision 45fce68e14e6414d58c1ca396723012fa364aeea](https://github.com/the-omega-institute/trureturing/blob/45fce68e14e6414d58c1ca396723012fa364aeea/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md).
In particular, an adaptive extension changes neither the information
in an acquired row nor the meaning of a constructor Read.

**Theorem 9.2 (arbitrary-code adaptive class and alphabet bounds).**
Under Assumption 9.1, every attained class satisfies

$$
|C_\gamma|\le6\cdot2^k-5.
\tag{NARC.9.1}
$$

Consequently, with exactly $q$ attained labels,

$$
q\le6\cdot2^k-5.
\tag{NARC.9.2}
$$

These are necessary bounds under each lag convention. They cover
arbitrary deterministic acquired encoders, adaptive actual words,
different cut-specific controllers, repeated target coordinates and
early halts; they are not sufficient readability or packing criteria.

**Proof.** The supplied common-translation obstruction [NAR, Theorem
16.3][NAR] makes $d$ injective on each class even if arbitrarily many
adaptive current Reads are allowed. Indeed, its two-slot specialization
identifies two same-code, same-$d$ distinct origins with the same whole
current tree and entire acquired entry at legal positive lags, but
different required outputs. Equal entry and equal earlier replies force
the same next request or halt; the equal current trees give the same
next reply. Thus increasing the call budget cannot remove that
obstruction. We use this supplier rather than a one-call assumption.

Fix $Z=q+1$. By Theorem 5.2 both visible regions at normalized clock
$Z$ have complete fiber $C_\gamma$, under either convention. The right
hidden ages are $Z+d\in[2,2q]$; the left hidden ages are
$q+Z-d\in[q+2,3q]$. Order the $m=|C_\gamma|$ origins by increasing
$d$. Their right hidden ages increase strictly and their left hidden
ages decrease strictly.

Consider one of the two controllers on its own full acquired entry.
Root and visible-slot requests have entry-constant replies by Theorem
5.2 and can be simulated locally. Each hidden request is an $E$, $P_t$
or $S_t$ experiment by Definition 5.3. Its reply cells are intervals
in the ordered origins. A $P_t$ has two tails and at most two singleton
cells; an $S_t$ has two tails and at most one singleton. Injectivity of
$d$ is essential here: a singleton age contains at most one origin.
$E$ is constant branch on these reference ages. Intersecting an
interval support with a reply cell again gives an interval support.
Thus every nonempty adaptive transcript leaf is an ordered interval,
even for a sparse class or response-dependent next address.

Let $L_j=3\cdot2^j-2$, so $L_0=1$ and $L_j=2L_{j-1}+2$ for
$j\ge1$. A depth-zero tree has at most one nonempty leaf. Inductively,
each tail after a first request has at most $L_{j-1}$ leaves, and each
singleton cell has at most one, regardless of the subsequent control.
There are therefore at most $2L_{j-1}+2=L_j$ leaves. An $S_t$, a
constant request or an early halt gives no more. This proves the bound
for every adaptive depth-$j$ tree. A terminating deterministic program
on this finite entry induces such a tree: at each common transcript
its next action is fixed, and at most four replies and $j$ calls can
occur. Uncharged computation adds no source-dependent branches.

Correctness of the right-visible controller makes $b$ constant on
each of its at most $L_k$ interval leaves, because the required lag is
$Z-b$. Its leaf partition therefore has at most $L_k-1$ boundaries
between consecutive ordered origins. Independently, correctness of
the left-visible controller makes $a$ constant on each of its at most
$L_k$ leaves, with at most $L_k-1$ boundaries in the same $d$ order;
reversing age order does not change the number or contiguity of blocks.
The common refinement has at most $2L_k-1$ nonempty blocks. Each block
fixes both $a$ and $b$ and hence contains only one origin. It follows
that $m\le2L_k-1=6\cdot2^k-5$.

This counts transcript blocks, not distinct outputs: the same $b$ or
$a$ may occur in several separated leaves. The two partitions are
mathematical partitions of the same origin class from two lawful
families of complete histories; no execution combines different cuts
or splices their sources. Finally, the $q$ nonempty attained classes
partition the $q^2$ allowed originals. Summing (NARC.9.1) gives
$q^2\le q(6\cdot2^k-5)$, proving (NARC.9.2). $\square$

## 10. An exact finite fixed-encoder all-lag criterion

**Definition 10.1 (origin-indexed native target separation).** Fix
public $q\ge1$ and the finite actual-query menu

$$
\mathcal M_q=\{E,P_2,P_3,\ldots,P_{3q+1}\}.
\tag{NARC.10.1}
$$

A finite state consists of a finite index set $I$ with integer ages
$n_i\ge0$ and targets $v_i$. Indices remain distinct when ages agree;
in particular, conflicting targets at the same age are not collapsed.
For $A\in\mathcal M_q$ and actual reply $r$, let $I_{A,r}$ contain
exactly the indices giving $r$ under (NARC.5.7). Restriction retains
each index's age and target. Define $D_0(I)$ to mean target constancy,
with empty states vacuous, and recursively

$$
\begin{aligned}
D_{j+1}(I)\quad\Longleftrightarrow\quad&
\text{the target is constant on }I\quad\text{or}\quad\\
&\exists A\in\mathcal M_q\,
\forall r\in\{\bot,\alpha,\beta,\mathsf b\},\quad
D_j(I_{A,r}).
\end{aligned}
\tag{NARC.10.2}
$$

An indexed constant-target state halts with that target. A witness of
the other alternative is a finite native tree whose next experiment
is $A$ and whose reply children are the indicated witnesses. Thus the
predicate preserves actual reply partitions and permits different
adaptive subtrees, rather than arbitrary four-way partitions.

**Theorem 10.2 (finite certification is equivalent to all-lag service).**
Fix any deterministic acquired encoder $e$ in Assumption 9.1 and a
budget $k\ge0$. Put $Z=q+1$. For each attained class $C_\gamma$, form
the two full origin-indexed states

$$
\begin{aligned}
S_R(\gamma)&=\bigl((Z+a-b,b)\bigr)_{(a,b)\in C_\gamma},\\
S_L(\gamma)&=\bigl((q+Z-a+b,a)\bigr)_{(a,b)\in C_\gamma}.
\end{aligned}
\tag{NARC.10.3}
$$

For nonnegative lags also form the at most $q$ complete boundary states

$$
S_0(z)=\bigl((z+a-b,b)\bigr)_
 {\substack{(a,b)\in C_{e(0,z)}\\b\le z}},
\qquad 0\le z<q.
\tag{NARC.10.4}
$$

For $\lambda=1$, all-lag recovery with at most $k$ actual Reads on
both visible regions exists exactly when $D_k$ holds on every state
in (NARC.10.3). For $\lambda=0$, it exists exactly when $D_k$ holds
on those states and every state in (NARC.10.4). The latter states
include the entire compatible fibers, not only their zero-age origins.
The finite menu (NARC.10.1) suffices for every certificate. This menu
bound is not a bound on the addresses used at unbounded runtime lags.

**Proof, native trees and necessity.** By induction on $j$, Definition
10.1 is equivalent to target separation by a depth-at-most-$j$ tree
using its menu. Every state tested here has ages in $[0,3q]$:
the right reference range is $[2,2q]$, the left reference range is
$[q+2,3q]$, and the boundary range is $[0,2q-2]$. Every descendant
inherits this bound. A threshold $t>3q+1$ has constant absence and
may be deleted. Every finite relative word otherwise has $E/P/S$
response geometry by Definition 5.3. Replace an $S_t$ node by the
actual $P_t$ and send replies $(\bot,\alpha,\beta,\mathsf b)$ to
$(\bot,\beta,\mathsf b,\mathsf b)$ before following its former
child. This refines its partition with the same call budget. Delete
root and visible-slot queries by the all-address correspondence of
Theorem 5.2, and delete any remaining constant nodes. The resulting
tree uses (NARC.10.1). This argument retains origin indices even if
two ages coincide, and proves that the finite predicate is exact for
each tested state.

Every reference state is a genuine whole acquired-input fiber at
$z=Z$, with its target coordinate determining the required lag by
subtraction from $Z$. Every boundary state is the complete right-visible
fiber at the entry $(e(0,z),\mathcal R^R_z)$ for $\lambda=0$;
it contains origin $(0,z)$ at lag zero. Theorem 5.2 realizes every
indexed alternative by its own original and legal continuation. An
all-lag controller restricted to one such entry therefore supplies
the required native decision tree. This proves necessity.

**Proof, positive translation.** Choose reference witnesses and delete
their $E$ nodes: every reference age is at least two, so all such
replies are branch. All remaining query nodes are actual $P_t$ with
$t\ge2$. At a later entry with normalized clock $z$, restrict the
appropriate reference tree to its exact fiber in Theorem 5.2. For each
of its origins the age changes by the same integer
$\Delta=z-Z$, while its target coordinate does not change. At a
reference $P_t$ node put $s=t+\Delta$. Its reply on the same origin
is the following partition of the actual age $n$:

$$
\widehat P_s(n)=
\begin{cases}
\bot,&n<s,\\
\alpha,&n=s,\\
\beta,&n=s+1,\\
\mathsf b,&n\ge s+2.
\end{cases}
\tag{NARC.10.5}
$$

This notation is an algebraic reply to be simulated; it does not add
an experiment to the native menu. On an actual positive support,
$n\ge1$, it has the following lawful implementations:

| Shifted threshold | Actual request | Reply supplied to the reference node |
| --- | --- | --- |
| $s\ge2$ | $P_s$ | unchanged actual reply |
| $s=1$ | $P_2$ | $\bot\mapsto\alpha$, $\alpha\mapsto\beta$, $\beta,\mathsf b\mapsto\mathsf b$ |
| $s=0$ | $E$ | unchanged actual reply |
| $s\le-1$ | no request | constant $\mathsf b$ |

For $s=1$, the absence cell of actual $P_2$ on positive ages contains
only $n=1$; its alpha cell is $n=2$, and all higher ages require
branch at the simulated node. For $s=0$, the only nonbranch positive
age is $n=1$, giving beta under both $E$ and (NARC.10.5). For
$s\le-1$, every positive age is at least $s+2$. These observations
prove all four identities pointwise. Every paid experiment is prefixed
by the actual hidden-slot address and uses (NARC.5.8). In particular,
the $s=1$ case requests actual $P_2$, never $P_1$.

Feed the implemented reply into the current reference node before
selecting its next child. Induction down the finite reference tree
shows that each actual origin follows exactly its reference transcript
after these reply maps. A skipped step still descends the finite tree,
and each paid step replaces at most one reference call. The final
reference target is therefore valid on the actual restricted fiber,
with at most $k$ paid Reads. This includes sparse fibers, conflicting
age indices and adaptive second or subsequent thresholds; if a
reference witness exists, its terminal target is constant on every
surviving index.

**Proof, zero boundary and sufficiency.** Left-hidden ages are always
at least $q$ by Theorem 5.2, so are positive. A right-hidden age equals
$a+\ell$ and is zero exactly when $a=0$ and $\ell=0$. This requires
$\lambda=0$, $z=b<q$ and label $e(0,z)$. These conditions are
recognizable from the acquired $z$, label and public encoder table;
no hidden-age test is used. On such an entry choose the separately
certified complete tree (NARC.10.4). All other entries have positive
hidden support and use the translated reference tree. In either case
the final target $v$ gives $\ell=z-v$, with the same actual original
retained as a compatible index throughout the actual replies.

At $n=0,s=1$, actual $P_2$ returns absence, whereas its positive
reply map would supply alpha instead of the required absence in
(NARC.10.5). Thus the positive translation cannot justify omission
of the boundary trees. The finite cases above exhaust that exception;
the translation proves all remaining, arbitrarily large lags. No
finite lag window is used as an all-lag inference. $\square$

**Proposition 10.3 (positive certificates can miss a complete zero fiber).**
For $q\ge13$, consider the symmetric class

$$
C_{\rm bad}=
\{(a,b)\in[0,q-1]^2:\max(a,b)=6\}\ \cup\
\{(A,0),(0,A):A\in\{10,11,12\}\}.
\tag{NARC.10.6}
$$

Both of its full reference target states at $Z=q+1$ have depth-two
native certificates. Nevertheless, if this is a code class, its
complete right-visible entry at $z=12$ under $\lambda=0$ admits no
two-read controller. This is an obstruction to that class and entry,
not to every encoder on the square or to positive-lag service.

**Proof.** In coordinates $u=a-b,v=b$, write $h=Z$ for the right
reference and $h=q+Z$ for the left reference, exchanging $a,b$ for
the latter. A $P_{h+s}$ partitions $u$ at $s,s+1$. At these reference
clocks all of the following thresholds are at least two. Use first
offset $1$, lower offset $-11$ after absence, and upper offset $4$
after branch. The first alpha and beta cells have targets $5,4$.
The lower second cells, in $(\bot,\alpha,\beta,\mathsf b)$ order,
have targets $(12,11,10,6)$; the upper second cells have targets
$(3,2,1,0)$. This follows from the three negative extras
$(-12,12),(-11,11),(-10,10)$, the base arm with $u\le0,v=6$,
and the positive base arm and target-zero extras. Symmetry supplies
the left reference. These are actual finite certificates for this class.

At $z=12$, every one of its nineteen origins has $b\le12$, so the
whole class is the complete fiber in Theorem 5.2. The ordered
hidden-age-to-target groups are

$$
\begin{array}{c|cccccccccc}
n&0&1&2&[6,12]&13&14&15&16&17&\{18,22,23,24\}\\ \hline
v&12&11&10&6&5&4&3&2&1&0.
\end{array}
\tag{NARC.10.7}
$$

Each target corresponds to lag $12-v$ on its own lawful fixed
original, with the same code and entire later row, reached hole and
singleton partition. There are ten ordered target runs. Every native
transcript leaf is an interval in this age order, so at least ten
nonempty target-constant leaves are required.

If the first informative request is $E$, it has two singleton cells
and one branch tail. One remaining request gives at most four leaves
on that tail, for at most six altogether. If the first informative
request is nonempty, Definition 5.3 makes both ages zero and one
absent. Their different targets force the remaining request on that
cell to be $E$: every nonempty relative word still merges them,
and root or visible-slot requests are constant. That child has at
most three leaves. The two possible singleton first cells contribute
at most two leaves, and the upper tail at most four, totaling at most
nine. An $S_t$ first request gives no more than this $P_t$ bound;
constant requests and early halts do not improve it. Ten runs cannot
be covered. This exhibits a necessary consumer of the complete zero
tests in Theorem 10.2 and of the column-gap condition below. $\square$

## 11. A genuinely acquired two-read code through seventeen labels

**Definition 11.1 (one symmetric master encoder).** For
$0\le a,b\le16$, put $A=\max(a,b)$ and $B=\min(a,b)$.
Normally set $e_{17}(a,b)=A$. Replace that value by $c$ exactly on
the following unordered pairs, including both orientations:

| Label $c$ | Reassigned $(A,B)$ |
| --- | --- |
| $0$ | $(16,B)$ for $0\le B\le6$ |
| $1$ | $(15,B)$ for $0\le B\le5$ |
| $2$ | $(13,3),(14,0),(14,1)$ |
| $3$ | $(12,0),(14,3),(14,4)$ |
| $4$ | $(12,2),(13,2),(14,2)$ |
| $5$ | $(11,1),(12,1),(13,1)$ |
| $6$ | $(10,0),(11,0),(13,0)$ |

For $1\le q\le17$, define $e_q$ by restriction to $[0,q-1]^2$.
The actual original remains $X_{a,b}=\langle T_a,T_{q+b}\rangle$;
its right offset is $q$, not seventeen. From the genuinely acquired
initial empty-cut row compute $a=c(T_a)$ and $b=c(T_{q+b})-q$
using the supplied acquired-literal clock. Export only $e_q(a,b)$
before the future region and lag are known. Discard the row, the two
coordinates and every other source-bearing field. The displayed
encoder table and all later certificate tables are public data common
to every source; they are not source-dependent surviving selections.

**Proposition 11.2 (alphabet and class geometry).** The encoder $e_q$
has exactly $q$ attained labels, the inherited minimum alphabet of
[NAR, Theorem 16.3][NAR]. Every one of its classes has distinct
differences $d=a-b$. In the master square, let $u=a-b,v=b$. For
$0\le c\le6$, class $c$ consists of its entire maximum-$c$ base

$$
\begin{cases}
-c\le u\le0,&v=c,\\
1\le u\le c,&v=c-u,
\end{cases}
\tag{NARC.11.1}
$$

and its listed symmetric extras. For $7\le c\le16$, put
$r=\min(c,9)$. Its class is exactly

$$
\begin{cases}
-r\le u\le0,&v=c,\\
1\le u\le r,&v=c-u.
\end{cases}
\tag{NARC.11.2}
$$

Smaller squares restrict these classes by deleting origins.

**Proof.** Every reassignment label satisfies $0\le c\le A$,
and $e_{17}(t,t)=t$. Thus a prefix square exports no label outside
$[0,q-1]$, and its diagonal attains every label in that interval.
The minimum-alphabet conclusion is the cited whole-current supplier,
without a new alphabet lower proof.

The seven reassignment rows contain $7+6+5\cdot3=28$ unordered
pairs. For $A=10,11,12,13,14,15,16$, respectively, they contain
all $A-9$ pairs with $B\le A-10$: the first five sets are read
directly from the five finite reassignment rows, and the last two are
the displayed stars. Hence they are exactly the pairs with $A-B\ge10$.
All other pairs keep their maximum. This proves (NARC.11.1)--(NARC.11.2).

The positive extra differences for labels $0,\ldots,6$ are,
respectively,

$$
[10,16],\ [10,15],\ \{10,13,14\},\ \{10,11,12\},\
\{10,11,12\},\ \{10,11,12\},\ \{10,11,13\}.
\tag{NARC.11.3}
$$

Each is distinct within its class and disjoint from the base
differences in $[-c,c]$. The reversed extras have their negative
differences, and the diagonal is the sole difference-zero point.
The normal classes have one point at each displayed $u$. Thus $d$
is injective in every master class and remains so upon restriction.
$\square$

**Definition 11.3 (oriented certificates and public pruning).** On a
right-visible entry set $(h,u,v)=(z,a-b,b)$; on a left-visible entry
set $(h,u,v)=(q+z,b-a,a)$. Symmetry of $e_q$ makes the same class
tables apply in both orientations. The exact candidate set is its
class restricted by $v\le z-\lambda$, and the hidden age and lag
are $h+u$ and $z-v$, by Theorem 5.2.

Write $Q(s)$ for the four-cell partition

$$
u<s,\qquad u=s,\qquad u=s+1,\qquad u\ge s+2,
\tag{NARC.11.4}
$$

in reply order $(\bot,\alpha,\beta,\mathsf b)$. When $h+s\ge2$
it is the actual hidden-slot-prefixed $P_{h+s}$ request. At other
thresholds this is partition notation only; the actual replacements
are specified below. Initially and after each reply, halt whenever
the surviving public candidates have constant $v$. A partition
constant on all remaining candidates can be followed locally without
a request. Both decisions use the finite candidate table and the
acquired entry, not a hidden tree or origin oracle.

**Lemma 11.4 (separated column triples with a lawful zero boundary).**
Let $B,A_1,A_2,A_3$ be nonnegative integers, with
$c\in\{4,5,6\}$, $0\le B<A_1$, $A_2=A_1+1<A_3$,
$A_1-B\ge10$, and public integer $q>A_3$.
Add the symmetric pairs $(A_i,B),(B,A_i)$, $i=1,2,3$, to the
maximum-$c$ base. Suppose $B=0$ if $c=6$, and suppose also

$$
B\ge1\quad\text{or}\quad A_3\ge A_2+2.
\tag{NARC.11.5}
$$

For this class, the target $v$ on every feasible fiber in Definition
11.3 is readable with at most two actual Reads under either lag
convention. The partition schedule is first $Q(1)$, then
$Q(B-A_2)$ after ambiguous absence or $Q(4)$ after ambiguous
branch, with the actual lower-threshold replacements in the proof.
This supplies classes $4,5,6$ of Definition 11.1 at

$$
(B;A_1,A_2,A_3)=
(2;12,13,14),\quad(1;11,12,13),\quad(0;10,11,13).
\tag{NARC.11.6}
$$

All three lower offsets equal $-11$. The lemma is a sufficient class
family, not a characterization of every two-read class or encoder.

**Proof.** The negative extras have $(u,v)=(B-A_i,A_i)$,
with distinct $u\le-10$. The base negative arm has $u\ge-c$
and target $c$, and positive extras have $(A_i-B,B)$ with $u\ge10$.
First $Q(1)$ has singleton middle targets $c-1,c-2$. On its lower
cell, $Q(B-A_2)$ gives targets $(A_3,A_2,A_1,c)$: its two
singleton positions are $B-A_2$ and $B-A_1$, and all base points
lie above these positions. On its upper cell, $Q(4)$ gives
$c-3,c-4,c-5$ in its first three positions when present. Its last
cell contains all positive extras, with target $B$. At $c=4$ the
beta base cell is absent, and at $c=5$ all three positions are
present. At $c=6$ the last cell also contains the base point $u=6$
with target zero, explaining the sufficient condition $B=0$.
Every terminal partition is therefore target-constant.

It remains to realize the thresholds on feasible actual fibers.
Right visibility with $h=0$ already has $v=0$ throughout and halts.
Otherwise $h\ge1$; this is also true on every left-visible fiber.
First $P_{h+1}$ and upper $P_{h+4}$ are then legal. A nonconstant
lower cell requires a negative extra, since all its base points have
target $c$. For right visibility such an extra has $v=A_i\le z$
and $h=z$, so $h\ge A_1$. Put $t=h+B-A_2$. Thus $t\ge B-1$.
If $t\ge2$, use actual $P_t$. If $t=0$, use actual $E$, whose
reply is exactly the partition at threshold zero.

The only possible negative threshold is $t=-1$, requiring $B=0$
and $h=A_1$. Then only the $A_1$ negative extra can be feasible;
it has age zero, while every lower base age is at least
$A_1-c\ge4$. Actual $E$ separates their targets. At $t=1$, every
feasible negative extra has age $h+B-A_i\ge B$, and the lower base
ages are again positive. If $B\ge1$ this whole lower support is
positive. If $B=0$, then $h=A_2+1$, and (NARC.11.5) excludes
the $A_3$ extra; the remaining extra ages are one and two. Thus
the support is still positive, and actual $P_2$ with the threshold-one
reply map of Theorem 10.2 realizes the desired partition. No $P_1$
is submitted. These cases exhaust $t<2$ whenever the lower target
is nonconstant. Feasibility restrictions can only remove points.

For left visibility, an ambiguous lower cell still requires
$z\ge A_1$, but $h=q+z$. Its threshold satisfies
$h+B-A_2\ge q+B-1\ge2$, so no exceptional lower request is
needed. Symmetry gives the same target partitions on both cuts.
The three instances (NARC.11.6) satisfy every hypothesis. The
consecutive zero-column triple of Proposition 10.3 fails precisely
the gap premise at its problematic clock, and that proposition
proves that dropping the premise wholesale is invalid. $\square$

**Theorem 11.5 (complete finite certificates for the master and every prefix).**
For every $1\le q\le17$, the encoder of Definition 11.1 satisfies
$D_2$ on both full reference states for every class, and on every
complete boundary state (NARC.10.4).

**Proof, coordinate reply certificates.** In the full master classes
use the following offset schedules. The middle first replies halt;
the lower or upper second experiment is needed only if its surviving
target is nonconstant.

| Class $c$ | First offset | Second after $\bot$ | Second after $\mathsf b$ |
| --- | --- | --- | --- |
| $0$ | $11$ | $0$ | $14$ |
| $1$ | $10$ | $-1$ | $13$ |
| $2$ | $1$ | $-11$ | $12$ |
| $3$ | $1$ | $-11$ | $10$ |
| $4,5,6$ | $1$ | $-11$ | $4$ |
| $7\le c\le16$ | $4$ | $1$ | $7$ |

Each pair of four-entry tuples below gives the targets of the second
reply cells after first absence and first branch, respectively.
$\varnothing$ denotes an empty cell, not an output target.

| $c$ | First $\alpha$ target | First $\beta$ target | Lower second $(\bot,\alpha,\beta,\mathsf b)$ | Upper second $(\bot,\alpha,\beta,\mathsf b)$ |
| --- | --- | --- | --- | --- |
| $0$ | $5$ | $4$ | $(16,0,\varnothing,6)$ | $(3,2,1,0)$ |
| $1$ | $5$ | $4$ | $(15,1,1,0)$ | $(3,2,1,0)$ |
| $2$ | $1$ | $0$ | $(14,\varnothing,13,2)$ | $(3,\varnothing,1,0)$ |
| $3$ | $2$ | $1$ | $(12,14,14,3)$ | $(0,4,3,0)$ |
| $4$ | $3$ | $2$ | $(14,13,12,4)$ | $(1,0,\varnothing,2)$ |
| $5$ | $4$ | $3$ | $(13,12,11,5)$ | $(2,1,0,1)$ |
| $6$ | $5$ | $4$ | $(13,11,10,6)$ | $(3,2,1,0)$ |

Here is a direct derivation of every exceptional row. Class zero has
negative extras $u=-16,\ldots,-10$ all with $v=16$, its base point
$(0,0)$, and positive extras $u=10,\ldots,16$ with $v=16-u$.
First offset eleven singles out targets five and four. Its lower
cell contains the negative group, the base, and $(u,v)=(10,6)$;
offset zero gives the displayed three nonempty target groups. Its
upper cell has $u=13,14,15,16$, which offset fourteen separates
as displayed. Class one similarly has negative extras
$u=-15,\ldots,-10$, all with target fifteen, base targets one at
$u=-1,0$ and zero at $u=1$, and positive extras
$u=10,\ldots,15$ with target $15-u$. Offsets ten, minus one
and thirteen give exactly its row.

Class two's negative extras are $(-14,14),(-13,14),(-10,13)$;
its positive extras are $(10,3),(13,1),(14,0)$. Its base lower
arm has target two, and its positive base points at $u=1,2$ have
targets one and zero. Offsets one and minus eleven partition the
lower group into targets fourteen, an empty singleton, thirteen and
two. Offset twelve on its upper extras gives three, an empty
singleton, one and zero. Class three's negative extras are
$(-12,12),(-11,14),(-10,14)$, and its positive extras are
$(10,4),(11,3),(12,0)$. Its lower base target is three, and its
upper cell also contains the base point $(3,0)$. The offsets in
its schedule now give its complete displayed row. Classes four
through six are exactly the instances of Lemma 11.4, which proves
their lower tuples and upper target mergers.

For a normal class (NARC.11.2), first offset four has middle targets
$c-4,c-5$. Its lower second offset one gives
$(c,c-1,c-2,c-3)$, and its upper second offset seven gives
$(c-6,c-7,c-8,c-9)$ wherever the indicated support points exist.
If $r<9$, the corresponding terminal positions are simply empty.
This proves target constancy in every occupied terminal cell for
every master class. Prefix restriction, and later entry feasibility,
only delete origins from these algebraic partitions.

**Proof, positive full reference realization.** At the right reference
$h=q+1$ and the left reference $h=2q+1$, every needed first
threshold is legal. Prune any target-constant state and any
constant-reply node. If a threshold exceeds $3q+1$, all tested
ages are below it, so its constant absence node is deleted as in
Theorem 10.2. The remaining first and second queries lie in the
finite menu whenever their thresholds are at least two.

For class zero, nontrivial extras first appear at $q=17$, so its
needed lower threshold $h$ is legal. For class one, $q\ge2$ gives
right lower threshold $h-1=q\ge2$, and the left threshold is
larger. For classes two through six, a nonconstant lower cell
requires a negative extra. Its smallest possible maximum coordinate
$A$ is, respectively, $13,12,12,11,10$. Since a prefix containing
it has $q\ge A+1$, the right lower threshold $h-11=q-10$
is at least two except at $q=11,c=6$. There its surviving lower
cell consists of the extra point of age two and target ten, and
base ages $6,\ldots,12$ of target six. Use actual $P_2$:
its alpha and branch cells separate these targets. The formal
threshold-one partition is not requested. For smaller prefixes
the corresponding lower cell is already target-constant. Every
needed left-reference lower threshold is legal, since an extra
requires $q\ge11$ and $h=2q+1$. All upper offsets are positive.
Normal-class offsets are positive as well. Thus the displayed
coordinate certificates give actual $D_2$ reference witnesses for
every prefix, including this sole positive-reference replacement.

**Proof, the complete zero-containing fibers.** The master boundary
labels are

$$
\bigl(e_{17}(0,z)\bigr)_{z=0}^{16}
=(0,1,2,3,4,5,6,7,8,9,6,6,3,6,2,1,0).
\tag{NARC.11.7}
$$

For any prefix take only $z<q$ and delete origins outside its square.
These are exactly the labels indexing (NARC.10.4), whose whole
fiber retains every class member with $b\le z$. Right visibility
has $h=z$, independently of the changed right offset $q$.
At $z=0$ all candidates have $v=b=0$, so halt. At every other
listed boundary clock the first threshold is legal; prune it if
constant. Upper second thresholds are positive and legal when
needed. The only nonconstant lower cells requiring $E$ in place
of the schedule's nonempty threshold are the following:

| $(c,z)$ | Complete remaining lower age-to-target groups | Actual second experiment |
| --- | --- | --- |
| $(1,1)$ | $\{0,1\}\mapsto1$, $2\mapsto0$ | $E$ |
| $(6,10)$ | $0\mapsto10$, $[4,10]\mapsto6$ | $E$ |
| $(6,11)$ | $0\mapsto11$, $1\mapsto10$, $[5,11]\mapsto6$ | $E$ |
| $(3,12)$ | $0\mapsto12$, $[9,12]\mapsto3$ | $E$ |

These groups follow from the base lower arms and the feasible negative
extras: at clock ten only $A=10$ survives in class six; at eleven
only $A=10,11$ survive there; at twelve only $(0,12)$ survives
among class three's negative extras. At $(1,1)$ no negative extra
with target fifteen is feasible, so the lower cell is exactly its
three-point base. Actual $E$ has separate alpha, beta and branch
cells and separates the stated targets in every row. Prefix
restriction can only remove some of these groups.

For exhaustion, at clocks $z=2,\ldots,6$ the label is $c=z$.
All negative extras have target greater than $z$, so the lower cell
has only its constant base target $c$ and halts. At clocks seven
through nine the normal-class positive offsets are legal. The
remaining four clocks have the following legal lower experiments
and target tuples:

| $(c,z)$ | Lower experiment | Lower $(\bot,\alpha,\beta,\mathsf b)$ targets |
| --- | --- | --- |
| $(6,13)$ | $P_2$ | $(13,11,10,6)$ |
| $(2,14)$ | $P_3$ | $(14,\varnothing,13,2)$ |
| $(1,15)$ | $P_{14}$ | $(15,1,1,0)$ |
| $(0,16)$ | $P_{16}$ | $(16,0,\varnothing,6)$ |

In the first row the feasible negative extra ages are zero, two and
three, with targets thirteen, eleven and ten; the base lower ages
are $[7,13]$. There is no age-one extra. In the second row the
negative extras have ages zero and one at target fourteen, and age
four at target thirteen, with lower base target two. The last two
rows are the star certificates already derived, translated to their
displayed clocks. Each occupied actual reply cell is target-constant.
Together with the four $E$ rows and the initial constant halt, this
exhausts (NARC.11.7), including every member of every complete
zero-containing fiber. Oversized constant-absence nodes are again
pruned, so these are witnesses using (NARC.10.1). $\square$

**Theorem 11.6 (exactly-$q$-label two-read service for every legal lag).**
For every $1\le q\le17$, Definition 11.1 supplies a genuinely
acquired deterministic encoder with exactly $q$ attained labels and
a decoder using at most two actual chronological original-root Reads,
for every original, both singleton visible regions, and separately
$\ell\ge0$ and $\ell\ge1$.

**Proof.** Proposition 11.2 proves the attained alphabet. Theorem 11.5
supplies both full positive certificates and every required complete
zero certificate. Invoke Theorem 10.2 with $k=2$, rather than
extrapolating a bounded selection of lag values. At runtime the
controller enumerates the public class, restricts it to the complete
acquired fiber of Theorem 5.2, and chooses either its certified zero
tree or the lawful translated reference tree using only the label,
visible region, normalized acquired clock and public lag convention.
Every actual reply is evaluated on the same stationary original's
current tree and is mapped, if required, exactly as in Theorem 10.2.
The original's index survives every restriction. The terminal common
target $v$ therefore equals that original's visible-origin coordinate,
and $z-v$ is its actual lag.

All requested words are the hidden-slot prefix followed by the
materialized representative (NARC.5.8), or the hidden-slot word
itself for $E$. No source-bearing part of the discarded initial row
is consulted, no $P_1$ is issued, and no age, equality or subtree
oracle is used. The right original offset changes to the actual $q$
in every prefix: its left-hidden full reference is $h=2q+1$, and
its later translated age is $q+z+b-a$. These are the states proved
in Theorem 11.5 and the correspondence used in Theorem 10.2;
smaller-$q$ source correctness is not asserted merely from a subset
of seventeen-offset sources. $\square$

## 12. Exact supported minima, task scope and resource correspondence

**Theorem 12.1 (supported call optima and the remaining two-read range).**
Let $K_{\min}(q,\lambda)$ be the minimum worst fresh-call count over
all exactly-$q$-label encoders and controllers in Assumption 9.1.
Under either lag convention,

$$
K_{\min}(q,\lambda)=
\begin{cases}
0,&q=1,\\
1,&2\le q\le6,\\
2,&7\le q\le17.
\end{cases}
\tag{NARC.12.1}
$$

Retaining the fixed coordinate $e(a,b)=b$ instead has exact worst
call count $K_+(q)$ of [AOF, Theorem 8.3][AOF], and supports two
calls exactly for $q\le10$. Every exactly-$q$-label encoder requires
more than two calls for $q\ge20$. Two-read feasibility for $q=18$
and for $q=19$ remains unresolved separately for $\lambda=0$ and
$\lambda=1$; neither a construction nor an exclusion for those
four cases follows from these results.

**Proof.** The zero and one optima in (NARC.12.1), including the
one-read impossibility for every $q\ge7$, are exactly the published
Theorem 7.5. Theorem 11.6 supplies the upper bound two through
seventeen; that published impossibility makes it sharp for
$7\le q\le17$. It does not assert that the particular master
encoder attains the one-call optimum at every smaller $q$.

For the fixed-$b$ comparison, right visibility determines the lag
from $z-b$ with no new call. On a left-visible fiber the compatible
$a$ values form a consecutive interval of at most $q$ integers,
and hidden ages $q+b+z-a$ form a positive consecutive interval
of the same size. Identifying its hidden age is equivalent to
recovering the required lag $z-a$, since $q,b,z$ are known.
The supplied positive interval theorem therefore gives worst price
at most $K_+(q)$. At $z=q$, every $a\in[0,q-1]$ survives under
either convention; its own lag $q-a\ge1$ realizes the same whole
left-visible row and fixed code $b$. The hidden-age interval is
$[q+b+1,2q+b]$, of length $q$. The all-address correspondence
of Theorem 5.2 makes the same supplier's lower bound applicable.
Thus this fixed encoder has exact price $K_+(q)$, and its
two-read capacity is $3\cdot2^2-2=10$. The relational code
improves that encoder-qualified range without contradicting it.

Finally, Theorem 9.2 at $k=2$ requires $q\le19$. This excludes
$q\ge20$ under both conventions. It is only necessary: even at
$k=1$ its allowance $q\le7$ is weaker than the supplied true
boundary $q\le6$. Neither it nor the sufficient construction
settles the four stated eighteen/nineteen cases. $\square$

**Proposition 12.2 (lag recovery leaves a different reconstruction task).**
Theorem 11.6 recovers the lag and the initial coordinate of the
subsequently visible slot. It does not require its two-read transcript
to identify the hidden initial coordinate or the full original tree.
For the stronger target of reconstructing the entire original pair,
exactly $q$ labels and $k$ native calls on both cuts necessarily satisfy

$$
q\le3\cdot2^k-2.
\tag{NARC.12.2}
$$

In particular, two-call original-profile reconstruction cannot hold
at $q=17$ with that alphabet, even though lag recovery does.

**Proof.** At $q=17$ take originals $(a,b)=(0,16)$ and $(1,16)$
at lag one. Both export label zero and have the same complete
right-visible row with exterior $T_{34}$, the reached left hole and
its singleton partition. Their normalized clock is $z=17$.
The certified class-zero tree first requests $P_{28}$ in the
hidden slot, the whole word $LR^{14}$, and after absence requests
$P_{17}$ there, the whole word $LLR^8$. Both actual hidden ages,
one and two, return absence on both requests. Their common terminal
target is $b=16$ and both outputs are $17-16=1$, but their initial
left trees and their current hidden trees differ. An additional Read
at the slot word $L$ gives beta versus branch. Thus the lag-constant
leaf really can retain a hidden spatial distinction.

For the stronger general target, use a full reference entry of
Theorem 9.2. Same-age conflicting originals cannot be separated;
otherwise its ordered-leaf argument bounds a class's nonempty leaves
by $L_k=3\cdot2^k-2$. Every successful reconstruction leaf must
contain a single original, rather than merely a common target
coordinate. Hence $|C_\gamma|\le L_k$, and summing over $q$
labels gives (NARC.12.2). At two calls it requires $q\le10$.
This is a necessary reconstruction bound, not an exact reconstruction
frontier under either convention.

The lost distinction is specific to the declared task transcript.
For the constructed code, difference injectivity means that code plus
both entire current ages identifies the original pair and lag. The
finite current-recovery supplier [NAR, Theorem 16.5][NAR] can acquire
the missing hidden-age information with additional native requests.
The two-read result neither denies that later recovery nor restores
an arbitrary original cut row without it. $\square$

**Definition 12.3 (the resource and source interpretation).** A
chronological fresh call is one submission of one fully materialized
original-root word. An $E$ request submits $L$ or $R$ and costs
one call. A $P_t$ request has word length $1+\lceil t/2\rceil$
using (NARC.5.8). Initial and later entire-row acquisition, parsing
of acquired literals, retained-label representation, public tables,
local candidate enumeration and arithmetic, changing workspace,
controller states, address production, total submitted length, lag
output representation and physical elapsed time are separate resource
coordinates. No numerical relationship among them is stipulated here.

The same-original pure-$\rho$ continuation, truthful entire-row
acquisition, causal export and actual discard are premises. A correct
lag output does not authenticate those premises or provide an absolute
epoch or a history archive. The cut and its spatial slot identity are
already part of the acquired entry; they are not inferred from the
retained label. The recovered temporal relation is the number of
intervening substitutions, not physical elapsed time.

**Proposition 12.4 (finite literal words with unbounded peaks).** The
decoder obtained from the certificates of Theorem 11.5 and translation
in Theorem 10.2 has finite materialized words at every promised input.
Writing $h=z$ for right visibility and $h=q+z$ for left visibility,
its submitted words satisfy

$$
|w|\le1+\left\lceil\frac{h+14}{2}\right\rceil.
\tag{NARC.12.3}
$$

For each fixed $2\le q\le17$, this specified decoder's worst
submitted length is unbounded over legal lags under either convention.
The call theorem supplies no uniform address cap, fixed finite Moore
realization or physical-resource bound.

**Proof.** All reference offsets in Theorem 11.5 are at most fourteen.
Its sole reference replacement uses threshold two at $h=12$, so
its offset is minus ten and satisfies the same bound. Translation
adds $z-Z$ to a reference threshold, giving at most the actual
$h+14$. A shifted threshold one uses actual $P_2$ instead; this
also satisfies the bound. Shifted threshold zero and the four
boundary replacements use $E$, with word length one; negative
shifted thresholds are skipped. The remaining boundary thresholds
are exactly the legal schedule thresholds and satisfy the same
offset bound. Formula (NARC.5.8) gives (NARC.12.3), and each
finite acquired clock produces a finite integer threshold and word.

For unboundedness use label one and left visibility at arbitrarily
large $z$, where its complete fiber is the full class. If $q<16$,
that class is its maximum-one base, with targets one at $u=-1,0$
and zero at $u=1$. Its first offset-ten partition is constant and
is pruned; its needed lower reference experiment translates to
$P_{h-1}$, whose length diverges with $z$. If $q\ge16$, class
one also contains the star extras at maximum fifteen. Its first
offset-ten experiment is nonconstant on the full class and
translates to $P_{h+10}$, again with divergent length. In both
cases sufficiently large $z$ makes every full-class alternative's
lag legal under either convention. These are lengths of actual
submitted words, not just hypothetical thresholds.

The decoder has input-dependent integer calculations and public
finite trees with separately constructed literal addresses and outputs.
A bound on tree depth alone does not bound those objects, their
production or physical service. The resource restrictions needed for
the fixed installed Moore statements of §4 are additional premises
and are absent from Assumption 9.1. $\square$

**Assumption 12.5 (mathematical supplier correspondence and limits).**
The native source and port correspond to `Source`, `substitution`,
`Address`, `Reply` and `readout` in the pinned suppliers cited in
Mathematical citation 8.1. Acquired coordinate parsing corresponds to
`rightClock` and `right_clock_iterate`; actual word replies correspond
to `right_clock_readout` and Definition 5.3. Whole-row equality
corresponds to `literalRecord`, `actualPartition` and
`canonicalRow_record_iff`. In particular, the singleton partition
does not expose a hidden-visible comparison. These semantic suppliers
do not already assert the adaptive class bound, finite all-lag
criterion or seventeen-label packing. Their distinct-address payment
or supplied-epoch decoder services are different contracts from the
chronological calls and unknown lag here.

The zero-error conflict method is literature-attested in Charpenay,
Le Treust and Roumy,
[*Optimal Zero-Error Coding for Computing under Pairwise Shared Side
Information*, arXiv:2211.03649v2, Definitions II.1, III.1 and IV.5,
and Theorem III.4](https://arxiv.org/html/2211.03649v2). A common
compatible side-information value with unequal required outputs is
the analogue of a common entire acquired entry with unequal lags.
Their prefix-free probabilistic block code, expected length and
asymptotic chromatic-entropy rate are not this attained-label,
worst-native-call objective; their graph conditions do not authorize
the reply partitions used here.

Restricted adaptive query geometry is literature-attested in Nowak,
[*The Geometry of Generalized Binary Search*, arXiv:0910.4397v5,
Theorem 1 and §V.A](https://arxiv.org/html/0910.4397v5). Its binary
hypothesis-identification bound assumes neighborliness and coherence,
and its point-test versus dyadic-test comparison distinguishes
different allowed query spaces. Here the hypotheses are compatible
origins, the task is only target-coordinate recovery, and allowed
queries have the supplied four-cell native geometry. No binary-search
bound or arbitrary partition is transferred numerically.

The repo-derived ordinary mathematical increment is the composition
of the native adaptive two-coordinate obstruction, the exact finite
criterion with its complete zero boundary, and the consumed symmetric
packing and actual certificates through $q=17$. The separate
[same-law stochastic predictive-quotient supplier, §§1--2](https://github.com/the-omega-institute/trureturing/blob/411caa2ef2896bc9c39706cf3d1239d4265f325d/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_PREDICTIVE_QUOTIENT_UNIFILAR_ERASURE_TAIL_AND_STRICT_SCOPE.md)
relates task defects to class-identification error; it supplies no
deterministic native-call or changing-source handoff theorem here.
No stochastic, thermodynamic or physical realization follows from
this correspondence, and no kernel verification, global priority or
unrestricted space/time/boundary/memory recovery claim is part of
these ordinary statements.

## 追加锚（本行以下为增补区）

## 13. Two-read equality and exact saturated zero-origin completion

**Definition 13.1 (class readability, runs and native saturation).**
Specialize Assumption 9.1 to $k=2$, retaining its entire acquisition,
causal export, discard, same-original pure-$\rho$ continuation and
stationary literal-Read contract. In particular the original family is
$X_{a,b}=\langle T_a,T_{q+b}\rangle$, $0\le a,b<q$, and an encoder
exports exactly $q$ attained labels from the genuinely acquired original
empty-cut row before either future choice. Its public table is common
to all originals. Every other source-bearing field is discarded.

A nonempty subset $C\subseteq[0,q-1]^2$ is *two-readable under
$\lambda$* if it can serve as one entire code class: both cut-specific
controllers recover the lag on every nonempty complete fiber of
Theorem 5.2 with at most two chronological actual Reads. This definition
does not require that the complement admits the other $q-1$ classes.
On right visibility the candidates, hidden ages and targets are
$b\le z-\lambda$, $z+a-b$ and $b$; on left visibility they are
$a\le z-\lambda$, $q+z-a+b$ and $a$. The whole rows, reached holes
and singleton partitions are precisely (NARC.5.3)--(NARC.5.6).
Each candidate has its own fixed-original history and indicated lag.
At a later transcript the support contains every candidate giving all
its actual replies. It is never replaced by a selected path of histories.

Whenever $d=a-b$ is injective, list $C=(p_0,\ldots,p_{m-1})$ in
strictly increasing $d$. Write $p_i=(a_i,b_i)$ and set

$$
\begin{aligned}
I_a&=\{i\in\{1,\ldots,m-1\}:a_i\ne a_{i-1}\},\\
I_b&=\{i\in\{1,\ldots,m-1\}:b_i\ne b_{i-1}\},\\
r_a&=1+|I_a|,\qquad r_b=1+|I_b|,\qquad
\sigma=|I_a\cap I_b|,\qquad \delta(C)=19-m.
\end{aligned}
\tag{NARC.13.1}
$$

Thus $r_a,r_b$ count maximal constant-coordinate runs, including
separated runs that revisit a value. They are not counts of different
targets. An $A$ edge changes only $a$, a $B$ edge changes only $b$,
and a $D$ edge changes both. Increasing $d$ makes every pure $A$
edge an increase of $a$ and every pure $B$ edge a decrease of $b$.
Their lengths are the corresponding positive integer increments.
A class of size nineteen is called *saturated*. This term refers to
the native two-read bound, not to a chain-partition $k$-norm.

**Theorem 13.2 (exact run defect and the ten-run equality condition).**
For every class two-readable at all positive lags, $d$ is injective,
$r_a,r_b\le10$, and

$$
\begin{aligned}
|C|&=r_a+r_b-1-\sigma,\\
\delta(C)&=(10-r_a)+(10-r_b)+\sigma.
\end{aligned}
\tag{NARC.13.2}
$$

For either coordinate having ten runs, its nine change positions are
three disjoint intervals of three consecutive edge positions. The
middle edge of each interval has $d$ increment one. Conversely,
for a $d$-injective class, these conditions for a particular ten-run
coordinate give a two-read full-reference certificate for that target.
If they hold for both coordinate targets, Theorem 10.2 gives both-cut
service at every positive lag. These statements allow repeated
nonadjacent coordinate values.

**Proof.** Use the collision and ordered-leaf argument of Theorem 9.2,
with $k=2$ and its genuine full fibers at $Z=q+1$. It supplies
$d$ injectivity and at most $L_2=10$ ordered interval leaves for
each target. Every coordinate change must be a leaf boundary, so
$r_a,r_b\le10$. Distinct consecutive origins change at least one
coordinate. Hence $I_a\cup I_b$ is the whole set of $m-1$ edge
positions. Inclusion-exclusion gives
$m-1=(r_a-1)+(r_b-1)-\sigma$, proving both identities. This uses
the supplied bound without introducing another general-$k$ result.

Consider a target with ten runs, ordered by increasing hidden age.
At the reference entry every age is at least two. Ten runs require
at least ten ordered leaves, and the supplied capacity permits exactly
ten. Consequently each leaf is exactly one maximal target run: no run
can be split and no two consecutive different runs can be merged.
After removal of entry-constant requests, a ten-leaf tree must have
a $P_t$ first request and a $P$ request on each of its two tails.
Indeed, an $S$ root has at most $4+1+4=9$ leaves, an $E$ root
is constant on these reference ages, and a missing root cell or a
tail with fewer than four cells also loses a leaf. Each singleton
root cell contains one origin by $d$ injectivity. A tail with four
cells must use $P$, with both adjacent singleton cells occupied.
Thus the ten run cardinalities, in this order, are

$$
(x_1,1,1,x_4,1,1,x_7,1,1,x_{10}),
\qquad x_1,x_4,x_7,x_{10}\ge1.
\tag{NARC.13.3}
$$

The ages of runs $2,3$ are consecutive, as are those of runs $5,6$
and $8,9$. Incoming, middle and outgoing edges around the two
singleton runs of each pair are three consecutive target changes.
These are exactly changes $1,2,3$, then $4,5,6$, then $7,8,9$.
The middle edge joins adjacent singleton ages and has $d$ increment
one. For the left target, increasing hidden age reverses the $d$
list. Reversal of ten runs preserves the three paired positions and
the middle-increment condition in the original $d$ order.

Conversely, the three change intervals make runs $2,3,5,6,8,9$
singletons. The unit middle increments make each indicated pair
consecutive in hidden age, in either orientation. At the full reference
query $P$ at the age of run $5$; after absence query at the age of
run $2$, and after branch at the age of run $8$. All thresholds
are at least two. The resulting leaves are precisely runs $1$ through
$10$, with their constant targets. This is an actual finite native
certificate using Definition 5.3, rather than an arbitrary ten-cell
partition. The positive translation and restriction in Theorem 10.2
serve every complete actual positive-lag fiber without additional
calls, including fibers that are not intervals in $d$. $\square$

**Theorem 13.3 (exact nineteen-point positive-lag normal form).**
A nineteen-point subset of the source square is two-readable on both
cuts at every positive lag if and only if, in increasing $d$ order,
its eighteen edges are six consecutive pure triples, three $AAA$
and three $BBB$, with the middle edge of each triple of length one.
Every other pure step has an arbitrary positive integer length,
subject only to membership in the square. Equivalently the second,
fifth and eighth changes of each coordinate have unit length.
All twenty macro words are permitted: if $U=AAA$ and $W=BBB$,
they are exactly the six-letter words with three $U$ and three $W$,
whose number is $\binom63=20$.

**Proof.** If the class is readable, (NARC.13.2) at $|C|=19$
forces $r_a=r_b=10$ and $\sigma=0$. Every edge is pure, so $a$
is nondecreasing and $b$ nonincreasing. Theorem 13.2 supplies three
consecutive change triples for each coordinate. Their disjoint union
is all eighteen edges, so they tile that list by the six stated blocks.
On a pure edge the $d$ increment is exactly its coordinate length;
the six middle increments are therefore unit lengths.

Conversely, each such word has nine changes of each coordinate,
three consecutive change triples with the required middle increments.
All pure lengths are positive, so $d$ increases strictly and the
vertices are distinct. The two full-reference trees of Theorem 13.2
and the positive part of Theorem 10.2 prove all positive lags.
There is no symmetry or endpoint-label hypothesis in either direction.
The count twenty chooses the three positions of $U$ among six;
it counts direction words, not coordinate embeddings or encoders.
$\square$

**Theorem 13.4 (exact nonnegative-lag first-step exclusion).**
Let $C=(p_0,\ldots,p_{18})$ have the normal form of Theorem 13.3,
with $p_0=(a_0,b_0)$. It is two-readable under $\lambda=0$ exactly
when

$$
\neg\bigl(a_0=0\ \text{and the first edge is a unit }B\bigr).
\tag{NARC.13.4}
$$

This additional condition concerns saturated classes. It is not a
criterion for arbitrary smaller or fused classes.

**Proof, the obstructed complete fiber.** In the excluded case the
right-visible entry at $z=b_0$ has the whole class as its fiber,
because $b$ is nonincreasing. Its first two origins are $(0,b_0)$
at lag zero and $(0,b_0-1)$ at lag one. Their hidden ages are zero
and one; their $b$ targets differ. Every origin gives the same complete
row $\mathcal R^R_{b_0}$, including its actual reached guard and
singleton partition. There are ten ordered $b$ runs with distinct
targets, so at least ten nonempty interval leaves are required.

A first $E$ gives at most two singleton leaves and four leaves on
its branch tail, totaling six. A first $S$ gives at most nine. For
any first $P_t$, $t\ge2$, ages zero and one are both absent.
The remaining query in this cell must be $E$: every nonempty
relative word still merges these two ages, and root or visible-slot
queries are constant. This cell has at most three leaves. The root's
two singleton cells and its other tail contribute at most $1+1+4$,
giving at most nine altogether. Early halts and constant requests
cannot improve these bounds. Hence no actual adaptive two-read
controller separates the complete fiber. This is the missing-$P_1$
obstruction, not a claim that the origins can never be distinguished
with more reads.

**Proof, all-clock sufficiency.** Left-hidden ages are always at least
$q$, so the positive-age translation in Theorem 10.2 serves that cut
even at lag zero. It also serves every right entry whose entire support
has positive hidden ages. It remains to consider a right fiber with
age zero. Such a point has $a=0$, lag zero and $b=z$ by Theorem
5.2. In a saturated class the fiber $b\le z$ is a suffix of complete
$b$ runs. Its zero-age point is its first point: strict increase of
$d$ and nonnegative actual ages exclude any earlier surviving point.
Thus the first surviving run, say $r$, begins at age zero.

Number the full class's ten $b$ runs by increasing $d$. Let $u,s,v$
be the predicted ages of singleton runs $2,5,8$, respectively,
computed as $z+d$ from their public points. Deleted runs may have
negative predicted ages. Their partners have ages $u+1,s+1,v+1$,
and

$$
s\ge u+3,\qquad v\ge s+3.
\tag{NARC.13.5}
$$

The ordinary full diagram has root $P_s$ and lower/upper tests
$P_u,P_v$. The following table gives actual tests for every possible
first surviving run at zero. A named tail is restricted by all previous
actual replies and the entire fiber. A constant-target tail halts.

| First surviving run $r$ | Predicted ages | Actual schedule |
| --- | --- | --- |
| $1$ | $u\ge2$ | $P_s$; $P_u$ on absence and $P_v$ on branch |
| $2$ | $u=0$, $s\ge3$ | $P_s$; $E$ on absence and $P_v$ on branch |
| $3$ | $u=-1$, $s\ge2$ | $P_s$; $E$ on absence and $P_v$ on branch |
| $4$ | $s\ge2$ | $P_s$; absence halts and branch uses $P_v$ |
| $4$ | $s=1$, $v\ge4$ | $P_2$; $E$ on absence and $P_v$ on branch |
| $5$ | $s=0$, $v\ge3$ | $E$; $P_v$ on branch |
| $6$ | $s=-1$, $v\ge2$ | $E$; $P_v$ on branch |
| $7$ | $v\ge2$ | $P_v$ |
| $7$ | $v=1$ | $E$; $P_2$ on branch |
| $8$ | $v=0$ | $E$ |
| $9$ | $v=-1$ | $E$ |
| $10$ | unrestricted | halt |

Here is the target verification and exhaustion of the table. If $r=1$,
strict integer ages give $u\ge1$. When $u=1$, run $1$ must consist
of the single age-zero point, and run $2$ is the next point at age
one. Its incoming edge changes $b$ and is pure by saturation, so it
is a unit $B$. Zero at $p_0$ gives $a_0=0,z=b_0$, exactly the
excluded case. Otherwise $u\ge2$, and all three diagram thresholds
are actual legal $P$ tests.

For $r=2$, the lower $E$ separates run $2$ at zero, run $3$ at
one and run $4$ at ages at least two. For $r=3$, it separates
run $3$ at zero from the remaining constant run-$4$ tail; its beta
and branch replies, if occupied, both have the run-$4$ target.
When $r=4$, run $5$ begins at an integer $s\ge1$. For $s\ge2$
the diagram's lower tail is constant. For $s=1$, actual $P_2$
puts only run $4$ at zero and run $5$ at one into absence; $E$
separates them. Its alpha reply is run $6$ at two, and its beta
reply, if occupied, is run $7$ at three. Its branch is separated
by legal $P_v$, since the run-$8,9$ pair starts at $v\ge4$.

For $r=5$, $E$ isolates runs $5,6$ at zero and one; its branch
contains runs $7$--$10$ and is separated by $P_v$. For $r=6$,
$E$ isolates run $6$ at zero, its beta belongs to run $7$ if
occupied, and $P_v$ separates its branch. For $r=7$, run $8$
starts at $v\ge1$. If $v\ge2$, one $P_v$ separates the constant
run-$7$ tail, the two singleton runs $8,9$, and run $10$. If
$v=1$, $E$ separates run $7$ at zero and run $8$ at one;
on its branch $P_2$ isolates run $9$ at two, while both higher
reply cells have run-$10$ target. For $r=8$, one $E$ separates
runs $8,9,10$. For $r=9$, its alpha isolates run $9$ and both
positive reply cells have run-$10$ target. For $r=10$ the whole
fiber has a constant target. These cases exhaust ranks $1$--$10$
and every integer spacing allowed by the diagram.

Each submitted $P$ has threshold at least two. Every $E$ is the
paid hidden-slot word, and each $P$ uses the fully materialized
hidden-slot-prefixed representative (NARC.5.8). No actual $P_1$
is requested. At every truthful transcript the same original remains
a candidate, and the final common $b$ is its own, giving its lag
$z-b$. The table covers all integer clocks with a zero-containing
fiber; Theorem 10.2 covers all remaining clocks. $\square$

## 14. Unrestricted nineteen-label constrained covers

**Definition 14.1 (the complete saturated path families).** In the
$19\times19$ square let $\mathcal P_t^+$ contain every nineteen-point
class of Theorem 13.3 containing $(t,t)$, for $0\le t\le18$.
The generation permits all twenty macro words, every initial point
and every positive integer outer step that stays in the square.
The six middle steps are unit. Equivalently choose ten increasing
$a$ values, ten decreasing $b$ values and a macro word, with the
second, fifth and eighth gaps of each coordinate equal to one,
then take its nineteen vertices. Retain all such embeddings containing
the anchor. Let $\mathcal P_t^0$ be the subfamily passing
(NARC.13.4). The superscripts $+$ and $0$ mean positive and
nonnegative lags, respectively.

A *constrained exact cover* chooses one $C_t$ from each corresponding
family, pairwise disjoint, with union the entire square. In finite
binary-variable notation the same condition is

$$
\sum_{t=0}^{18}\ \sum_{C\in\mathcal P_t^\lambda:\,p\in C}x_{t,C}=1
\quad(p\in[0,18]^2),\qquad x_{t,C}\in\{0,1\},
\tag{NARC.14.1}
$$

where $\mathcal P_t^1=\mathcal P_t^+$ and
$\mathcal P_t^0$ has the meaning above. A candidate has exactly
one diagonal point by strict increase of $d$, so the equations on
diagonal points already force one selected candidate per anchor.
Duplicate descriptions of the same subset are treated as one candidate.

**Theorem 14.2 (exact unrestricted encoder-cover equivalence).**
Under Definition 13.1, a $q=19$ encoder with both-cut two-read
service exists for $\lambda=1$ if and only if the families
$\mathcal P_t^+$ have a constrained exact cover. For $\lambda=0$
the same equivalence holds with $\mathcal P_t^0$.

**Proof.** Theorem 9.2 bounds each of the nineteen nonempty attained
classes by nineteen. They partition $19^2$ originals, so each has
exactly nineteen points. Theorems 13.3--13.4 give precisely the
appropriate class condition. Injectivity of $d$ allows at most one
diagonal point per class; nineteen diagonal points and nineteen classes
give exactly one in each. Relabel that class by its anchor $t$.
This is a bijective relabeling of the attained alphabet, not retention
of extra source information. It yields the asserted exact cover.

Conversely, an exact cover gives the public table $e(a,b)=t$ for
the unique selected $C_t$ containing $(a,b)$. The genuinely acquired
original empty-cut row computes that entry; export only $t$ and discard
the row and every other source-bearing field. Every label is attained
at $(t,t)$. The appropriate theorem supplies a reader for each entire
class, using only its public table, the acquired later row and earlier
actual replies. Those are exactly the complete fibers of Theorem 5.2.
Thus the cover defines a lawful encoder under the original native
contract, for every legal lag, with the two supplied cut controllers.
No endpoint rule, symmetry or selected family was imposed on an
arbitrary encoder in the forward direction. $\square$

**Theorem 14.3 (six boundary corners, unequal gates and incidence).**
In every cover of Theorem 14.2, write $e(t,t)=t$. Then:

1. Every point $(a,b)\in C_t$ satisfies
   $\min(a,b)\le t\le\max(a,b)$. Classes $C_0,C_1,C_2$ have
   macro order $BBB\,BBB\,BBB\,AAA\,AAA\,AAA$, with their
   minimum-coordinate corner exactly $(t,t)$. Classes
   $C_{16},C_{17},C_{18}$ have the reverse macro order and their
   maximum-coordinate corner exactly $(t,t)$. Each of these six
   L paths has two ten-point arms. Their nonmiddle gaps remain free.
2. There are distinct $m_+,m_-\in\{2,\ldots,16\}$ such that

$$
\begin{aligned}
e(i+1,i)&=\begin{cases}i,&i<m_+,\\i+1,&i\ge m_+,\end{cases}\\
e(i,i+1)&=\begin{cases}i,&i<m_-,\\i+1,&i\ge m_-,\end{cases}
\qquad 0\le i\le17.
\end{aligned}
\tag{NARC.14.2}
$$

   Consequently adjacent-diagonal asymmetry occurs exactly at
   $\min(m_+,m_-)\le i<\max(m_+,m_-)$, a nonempty interval.
   No symmetric encoder $e(a,b)=e(b,a)$ can work at $q=19$.
3. Every nonempty intersection of a class with a fixed row or column
   has size $1+3j$ with $0\le j\le3$. If $N_a$ counts classes
   meeting the line with fixed first coordinate $a$, and $M_b$
   those meeting the line with fixed second coordinate $b$, then

$$
\begin{gathered}
N_a,M_b\in\{4,7,10,13,16,19\},\\
\sum_{a=0}^{18}N_a=190=\sum_{b=0}^{18}M_b.
\end{gathered}
\tag{NARC.14.3}
$$

   For coordinates $0,1,2,16,17,18$ the corresponding incidence
   counts belong to $\{4,7,10\}$.

All these necessities hold under both lag conventions. They give
$15\cdot14=210$ ordered gate pairs as constraints, not 210 feasible
encoders or an exclusion of every nonsymmetric encoder.

**Proof, anchors and corners.** Before the anchor $(t,t)$, monotonicity
gives $a\le t\le b$; afterwards it gives $b\le t\le a$.
This proves the belt inequality without assuming labels are endpoints.
For $t\le2$, at most $t$ pure $A$ changes can precede the anchor,
since they increase $a$ by at least one from a nonnegative start.
At most $t$ pure $B$ changes can follow it. If an $A$ triple
preceded a later $B$ triple, the anchor would have to lie strictly
before completion of the former (otherwise three $A$ changes precede
it), and strictly after commencement of the latter (otherwise three
$B$ changes follow it). The two requirements contradict their order.
Thus every $B$ triple precedes every $A$ triple, giving $B^9A^9$.

Write its corner as $(u,v)$. Both $u,v\le t$, and one equals $t$,
because the anchor lies on one of the two arms. Each arm contains
ten distinct points. Two of these lower-corner paths cannot share
a corner's first coordinate: their ten-point fixed-first-coordinate
arms would intersect within a nineteen-point line. They cannot share
a corner's second coordinate for the same reason. For $t=0$ the
corner is $(0,0)$. At $t=1$, neither corner coordinate can be zero,
so the corner is $(1,1)$. At $t=2$, neither can be zero or one,
so it is $(2,2)$. Reflect both coordinates by $x\mapsto18-x$ and
reverse the path list. This preserves the normal form and disjoint
coverage and gives the three upper-corner assertions.

**Proof, independent gates and their inequality.** The belt makes each
adjacent-diagonal cell's label one of its two endpoint indices. All
eighteen labels on either band are different: within a class $d$
is injective, whereas a band has constant $d=1$ or $d=-1$.
A sequence of lower/upper choices cannot have an upper choice
followed later by a lower choice. At its first upper-to-lower transition,
positions $i$ and $i+1$ would both have label $i+1$. Thus each
band consists of a lower prefix followed by an upper suffix, with
a threshold in $\{0,\ldots,18\}$ and that threshold as its unique
missing label. The two bands may initially have different thresholds.
Class $C_2$, with minimum corner $(2,2)$, cannot contain $(1,2)$
or $(2,1)$, so both those cells have label one and both thresholds
are at least two. Class $C_{16}$ cannot contain $(16,17)$ or
$(17,16)$, so both have label seventeen and both thresholds are
at most sixteen.

Suppose both thresholds equal $m$, and put $t=m-1$. Equations
(NARC.14.2) force the consecutive $d=-1,0,1$ points

$$
(t,t+1),\quad(t,t),\quad(t+1,t)
\tag{NARC.14.4}
$$

into $C_t$. They are consecutive because differences are distinct
integers. This is a $B$-to-$A$ turn, hence a junction of triples.
The edge entering the anchor is the last $B$ in its triple, so the
previous middle $B$ edge is unit and forces $(t,t+2)$. The edge
leaving the anchor is the first $A$ in its triple, so the following
middle $A$ edge forces $(t+2,t)$. On the other hand $C_{m+1}$
contains consecutive points
$(m,m+1),(m+1,m+1),(m+1,m)$, an $A$-to-$B$ junction. Its
two neighboring middle edges force $(m-1,m+1)$ and $(m+1,m-1)$.
These are exactly the two extra points just forced into $C_t$.
All lie in the square because $2\le m\le16$. Disjointness is
contradicted, proving $m_+\ne m_-$. The asymmetry interval and
the symmetric-encoder exclusion follow directly from (NARC.14.2).

**Proof, joint row and column incidence.** On a saturated path the
first coordinate never returns after an $A$ change. Its intersection
with any fixed-first-coordinate line is consequently one run of
vertices, and all edges inside it are whole $B$ triples. Its size
is $1+3j$, $0\le j\le3$. The argument for fixed second coordinate
uses whole $A$ triples. Each class occupies ten distinct first
coordinates and ten distinct second coordinates.

In a nineteen-point line, summing the nonempty intersection sizes
makes its incidence count congruent to one modulo three. Each
intersection has at most ten points, so at least two classes meet
the line. These facts give precisely the displayed allowed incidence
counts. Double-counting class-line memberships gives nineteen times
ten in each direction. Each of the six boundary lines has a ten-point
arm of its corresponding corner class, leaving only nine points for
other classes, so its count is at most ten. These are simultaneous
necessary equations on one cover; separately satisfiable arms or
incidence lists do not supply a joint realization. $\square$

## 15. Eighteen-label defect budgets and nonmonotone fusion

**Theorem 15.1 (all defect allocations and the precise fusion case).**
For any encoder satisfying Definition 13.1,

$$
\sum_{\gamma}\delta(C_\gamma)=q(19-q).
\tag{NARC.15.1}
$$

At $q=18$ the total defect is eighteen. If no class is saturated,
all eighteen classes have size eighteen. More generally,

$$
\#\{\gamma:\delta(C_\gamma)=0\}
=\sum_{\gamma:\delta(C_\gamma)\ge2}
       (\delta(C_\gamma)-1).
\tag{NARC.15.2}
$$

An eighteen-point readable class has exactly one of

$$
(r_a,r_b,\sigma)=(9,10,0),\quad(10,9,0),\quad(10,10,1).
\tag{NARC.15.3}
$$

The first two cases are axis-monotone. The ten-run coordinate has
the three change triples and unit middle increments of Theorem 13.2;
readability of that coordinate alone does not assert readability of
the other nine-run target.

For a $d$-injective eighteen-point class with $(r_a,r_b,\sigma)=
(10,10,1)$, positive-lag two-readability on both cuts is equivalent
to the following normal form. Its seventeen edges consist of four
pure triples, two $AAA$ and two $BBB$, and one fused block

$$
AA\,D\,BB\qquad\text{or}\qquad BB\,D\,AA.
\tag{NARC.15.4}
$$

Before the one-edge overlap, there are three coordinate-change triples
of each kind. All six middle edges are unshared pure unit edges.
Every other pure length is an arbitrary positive integer. The shared
edge $D$ changes both coordinates and has
$\Delta a-\Delta b>0$; its coordinate changes need not have the
monotone signs. All vertices must belong to the source square.
If the class also has $a\ge1$ everywhere, this form suffices for
nonnegative lags. No general zero-origin iff for fused classes is
asserted by (NARC.15.4).

**Proof.** Sum $19-|C_\gamma|$ over the $q$ classes that partition
$q^2$ points. This gives (NARC.15.1). All defects are nonnegative
by Theorem 13.2. At $q=18$ they sum to eighteen over eighteen
nonempty classes. With no zero defect, each is at least one and
therefore exactly one. Subtracting eighteen from the defect sum
gives (NARC.15.2). It leaves saturated classes, both defect-one
geometries and every higher-defect allocation in the domain.

At size eighteen, (NARC.13.2) expresses one as three nonnegative
integers, giving exactly (NARC.15.3). When $\sigma=0$ every edge
is pure, so its sign follows from increasing $d$ and the class is
axis-monotone. The coordinate with ten runs obeys Theorem 13.2.

In the $(10,10,1)$ case that theorem gives three disjoint length-three
intervals of change positions for each coordinate. Their union has
seventeen positions and their intersection has one. Exactly one
$a$ interval and one $b$ interval overlap, at a single edge.
Two intervals of length three can intersect in exactly one position
only when it is the last position of one and the first of the other.
Thus this pair contributes one five-edge fused block of (NARC.15.4),
and the remaining four intervals are pure triples. The shared edge
is not a middle edge of either triple. Theorem 13.2 supplies all
six middle increments, which on pure edges are unit coordinate steps.
The sole conditions on the shared signs are that both changes are
nonzero and the difference increases.

Conversely, the fused diagram gives each coordinate three disjoint
consecutive triples of changes with unit middle increments. It has
nine changes of each coordinate, seventeen total edges and exactly
one double change. Increasing $d$ follows from the pure signs and
the stated condition on $D$. The full-reference trees of Theorem
13.2 separate each coordinate's ten runs, even if the shared edge
causes a coordinate to revisit a previous value. Theorem 10.2
translates them to every complete positive-lag fiber; no suffix
assumption is needed for nonmonotone classes. If $a\ge1$ everywhere,
right-hidden ages $a+\ell$ are positive also at zero lag, and left-hidden
ages are always positive. The same supplied translation then serves
both cuts under $\lambda=0$. $\square$

**Theorem 15.2 (a complete native cover domain at eighteen labels).**
For $q=18$, define $\mathcal A_t^\lambda$ to contain every nonempty
$d$-injective subset $C\subseteq[0,17]^2$ containing $(t,t)$ for
which $D_2$ of Definition 10.1 holds on both full-reference states
(NARC.10.3), and, when $\lambda=0$, on every state

$$
\bigl((z+a-b,b)\bigr)_{(a,b)\in C,\ b\le z}
\quad\text{with }(0,z)\in C,quad 0\le z\le17.
\tag{NARC.15.5}
$$

An eighteen-label two-read encoder exists exactly when one can choose
one member of each $\mathcal A_t^\lambda$, pairwise disjoint and
covering all $324$ points. Every such cover has (NARC.15.1)--(NARC.15.2).
This domain includes the two nine-run cases, the fused case, saturated
classes, and all permitted higher defects. It imposes neither a common
class size nor a common macro word or symmetry.

**Proof.** A lawful encoder has $d$ injective by Theorem 9.2. Its
eighteen diagonal points force exactly one diagonal point in each
class, so the classes can be indexed by $t$. Theorem 10.2 with
$k=2$ gives precisely the two reference tests and the complete
zero-containing fibers (NARC.15.5). Thus each class belongs to the
corresponding family. Conversely an exact cover defines the public
table and genuinely acquired exported label just as in Theorem 14.2.
The selected certificates and Theorem 10.2 supply all legal lags.
Each family member has only one diagonal point by $d$ injectivity,
so all eighteen labels are attained. The defect identities follow
from Theorems 13.2 and 15.1.

This is an exact finite predicate, not a geometric classification of
the nine-run target: its $D_2$ test retains the actual $E/P$ menu
and every indexed reply cell. In particular, satisfying the ten-run
coordinate conditions alone is not substituted for the second test.
For zero-containing smaller classes, the tests in (NARC.15.5) are
entire fibers, and (NARC.13.4) is not used as their replacement.
$\square$

**Proposition 15.3 (one positive-coordinate nonmonotone class with
literal service under both conventions).** For every $q\ge12$,
start at $p_0=(1,8)$ and apply the seventeen increments

$$
AA\,D\,BB\,AAA\,BBB\,AAA\,BBB,
\qquad A=(1,0),\quad B=(0,-1),\quad D=(2,1).
\tag{NARC.15.6}
$$

The eighteen vertices form a class two-readable at every legal lag
under each $\lambda\in\{0,1\}$. It is contained in no monotone
saturated path, even in a larger square. This supplies a class,
not a complete $q$-label encoder.

**Proof, vertices and entire entry.** Its vertices are

$$
\begin{aligned}
&(1,8),(2,8),(3,8),(5,9),(5,8),(5,7),\\
&(6,7),(7,7),(8,7),(8,6),(8,5),(8,4),\\
&(9,4),(10,4),(11,4),(11,3),(11,2),(11,1).
\end{aligned}
\tag{NARC.15.7}
$$

All coordinates lie in $[1,11]$ and $d(p_i)=i-7$, $0\le i\le17$.
The $a$ change positions are $1,2,3;6,7,8;12,13,14$; the $b$
positions are $3,4,5;9,10,11;15,16,17$. Thus $r_a=r_b=10$
and $\sigma=1$, with all middle edges unit. The two points
$(3,8),(5,9)$ are incomparable in the order with $a$ increasing
and $b$ decreasing. A monotone path cannot contain both, proving
the asserted failure of the monotone-deletion restriction.

If this is an encoder's entire preimage, initialize candidates to
the complete $F_R(C,z,\lambda)$ or $F_L(C,z,\lambda)$ of Theorem
5.2. Initially and after a reply, halt whenever the visible-origin
target is constant. Otherwise use the following schedule, with
$h=q+z$ for left visibility. Each second request is selected only
after the indicated actual first reply.

| Visible region | First experiment | Second after ambiguous $\bot$ | Second after ambiguous $\mathsf b$ |
| --- | --- | --- | --- |
| right | $P_{z+2}$ | $P_{z-4}$ | $P_{z+8}$ |
| left | $P_h$ | $P_{h-6}$ | $P_{h+5}$ |

Its complete whole-class target certificates are as follows. The
four-entry tuples use actual reply order
$(\bot,\alpha,\beta,\mathsf b)$, and conditional cells are intersected
with the first reply's support.

| Visible region | First $\alpha$ target | First $\beta$ target | Lower second targets | Upper second targets |
| --- | --- | --- | --- | --- |
| right, target $b$ | $6$ | $5$ | $(8,9,8,7)$ | $(4,3,2,1)$ |
| left, target $a$ | $7$ | $6$ | $(11,10,9,8)$ | $(5,3,2,1)$ |

For the right table, $n=z+i-7$, so the first threshold $z+2$
singles out $i=9,10$. Its lower tail is $i\le8$, and threshold
$z-4$ singles out $i=3,4$: indices $0,1,2$ have $b=8$,
$i=3$ has $b=9$, $i=4$ has $b=8$, and indices $5$--$8$
have $b=7$. Its upper tail is $i\ge11$, and $z+8$ singles
out $i=15,16$: indices $11$--$14$ have $b=4$, then targets
are $3,2,1$. For the left table, $n=h+7-i$. First $P_h$
singles out $i=7,6$. Its lower tail is $i\ge8$, and $h-6$
singles out $i=13,12$: indices $14$--$17$ have $a=11$,
followed in increasing age by $a=10,9$ and the $a=8$ group.
Its upper tail is $i\le5$, and $h+5$ singles out $i=2,1$:
indices $3$--$5$ have $a=5$, followed by targets $3,2,1$.
These calculations prove every table entry symbolically. Restriction
to the full compatible fiber only deletes indices from the certified
cells; it cannot introduce a second target into a cell.

**Proof, actual legality and all lags.** A nonempty right fiber has
$z\ge1+\lambda$, since the minimum $b$ is one. Its first and
upper thresholds are therefore at least three. The lower second
threshold is submitted only on an ambiguous first-absence cell.
All points of that cell with $b<8$ have the common target seven.
Ambiguity therefore requires a surviving point with $b\ge8$.
Its complete-fiber membership gives $z\ge8+\lambda$, so the
needed lower threshold satisfies $z-4\ge4+\lambda$.
On the left, a nonempty fiber has $z\ge1+\lambda$ and $q\ge12$,
so $h-6\ge7+\lambda$; every left threshold is legal as well.
Thus neither $P_1$ nor a virtual or negative test is ever submitted,
under either lag convention.

For each requested $t=2m$, materialize $w_t=R^m$, and for
$t=2m+1$, materialize $w_t=LR^m$, with $m\ge1$. Submit
the entire word $Lw_t$ on right visibility or $Rw_t$ on left
visibility to the actual stationary original root. These are the
literal requests of Definition 5.3, each costing one chronological
Read. Retain exactly the public candidates giving its actual reply.
The actual original belongs to the initial complete fiber and survives
every truthful reply. Each terminal cell has the displayed constant
origin $v$, so its output $z-v$ is that original's own legal lag.
The inequalities and reply identities hold for every integer $z$,
not just a finite lag window. All choices use only the attained label,
later acquired row, public class table, selected region and actual
earlier replies. Nothing consults the discarded original row or a
hidden-age port. No covering claim about the complement is made.
$\square$

**Proposition 15.4 (why the saturated diagonal belt is not a local
eighteen-point lemma).** A positive-lag two-readable eighteen-point
class in $[0,17]^2$ can contain $(11,11)$ and $(0,9)$. Thus the
anchor-belt conclusion of Theorem 14.3 cannot be transferred to
arbitrary readable defect-one classes as a candidate restriction in
Theorem 15.2.

**Proof.** Use the word (NARC.15.6), start at $(0,9)$, and replace
only its shared increment by $D=(9,2)$. Its first vertices are
$(0,9),(1,9),(2,9),(11,11),(11,10),(11,9)$; its remaining vertices
are $(12,9),(13,9),(14,9),(14,8),(14,7),(14,6),(15,6),(16,6),
$(17,6),(17,5),(17,4),(17,3)$. All lie in the square. Pure edges
have unit lengths and the shared edge has $d$ increment seven.
Theorem 15.1 proves positive-lag readability. The diagonal point
is $(11,11)$, yet at $(0,9)$ the proposed belt would require
$11\le\max(0,9)$, which is false. This is a counterexample to
the local transfer, not to a global eighteen-label theorem with
additional packing hypotheses. It supplies neither a complete encoder
nor a nonnegative-lag certificate for this auxiliary class. $\square$

## 16. Temporal alignment, selected boundary memory and the remaining cover

**Theorem 16.1 (the recovered original cut row and saturated residual).**
For any successful class reader above, the output recovers the complete
original row at the same selected cut. For right visibility this row
is

$$
R_{\{L\}}(X_{a,b})=
\bigl(\langle\square_L,T_{q+b}\rangle,\{\{L\}\}\bigr),
\tag{NARC.16.1}
$$

and for left visibility it is

$$
R_{\{R\}}(X_{a,b})=
\bigl(\langle T_a,\square_R\rangle,\{\{R\}\}\bigr).
\tag{NARC.16.2}
$$

This does not reconstruct the hidden original filling. More sharply,
at a full reference entry of a saturated class, every correct two-read
lag controller has a truthful terminal transcript compatible with at
least four different originals, all with the same recovered lag and
selected original cut row. Full original reconstruction with the same
alphabet and two-read budget is impossible at $q=18$ or $q=19$,
by the stronger-task bound of Proposition 12.2.

**Proof.** The certified terminal target is the initial coordinate of
the visible slot. Theorem 5.2 identifies that target as $b$ on the
right and $a$ on the left, with the acquired normalized clock minus
the target giving the actual lag. Substituting the recovered origin
in the original family yields (NARC.16.1) or (NARC.16.2), including
the same reached guard and full singleton partition. This is a
reconstruction from the acquired entry and actual replies; it is not
another acquisition or recovery of a previously unknown cut.

At a saturated full reference entry, Theorem 13.2 forces every
successful reader's ten leaves to be exactly its ten coordinate runs.
Six are singleton runs. Each other run has size $1+3j$: its interior
edges are whole opposite-coordinate triples. Across these four runs
the corresponding four nonnegative integers sum to three, since
the class has nineteen points. Hence one has size at least four.
Its origins have the same visible coordinate and, at this common
clock, the same lag; their hidden coordinates differ. They share the
received label, entire later row and actual terminal transcript, but
their hidden original trees are distinct. This proves a real residual
source ambiguity for every two-read lag controller on that entry.

Proposition 12.2 already proves that universal two-read full-original
reconstruction with exactly $q$ labels requires $q\le10$. Applying
that existing result to $q=18,19$ makes the stronger task impossible,
irrespective of whether their lag-recovery covers exist. Extra native
information can change that task: [NAR, Theorem 16.5][NAR] supplies
finite current recovery, and a $d$-injective public class together with
both current ages determines its original pair and lag. Such additional
acquisition or calls are not supplied by the two-read transcript.
$\square$

**Definition 16.2 (mathematical correspondences and separate resources).**
The exact semantic suppliers remain those of Mathematical citation
8.1 and Assumption 12.5. Their parameter correspondence here is
two ordered slots, original offsets $0,q$, actual free-magma source
$X_{a,b}$, substitution count $\ell$, literal original-root word,
four-valued constructor reply, and complete cut exterior plus actual
hole partition. The Lean source meanings are `Source` and
`substitution` in GenealogicalFiberTransport; `Address`, `Reply` and
`readout` in ActualTreeReadoutAcquisition; `rightClock`,
`right_clock_iterate` and `right_clock_readout` in DelayedOriginalReadout;
and `literalRecord`, `actualPartition` and `canonicalRow_record_iff`
in ActualCutPartitionDecoder. Acquired visible-literal parsing computes
$z$; it does not measure a hidden age. Theorem 9.2 supplies the
ordered reference bound, Theorem 10.2 the exact finite/all-lag bridge,
and Proposition 12.2 the stronger reconstruction boundary. None of
these semantic correspondences identifies the new geometric statements
with an existing kernel proof.

The ordered-search representation is literature-attested in Bruno,
De Prisco, De Santis and Vaccaro,
[*Bounds and Algorithms for Alphabetic Codes and Binary Search Trees*,
arXiv:2407.16443v1, §§I--II](https://arxiv.org/html/2407.16443v1).
Their alphabetic trees preserve the order of searched symbols, and
their comparison-search descriptions distinguish binary outcomes
from ternary outcomes. Here the ordered symbols are $d$-indexed
origins, terminal leaves are intervals, and the task is coordinate
recovery. Their probability-weighted average costs do not supply
our worst-depth-two four-reply capacity, two adjacent singleton cells,
missing-$P_1$ boundary or a grid partition. The allowed-query
distinction is also the primary point-test/dyadic-test comparison in
Nowak, [*The Geometry of Generalized Binary Search*,
arXiv:0910.4397v5, §V.A](https://arxiv.org/html/0910.4397v5),
already used in Assumption 12.5. Its binary hypothesis framework
does not authorize stronger native tests here.

After reversing the second coordinate, saturated classes are chains
in the coordinate-product order. The relevant primary definitions
are Liu and West, [*Duality for semiantichains and unichain coverings
in products of special posets*, §1 and Example 2.1](https://dwest.web.illinois.edu/pubs/semianch.pdf).
A unichain there is constant in one coordinate throughout, whereas
our saturated paths turn between coordinates. Its cover results do
not produce a native six-triple exact cover. Greene--Kleitman
$k$-saturation is equality between a chain partition's
$\sum_C\min(k,|C|)$ and the largest union of $k$ antichains,
as defined also in West, [*Poly-unsaturated Posets: The
Greene-Kleitman Theorem Is Best Possible*, Journal of Combinatorial
Theory A 41, 105--116](https://dwest.web.illinois.edu/pubs/polyuns.pdf).
That is different from saturation of our native ordered leaves.
Even ordinary equal-size chains are insufficient: the nineteen grid
rows themselves partition the square into nineteen nineteen-point
product-order chains, but have a constant coordinate and nineteen
runs of the other coordinate, violating Theorem 13.2. No cited
chain-cover or ordered-search theorem supplies the new native
zero filter, unequal gates or fusion geometry. Those are repo-derived
ordinary deductions under the stated contract; this correspondence
makes no global novelty claim.

The call resource is a chronological submission of one fully
materialized finite word. A hidden $E$ costs one call. A $P_t$
representative has whole-word length $1+\lceil t/2\rceil$, including
the hidden-slot prefix. The displayed witness thresholds grow with
the acquired clock. Initial and later whole-row acquisition, parsing
and storage, retained-label representation, public tables, changing
workspace, arithmetic, controller representation, address production
and total submitted length, output size and physical time are separate
resources. Two calls do not imply a uniform address bound or a finite
uniform Moore implementation. Time here is the count of pure-$\rho$
steps; space is ordered constructor structure; boundary is the supplied
singleton cut; retained memory is the exported source-dependent label.
These meanings do not assert a physical model.

**Definition 16.3 (the exact remaining mathematical gap).**
For nineteen labels the remaining question is existence of a cover in
(NARC.14.1), separately with $\mathcal P_t^+$ and $\mathcal P_t^0$.
The six boundary corners, the 210 ordered unequal gate pairs and
the incidence equations constrain that same cover. They are not
a construction, and their individual consistency is not sufficient.
A class-complete obstruction could, for each remaining gate pair,
give real cell weights $w_p$ and bounds $\mu_t$ valid for every
candidate of anchor $t$ compatible with that pair, such that

$$
\sum_{p\in C}w_p\le\mu_t\quad\text{for every such }C,
\qquad
\sum_{p\in[0,18]^2}w_p>\sum_{t=0}^{18}\mu_t.
\tag{NARC.16.3}
$$

A disjoint full cover would contradict this inequality by summing
over its actual classes. Its validity must include every allowed
macro word and integer gap, rather than a symmetric, endpoint,
unit-step or L-only subfamily. No such complete obstruction or
full cover is supplied here.

For eighteen labels the remaining question is a cover of the complete
families $\mathcal A_t^\lambda$ in Theorem 15.2, with total defect
eighteen. The geometric gaps include the native nine-run target
conditions in the two axis-monotone defect-one cases, the zero-containing
fibers of general fused classes, and compatibility of every permitted
mixture of saturated and higher-defect classes. The finite criterion
defines all of them without omitting a defect allocation; the fusion
witness does not solve their joint packing. Thus unrestricted
$q=18$ and $q=19$ whole-grid feasibility remains unresolved under
each convention.

In the broader alpha/beta programme, these results identify precisely
which retained source relation and fresh native replies can align the
current visible structure with its original coordinate, and thereby
recover the selected original boundary row and substitution count.
The saturated residual shows why this recovery can leave hidden
spatial distinctions in memory's original fiber. Recovering the other
original cut row or the full hidden filling demands further information.
The next gap is the complete compatible cover or its unrestricted
obstruction, followed by any additional hypotheses needed for stronger
mutual reconstruction. Neither that gap nor the full space/time/boundary/
memory programme is settled by the local class theorems.

## 追加锚（本行以下为增补区）

## 17. The acquired native entry and complete read/write memory

**Assumption 17.1 (causal code, entire entry and conditional services).**
Use the actual ordered-tree algebra, homomorphic substitution and
complete-row semantics of [NAR, Definitions 1.1--1.2][NAR-RW]. Thus

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
T_0=\alpha,\quad T_1=\beta,\quad
T_{n+2}=\langle T_{n+1},T_n\rangle=\rho^{n+2}\alpha.
\tag{NARC.17.1}
$$

The allowed originals are all
$X_{a,b}=\langle T_a,T_{16+b}\rangle$, $0\le a,b\le15$.
Genuinely acquire the entire initial empty-cut row, compute the
restricted encoder $e_{16}$ of Definition 11.1 from that row, and
export only its label before the future lag and visible region are
chosen. Discard the row, its parsed coordinates and every other
source-bearing field. Retain the acquisition, export, discard and
same-original pure-$\rho$ premises of Assumptions 5.1 and 9.1.
Require positive lags; the conditional fiber below also satisfies
the nonnegative-lag convention.

Condition on label $1$, visible region $R$, cut $\{L\}$, and genuine
acquisition of the entire later row

$$
\mathcal I=
\left(1,R,
 \bigl(\langle\square_L,T_{33}\rangle,\{\{L\}\}\bigr)\right).
\tag{NARC.17.2}
$$

Equality includes every literal exterior label and bracket, the
reached left hole and the complete singleton partition. The partition
supplies no hidden-visible comparison. The current actual tree is
stationary throughout capture and all subsequent native Reads.
Every finite original-root word is a legal constructor query, including
absent addresses, with replies in the order
$\mathcal A=(\bot,\alpha,\beta,\mathsf b)$.
Every invocation, including a repeated request, counts as one
chronological Read.

A separately supplied terminating compiler may use only this common
acquired entry and public source and encoder data. It installs one
common table and one common initial state for the entire compatible
fiber, then closes access to all mutable compilation inputs and
workspace. It cannot select a table using the unknown actual origin,
hidden age or lag. Acquisition, encoding, export, later capture,
parsing, compilation, installation and initialization are distinct
conditional services with separate costs.

**Proposition 17.2 (exact acquired label-one histories).** The inverse
class and the entire compatible histories of (NARC.17.2) are exactly

$$
\begin{aligned}
C&=e_{16}^{-1}(1)
 =\{(1,0),(1,1),(0,1)\}
   \cup\{(15,j),(j,15):0\le j\le5\},\\
\ell_{a,b}&=17-b\ge2,\qquad
n_{a,b}=17+a-b,\\
Y_{a,b}&=\rho^{\ell_{a,b}}X_{a,b}
 =\langle T_{n_{a,b}},T_{33}\rangle.
\end{aligned}
\tag{NARC.17.3}
$$

The following table lists every history; each original is continued
by its own indicated lag and remains the same source during its Reads.

| Origin $(a,b)$ | Actual original $X_{a,b}$ | Lag $\ell_{a,b}$ | Actual current source $Y_{a,b}$ |
| --- | --- | --- | --- |
| $(0,15)$ | $\langle T_0,T_{31}\rangle$ | $2$ | $\langle T_2,T_{33}\rangle$ |
| $(1,15)$ | $\langle T_1,T_{31}\rangle$ | $2$ | $\langle T_3,T_{33}\rangle$ |
| $(2,15)$ | $\langle T_2,T_{31}\rangle$ | $2$ | $\langle T_4,T_{33}\rangle$ |
| $(3,15)$ | $\langle T_3,T_{31}\rangle$ | $2$ | $\langle T_5,T_{33}\rangle$ |
| $(4,15)$ | $\langle T_4,T_{31}\rangle$ | $2$ | $\langle T_6,T_{33}\rangle$ |
| $(5,15)$ | $\langle T_5,T_{31}\rangle$ | $2$ | $\langle T_7,T_{33}\rangle$ |
| $(0,1)$ | $\langle T_0,T_{17}\rangle$ | $16$ | $\langle T_{16},T_{33}\rangle$ |
| $(1,1)$ | $\langle T_1,T_{17}\rangle$ | $16$ | $\langle T_{17},T_{33}\rangle$ |
| $(1,0)$ | $\langle T_1,T_{16}\rangle$ | $17$ | $\langle T_{18},T_{33}\rangle$ |
| $(15,5)$ | $\langle T_{15},T_{21}\rangle$ | $12$ | $\langle T_{27},T_{33}\rangle$ |
| $(15,4)$ | $\langle T_{15},T_{20}\rangle$ | $13$ | $\langle T_{28},T_{33}\rangle$ |
| $(15,3)$ | $\langle T_{15},T_{19}\rangle$ | $14$ | $\langle T_{29},T_{33}\rangle$ |
| $(15,2)$ | $\langle T_{15},T_{18}\rangle$ | $15$ | $\langle T_{30},T_{33}\rangle$ |
| $(15,1)$ | $\langle T_{15},T_{17}\rangle$ | $16$ | $\langle T_{31},T_{33}\rangle$ |
| $(15,0)$ | $\langle T_{15},T_{16}\rangle$ | $17$ | $\langle T_{32},T_{33}\rangle$ |

**Proof.** Definition 11.1 normally returns $\max(a,b)$. Its unchanged
maximum-one base is precisely $(0,1),(1,0),(1,1)$. The only
reassignment to label one is $(\max(a,b),\min(a,b))=(15,j)$,
$0\le j\le5$, in both orientations. Its label-zero star at maximum
sixteen is outside the restricted square, and all other reassignment
labels differ from one. Hence the displayed fifteen-element set is
the exact inverse class, without an all-label decoder premise.

The supplied acquired-literal clock satisfies
$c(\alpha)=0$, $c(\beta)=1$,
$c(\langle s,t\rangle)=2+c(t)$ and $c(T_m)=m$.
The genuinely acquired original row therefore computes
$a=c(T_a)$ and $b=c(T_{16+b})-16$ before the future choice.
The code is a finite deterministic function of that acquired row;
the parsed coordinates do not survive its export and discard.

For a member of $C$, homomorphism at lag $17-b$ gives exactly the
listed $Y_{a,b}$. Both original-root slots are reached, and replacing
the entire left filling leaves $\langle\square_L,T_{33}\rangle$.
One reached hole has precisely the partition $\{\{L\}\}$,
independently of its filling. Thus every listed history realizes the
entire row, rather than just its clock.

Conversely, a history with this entry has original in $C$ because
its exported label is one. Its visible literal must obey
$T_{16+b+\ell}=T_{33}$. Applying the clock gives
$16+b+\ell=33$, so $\ell=17-b$ and $a+\ell=17+a-b$.
There is no other lag for that original and no other compatible
original. This is both directions of Theorem 5.2 specialized to
$q=16,z=17$; all $b\le15$ meet its feasibility restriction under
either lag convention. The definition of the encoder and this local
fiber calculation require neither the full Theorem 11.6 nor any
packing conclusion of §§13--16. $\square$

**Definition 17.3 (proof coordinates and the lag target).** The fifteen
distinct hidden ages and their visible-origin target function are

$$
\begin{aligned}
D&=\{2,3,4,5,6,7,16,17,18,27,28,29,30,31,32\},\\
\tau(n)&=
\begin{cases}
15,&2\le n\le7,\\
1,&n=16,17,\\
0,&n=18,\\
32-n,&27\le n\le32,
\end{cases}
\qquad g(n)=17-\tau(n),\\
D_L&=\{2,3,4,5,6,7,16,17,18\},\qquad
D_U=\{29,30,31,32\}.
\end{aligned}
\tag{NARC.17.4}
$$

The required output is the complete numeric lag $g(n)$, with image
$\{2,12,13,14,15,16,17\}$. Distinct $\tau$ values are exactly
distinct required outputs. The coordinates $n,\tau$ parametrize
actual histories for proofs; they are not observer inputs. In
particular the task does not require identifying all fifteen ages.

**Assumption 17.4 (all installed states and immediate writes).**
Impose the complete Moore discipline of Assumption 4.1 and
[AOF, Definition 10.1][AOF-RW] on the arbitrary-code entry of
Assumption 17.1. A table has finite disjoint running and halting
sets $K=Q\sqcup H$, one common initial state $R$, a fixed fully
materialized original-root word $\operatorname{addr}(s)$ for each
$s\in Q$, a total map $\operatorname{next}:Q\times\mathcal A\to K$,
and one fixed complete natural-number output at each $h\in H$.
It must first halt correctly after at most two chronological Reads
on each of the fifteen actual sources. All installed states count,
including unreachable, redundant and unused states.

After installation the current state is the entire mutable accessible
configuration. There is no separately accessible input code or row,
reply latch, program counter, phase, clock, history, mutable selector,
address register, output accumulator or arithmetic decoder. The
installed address, transition and complete-output table is immutable,
with separately supplied reading and output services and separately
charged storage. There is no free control step between Reads.

For the writable variant additionally impose [FIB, Definition
45.1][FIB-RW]: one fixed-length binary word without adjacent ones
is the entire mutable configuration. The current word and the actual
reply choose that same installed word or one legal bit flip immediately,
then discard the reply. The next instruction is selected solely by
the updated word. There is no intermediate write instruction or
additional write phase. Initialization, immutable-table access,
Read execution, atomic response writing and complete output are
conditional services; legal names alone supply none of them physically.
All configuration needed by a proposed device must satisfy this
complete-state contract to receive the bounds below.

This combines the arbitrary-code fiber and two-Read budget of
Assumption 9.1 with an additional finite Moore restriction. It does
not substitute $e_{16}$ for the fixed reference $e=a_0$ in Theorem
4.2, or transfer AOF's interval age-identification numerical optima.
The acquisition and compilation phases have their own memory and
cost contracts; the writable restriction here concerns recovery
after complete installation.

**Definition 17.5 (optimization and actual supported edges).** Let
$\mathfrak M_2$ be all tables satisfying Assumption 17.4's abstract
contract on this exact entry. Let $\mathfrak W_2$ be those also
satisfying its immediate-write contract, allowing arbitrary finite
word lengths and counted state refinement. Define

$$
M_2=\min_{\mathcal K\in\mathfrak M_2}|K|,\qquad
W_2=\min_{\mathcal K\in\mathfrak W_2}|K|,\qquad
L_2=\min_{\mathcal K\in\mathfrak W_2}d(\mathcal K).
\tag{NARC.17.5}
$$

In $L_2$ the number of installed states ranges over every finite
budget. Write $L_{11}$ for the length minimum restricted to exactly
eleven installed states.

The actual support graph $G_{\mathcal K}$ has every installed state
as a vertex. It has an undirected edge $\{s,t\}$, $s\ne t$, exactly
when some allowed original uses that response transition on its own
actual stationary run. Empty-support states remain vertices.
For a writable table, its complete words give an injective
edge-preserving map to

$$
\Gamma_d=
\bigl(\{w\in\{0,1\}^d:w_iw_{i+1}=0\ (1\le i<d)\},
       \{\{w,w'\}:d_H(w,w')=1\}\bigr).
\tag{NARC.17.6}
$$

This is the exact-supported version of [FIB, Definitions 45.3 and
Theorem 45.4][FIB-RW]. Neither induced nor isometric preservation
is required. Ambient legal words without installed instruction rows
are not installed states; adding such rows makes them count.

## 18. Universal native query rigidity and the actual degree path

**Theorem 18.1 (forced queries at every finite state budget).**
Every table in $\mathfrak M_2$ has distinct reached running states
$R,A,B$ with hidden-relative response functions respectively
$P_{27},P_{16},P_{30}$. The first absence and branch successors
are $A$ and $B$. Its actual support contains

$$
A-R-B,\qquad
\deg_{G_{\mathcal K}}(A)\ge4,\qquad
\deg_{G_{\mathcal K}}(B)\ge5.
\tag{NARC.18.1}
$$

These requirements hold over all finite literal addresses, all
installed-state budgets, shared successor configurations, early
halts and installed states with empty support.

**Proof, all-address correspondence.** Every original-root word is
$\varepsilon$, $Rp$ or $Lp$. The first is constantly branch on
$\langle T_n,T_{33}\rangle$; $Rp$ is evaluated on the same
$T_{33}$ throughout the fiber, including when its reply is absence.
The reply at $Lp$ is precisely the native relative reply at $p$ on
that origin's actual $T_n$.

Apply Definition 5.3 and [AOF, Definition 8.2][AOF-RW], including
their proper-prefix reach guard. For completeness of the parameter
correspondence, give $L$ weight one and $R$ weight two. If $p$
is nonempty, traversal is possible exactly when
$n\ge w(p^-)+2$, where $p^-$ deletes the last letter. All earlier
pre-edge branch guards are weaker because prefix weights increase.
When traversal is possible its filling is $T_{n-w(p)}$. A final
$R$ gives $t=w(p)\ge2$ and response $P_t$; a final $L$ gives
$t=w(p)+1\ge2$ and response $S_t$. An empty suffix gives $E$.
Their supplied functions are

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\ \hline
E&\text{never}&n=0&n=1&n\ge2\\
P_t&n<t&n=t&n=t+1&n\ge t+2\\
S_t&n<t&\text{never}&n=t&n\ge t+1.
\end{array}
\tag{NARC.18.2}
$$

Thus every arbitrary relative literal is accounted for. In particular
there is no $P_1$: the weight-one word $L$ gives $S_2$.
$E$ is constant on $D$. The proof has not replaced a literal Read
by an age or subtree oracle, nor limited the length of allowed words.

**Proof, one remaining Read and the lower tail.** At a running state
entered after the first Read, every supported successor after its
Read must halt; otherwise that source would issue a third Read.
Equal actual replies have one fixed successor and one fixed complete
output. Its whole arriving support must therefore be target-constant
in each reply cell, and can contain at most four distinct targets.
Merged arrivals strengthen this condition; extra installed states
do not create extra replies or another allowed phase.

On $D_L$, a $P_s$ with $s\le15$ gives branch at both ages
$17,18$, whose targets are $1,0$. A $P_s$ with $s\ge17$ gives
absence at both ages $2,16$, whose targets are $15,1$. Consequently
only $P_{16}$ can work. It does work, with targets
$(15,1,1,0)$ in the four reply cells. For $S_s$, separating
$17,18$ requires $s\ge17$, while separating $2,16$ requires
$s\le16$, an impossibility. Constants, including $E$, fail as well.
This forces the response function, without requiring a unique literal
spelling of it.

**Proof, the initial query.** Seven distinct lags prevent an initial
halt. A constant first query leaves seven targets for one remaining
Read and fails. For first function $P_t$ with $t\le26$, its branch
cell contains ages $28,29,30,31,32$ with five distinct targets
$4,3,2,1,0$. For $t\ge29$, its absence cell contains
$2,16,18,27,28$ with five distinct targets $15,1,0,5,4$.
Neither cell can be served by a halt or one four-valued Read.
At $t=28$, its absence cell contains $D_L$ and age $27$.
A remaining solver must solve $D_L$, so must use $P_{16}$;
but that query merges $18,27$ in branch with targets $0,5$.
Thus only $P_{27}$ survives.

For first function $S_t$, $t\le27$ puts the same five upper targets
in branch, $t\ge29$ puts the same five lower targets in absence,
and $t=28$ has the same failed $D_L$-plus-$27$ absence cell.
These cases exhaust all $S_t$, including thresholds larger than
every supported age. Along with the constant queries already
excluded, they exhaust every original-root literal.

**Proof, the upper tail and distinct states.** $P_{27}$ partitions
the actual ages into $D_L,\{27\},\{28\},D_U$ in reply order.
Both tails are target-nonconstant, so their destinations $A,B$ run.
$A$ must have function $P_{16}$. On $D_U$ the four targets
$3,2,1,0$ are distinct, so constants and all $S_s$, which have
at most three realized replies, fail. A $P_s$ with $s\le29$
merges $31,32$ in branch; a $P_s$ with $s\ge31$ merges $29,30$
in absence. Hence $B$ must have function $P_{30}$, which works.
One fixed literal has one function from (NARC.18.2); its necessary
parameters on these supports are different. Therefore $R,A,B$ are
pairwise distinct. Equivalently, merging $A,B$ would ask one
remaining four-valued query to serve the five targets in
$D_L\cup D_U$.

**Proof, actual neighborhoods and stationarity.** Actual lower and
upper origins witness edges $R-A$ and $R-B$ of the same installed
table. $A$'s second Read must enter at least three distinct halts,
for complete lags $2,16,17$. These halts are disjoint from running
$R$, so $A$ has at least four distinct neighbors. $B$ must enter
four distinct halts, for $14,15,16,17$, and has $R$ as a fifth
distinct neighbor. Halt duplication cannot decrease either count.
Root singleton origins may use extra states or halt early without
removing any of these actual edges.

If any one stationary source revisits the same complete running
state, determinism repeats its entire future query, reply and
successor sequence. It cannot subsequently have a first halt.
Thus self updates or reachable repeated-state cycles cannot supply
an uncounted phase or clock. This does not require the undirected
union of edges from different source runs to be a tree. Extra or
unreachable states remain counted but cannot weaken the forced
path or its neighborhoods. $\square$

## 19. One exact same-source read/write certificate

**Definition 19.1 (eleven complete words and immutable instructions).**
Install the following running rows. Columns after the address give
successors in the reply order $\bot,\alpha,\beta,\mathsf b$.

| Running state | Complete mutable word | Complete original-root address | Length | $\bot$ | $\alpha$ | $\beta$ | $\mathsf b$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $R$ | `000000` | `LLRRRRRRRRRRRRR` | $15$ | $A$ | $H_5$ | $H_4$ | $B$ |
| $A$ | `001000` | `LRRRRRRRR` | $9$ | $H_{15}$ | $H_{1L}$ | $H_{1L}$ | $H_0$ |
| $B$ | `100000` | `LRRRRRRRRRRRRRRR` | $16$ | $H_3$ | $H_2$ | $H_{1U}$ | $H_0$ |

These are the fully materialized original-root representatives
$Lw_{27}=LLR^{13}$, $Lw_{16}=LR^8$, $Lw_{30}=LR^{15}$ of
Definition 5.3. The actual submitted objects are the displayed
literal strings; powers and query indices are mathematical notation.
Install the following complete-output halt rows, with no Read or
response transition at a halt.

| Halt state | Complete mutable word | Installed complete lag output | Exact hidden-age support |
| --- | --- | --- | --- |
| $H_0$ | `101000` | $17$ | $\{18,32\}$ |
| $H_5$ | `010000` | $12$ | $\{27\}$ |
| $H_4$ | `000100` | $13$ | $\{28\}$ |
| $H_{15}$ | `001010` | $2$ | $\{2,3,4,5,6,7\}$ |
| $H_{1L}$ | `001001` | $16$ | $\{16,17\}$ |
| $H_3$ | `100100` | $14$ | $\{29\}$ |
| $H_2$ | `100010` | $15$ | $\{30\}$ |
| $H_{1U}$ | `100001` | $16$ | $\{31\}$ |

The common initial word is `000000`. State names are proof labels.
The $H_j$ instruction already contains the complete number $17-j$;
no subtraction or target lookup is performed after entry. The two
states bearing subscript one have the same numeric output and
different complete control words. Only these eleven words have
installed instruction rows.

**Proposition 19.2 (all fifteen actual first-halt traces).** Under
Assumptions 17.1 and 17.4's conditional services, Definition 19.1
is a correct immediately writable controller. Its full traces are
as follows. An ordered list of addresses means chronological
submissions, and an ordered word path includes its first halt.
Every row refers to the one actual $Y_{a,b}$ of Proposition 17.2.

| Origin $(a,b)$ | Submitted actual literals in order | Actual replies in order | Complete word path | First halt | Complete output | Reads | Response writes | Peak | Sum |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $(0,15)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `000000` → `001000` → `001010` | $H_{15}$ | $2$ | $2$ | $2$ | $15$ | $24$ |
| $(1,15)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `000000` → `001000` → `001010` | $H_{15}$ | $2$ | $2$ | $2$ | $15$ | $24$ |
| $(2,15)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `000000` → `001000` → `001010` | $H_{15}$ | $2$ | $2$ | $2$ | $15$ | $24$ |
| $(3,15)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `000000` → `001000` → `001010` | $H_{15}$ | $2$ | $2$ | $2$ | $15$ | $24$ |
| $(4,15)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `000000` → `001000` → `001010` | $H_{15}$ | $2$ | $2$ | $2$ | $15$ | $24$ |
| $(5,15)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `000000` → `001000` → `001010` | $H_{15}$ | $2$ | $2$ | $2$ | $15$ | $24$ |
| $(0,1)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\alpha$ | `000000` → `001000` → `001001` | $H_{1L}$ | $16$ | $2$ | $2$ | $15$ | $24$ |
| $(1,1)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\beta$ | `000000` → `001000` → `001001` | $H_{1L}$ | $16$ | $2$ | $2$ | $15$ | $24$ |
| $(1,0)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\mathsf b$ | `000000` → `001000` → `101000` | $H_0$ | $17$ | $2$ | $2$ | $15$ | $24$ |
| $(15,5)$ | `LLRRRRRRRRRRRRR` | $\alpha$ | `000000` → `010000` | $H_5$ | $12$ | $1$ | $1$ | $15$ | $15$ |
| $(15,4)$ | `LLRRRRRRRRRRRRR` | $\beta$ | `000000` → `000100` | $H_4$ | $13$ | $1$ | $1$ | $15$ | $15$ |
| $(15,3)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRRRRRRRRR` | $\mathsf b,\bot$ | `000000` → `100000` → `100100` | $H_3$ | $14$ | $2$ | $2$ | $16$ | $31$ |
| $(15,2)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRRRRRRRRR` | $\mathsf b,\alpha$ | `000000` → `100000` → `100010` | $H_2$ | $15$ | $2$ | $2$ | $16$ | $31$ |
| $(15,1)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRRRRRRRRR` | $\mathsf b,\beta$ | `000000` → `100000` → `100001` | $H_{1U}$ | $16$ | $2$ | $2$ | $16$ | $31$ |
| $(15,0)$ | `LLRRRRRRRRRRRRR`, `LRRRRRRRRRRRRRRR` | $\mathsf b,\mathsf b$ | `000000` → `100000` → `101000` | $H_0$ | $17$ | $2$ | $2$ | $16$ | $31$ |

**Proof, actual readout and writes.** The three addresses have native
functions $P_{27},P_{16},P_{30}$. Equation (NARC.18.2) gives
$P_{27}$ cells $D_L,\{27\},\{28\},D_U$;
$P_{16}$ on $D_L$ has cells $\{2,\ldots,7\},\{16\},\{17\},\{18\}$;
$P_{30}$ on $D_U$ has cells $\{29\},\{30\},\{31\},\{32\}$.
Substitution of the fifteen ages in Proposition 17.2 gives exactly
the displayed actual replies and first halts. The final constants
are their respective $17-b$. Every running row realizes all four
reply labels on its exact arriving support; no unsupported-response
completion is needed here.

All eleven displayed words are distinct, length six, and contain no
adjacent ones. Number coordinates from the left by $1,\ldots,6$.
The immediate response flips, in reply order, are

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\ \hline
R&3&2&4&1\\
A&5&6&6&1\\
B&4&5&6&3.
\end{array}
\tag{NARC.19.1}
$$

For example the lower branch transition is
`001000` → `101000`, flipping coordinate one, while the upper
branch is `100000` → `101000`, flipping coordinate three.
Each listed actual transition changes exactly one bit to a legal
installed word. The response is discarded at that update, with
no added instruction or mutable field. All eleven installed words
are reached by at least one displayed origin.

**Proof, the same-source closed loop.** For every state $s$ define
the exact proof support

$$
\mathcal C_s=
\{(\ell_{a,b},Y_{a,b}):(a,b)\in C
          \text{ and the displayed run visits }s\}.
\tag{NARC.19.2}
$$

The running supports are all $C$ at $R$, the nine origins of $D_L$
at $A$, and the four origins of $D_U$ at $B$. The halt supports
are exactly those in Definition 19.1. Every actual Read is legal
and has identity source transition: its successor source is that
same $Y_{a,b}$. The response-cell calculation places that same
$(\ell_{a,b},Y_{a,b})$ in the prescribed successor support.
Every halt support has its halt's correct constant lag. Take proof
rank two at $R$, one at $A,B$, and zero at every halt. Rank strictly
decreases on every supported step. Initial coverage, action legality,
same-source successor closure, rank descent and halt correctness
are therefore exactly [FIB, Theorem 27.2][FIB-RW]'s conditions.
Neither supports nor ranks are accessible inputs or runtime counters.

The non-self supported edges are precisely

$$
\begin{aligned}
&RA,\ RH_5,\ RH_4,\ RB,\\
&AH_{15},\ AH_{1L},\ AH_0,\\
&BH_3,\ BH_2,\ BH_{1U},\ BH_0.
\end{aligned}
\tag{NARC.19.3}
$$

Every edge is witnessed in the displayed actual-source table.
The words give its injective edge-preserving map into $\Gamma_6$.
[FIB, Theorem 45.4][FIB-RW] hence transfers the same closed-loop
certificate under the conditional write service. The different
source alternatives supply requirements on one installed table;
no execution splices their trees or histories. $\square$

**Proposition 19.3 (ten-state quotient and exact native schedule).**
Identify $H_{1L},H_{1U}$ as one abstract halt $H_1$ with complete
output $16$, fixing every other state. The quotient has exactly
ten installed states and the following total running table:

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\ \hline
R&A&H_5&H_4&B\\
A&H_{15}&H_1&H_1&H_0\\
B&H_3&H_2&H_1&H_0.
\end{array}
\tag{NARC.19.4}
$$

Its seven halt outputs are $2,12,13,14,15,16,17$ at
$H_{15},H_5,H_4,H_3,H_2,H_1,H_0$, respectively, and it uses
the same three literal addresses. For each original, projection
from Definition 19.1 preserves the actual literal requests, replies,
stationary source, complete output and first-halting Read count.

**Proof.** The projection changes only two halts with the same
output. It fixes all running rows except for their successor names.
Induction along each row of Proposition 19.2 therefore fixes every
requested literal and actual reply, and maps the first halt to the
same numeric-output first halt. No additional Read or write phase
is introduced.

This is the class-one schedule already supplied in the coordinate
reply certificates of Theorem 11.5: with its $(h,u,v)=(17,a-b,b)$,
offsets $(10,-1,13)$ give thresholds $(27,16,30)$, singleton
first targets $(5,4)$ and second target tuples $(15,1,1,0)$ and
$(3,2,1,0)$. The displayed certificate checks this row directly
on its entire acquired fiber. The writable table is an actual-path
refinement in [FIB, Definition 47.1][FIB-RW]'s sense, with the
split distinction counted as part of the complete halt word.
The schedule itself is reused; no full-encoder theorem is needed
to establish this conditional correspondence. $\square$

## 20. Sharp conditional separation and relational recovery

**Theorem 20.1 (abstract states, immediately writable states and bits).**
Under Assumptions 17.1 and 17.4, on the exact acquired entry
(NARC.17.2), the optima of Definition 17.5 are

$$
\boxed{M_2=10,\qquad W_2=11,\qquad L_2=6.}
\tag{NARC.20.1}
$$

The $L_2$ lower bound holds at every finite installed-state budget.
Definition 19.1 simultaneously attains $W_2$ and $L_2$, so also
$L_{11}=6$. These are complete recovery-control coordinates under
the named conditional services, with separately charged acquisition,
compilation, immutable storage, address submission and physical costs.

**Proof, the abstract state minimum.** Theorem 18.1 requires three
distinct reached running states. The seven distinct complete lags
require at least seven distinct reached halts, disjoint from running
states. Thus every table has at least ten installed states, whether
or not it has extra unreachable states. Proposition 19.3 attains ten,
giving $M_2=10$.

**Proof, the writable state minimum.** At exactly ten installed states
there are precisely the forced three running states and one halt
for each required lag. Write $H_0,H_1$ for the unique halts with
outputs $17,16$. Actual lower and upper second responses require
both $A,B$ to be adjacent to both these halts. They are also both
adjacent to $R$. These three common neighbors are distinct, so
every ten-state controller's actual support contains

$$
K_{2,3}\quad\text{with parts }\{A,B\},\{R,H_0,H_1\}.
\tag{NARC.20.2}
$$

The graph obstruction is classical: [Havel--Morávek, Propositions
1--2 and Example 1][HM-RW], pp.340--342, supply adjacency-preserving
injective cube coding and exclusion of $K_{2,3}$, as reused in
[FIB, Proposition 46.2][FIB-RW]. Its local specialization is that
two distinct cube words with a common neighbor differ in exactly
two coordinates, and have just the two intermediate words as
possible common neighbors. They cannot have three. Since
$\Gamma_d$ is a subgraph of the binary cube, (NARC.20.2) precludes
an injective edge-preserving implementation at every finite length.
The task-specific premise is the universally forced actual native
support, rather than the obstruction of just one chosen table.

Every admissible word device is itself a Moore table on all its
installed complete words and is subject to Theorem 18.1. Thus the
argument excludes all ten-state writable competitors, including
newly synthesized tables, and the abstract bound excludes fewer.
Definition 19.1 supplies eleven immediately writable states, hence
$W_2=11$.

For the exact ten-state boundary, singleton first ages $27,28$
cannot enter $A$: its $P_{16}$ branch successor is already required
to output $17$ for lower age $18$, whereas their outputs are $12,13$.
They cannot enter $B$: its $P_{30}$ absence successor already
outputs $14$ for upper age $29$. Returning to $R$ cannot terminate
on the stationary source. There is no other running state, so
they halt directly at $H_5,H_4$. All lower-bound states are reached;
an unused installed state does not repair this boundary.

**Proof, word length independently of state budget.** Use the actual
path $A-R-B$ and degree bounds of Theorem 18.1 for an arbitrary
finite competitor, without assuming ten or eleven states.
The needed ambient degree facts are literature-attested consequences
of [Klavžar--Mollard--Petkovšek][KMP-RW]. In their notation
$f_{n,k,w}$ counts degree-$k$, weight-$w$ vertices of $\Gamma_n$.
Corollary 3.4 (author manuscript p.7), at $n=5,m=0$, satisfies
its hypothesis $n\ge2m+2$ and gives one degree-five vertex.
The word `00000` has all five unit words as neighbors, so it is
that unique vertex. Theorem 4.6 (p.12) gives

$$
f_{n,k,w}=
\binom{w+1}{n-w-k+1}\binom{n-2w}{k-w},\qquad
f_{5,k,2}=\binom3{4-k}\binom1{k-2}=0\quad(k=4,5).
\tag{NARC.20.3}
$$

The binomial coefficient is zero outside its allowed lower-index
range. Since degree is at most five, every legal weight-two vertex
of $\Gamma_5$ has degree at most three. These are intermediate
classical graph facts, not new graph-theory claims.

Suppose a correct writable controller embeds its actual support
into $\Gamma_5$. Injectivity and edge preservation give each image
at least as many distinct ambient neighbors as its supported degree.
If $\deg(B)>5$ this is already impossible; otherwise $B$ must map
to `00000`. Its distinct neighbor $R$ maps to a unit word $e_i$.
A neighbor of $e_i$ other than zero has weight two. Because
$A\ne B$ and the map is injective, $A$ must map to such a legal
weight-two word. It then has at most three ambient neighbors,
contradicting $\deg(A)\ge4$.

For a shorter word length $d<5$, append $5-d$ trailing zeros.
This preserves injectivity, absence of adjacent ones and every
Hamming-one edge, and would give the already excluded embedding
into $\Gamma_5$. Thus every finite-state immediate controller
in this exact two-Read competition class needs at least six bits.
The six-bit certificate gives $L_2\le6$, proving equality and the
restricted $L_{11}=6$. No classification of eleven-state controllers
or square-based lower-bound route enters the argument. $\square$

**Proposition 20.2 (joint resources and separate service costs).**
For the same eleven-state, six-bit controller the actual sourcewise
vector $(\text{Reads},\text{response writes},\text{peak},\text{sum})$
is

$$
\begin{cases}
(2,2,15,24),&n\in D_L,\\
(1,1,15,15),&n=27,28,\\
(2,2,16,31),&n\in D_U.
\end{cases}
\tag{NARC.20.4}
$$

The three independently stored addresses contain forty letters in
this table representation. This is table accounting, not a storage
optimum. Response writes exclude initialization. Mutable word length,
installed states, immutable table/output/address storage and submitted
address lengths remain different resources.

**Proof.** Proposition 19.2 gives every first-halt trace and exactly
one response flip per Read. Lower traces submit lengths $15,9$;
root singleton traces submit length $15$; upper traces submit
$15,16$. Taking maximum and sum on that same actual trace gives
(NARC.20.4). In particular each individual upper origin simultaneously
attains two Reads, two writes, peak sixteen and sum thirty-one with
the same installed table. No coordinate comes from another source
or another controller. The independent literal storage total is
$15+9+16=40$; shared representations could have a different charge.

Following [FIB, Definition 45.2][FIB-RW], let costs be separately
supplied nonnegative scalars or resource vectors. For a trace with
$m$ Reads and complete halt output $\ell$, one service account is

$$
\begin{aligned}
\mathcal C={}&C_{\rm initial\ capture}+C_{\rm encode/export}
 +C_{\rm continuation}+C_{\rm later\ capture/parse}
 +C_{\rm compile/install}+C_{\rm init}+C_{\rm immutable}\!\\
&+\sum_{t<m}\left(C_{\rm table}(w_t)
 +C_{\rm submit}(p_t)+C_{\rm Read}(p_t,Y_{a,b})
 +C_{\rm response\ write}(w_t,o_t)\right)\\
&+C_{\rm table}(w_m)+C_{\rm output}(\ell).
\end{aligned}
\tag{NARC.20.5}
$$

Choose these accounts without double counting any shared service;
none is made free by the finite state proof. Initialization writes
belong to $C_{\rm init}$, and the fixed literal/output representation
belongs to the installation and immutable accounts. Equation
(NARC.20.5) provides no numerical physical cost unless those
services and costs are actually supplied. Six mutable recovery bits
therefore imply neither six bits of total physical storage nor any
physical latency, energy or acquisition bound. $\square$

**Proposition 20.3 (selected temporal recovery and operational memory).**
Under the exact acquired-entry and service contract, acquired literal
boundary structure and the causally exported origin relation, together
with the permitted native Reads, recover the number of intervening
substitutions. This recovery neither determines the full source nor
identifies every hidden age. The additional writable state records
an operational distinction for legal updates, while the sixth bit
is forced by the actual transition geometry.

**Proof.** The acquired right exterior gives the relation $b+\ell=17$.
The causal label restricts $(a,b)$ to $C$. Actual native replies
resolve $b$ to a common target at the reached halt, whose installed
constant is exactly $\ell=17-b$. This links current spatial boundary
data with elapsed substitution count relative to the genuinely
acquired original. It gives no physical elapsed time or absolute epoch.

Before a fresh Read, for example $(0,15)$ at lag two and $(15,0)$
at lag seventeen have the same code and entire later row. Thus that
entry alone does not determine the lag. Even one four-valued Read
cannot serve its seven distinct lag values. The certificate completes
recovery in at most two Reads, and Theorem 18.1 identifies the native
partitions necessary to do so.

The six origins $(j,15)$, $0\le j\le5$, have the same acquired
entry and the same entire two-reply transcript, but distinct originals
and current hidden ages $2,\ldots,7$. They all halt at $H_{15}$
with output two. No decoder of that completed trace can reconstruct
all those originals or hidden fillings. At output sixteen the lower
origins $(0,1),(1,1)$ also share a halt. These collisions witness the
precise distinction between target recovery and full reconstruction.

The ten-state quotient freely shares equal-output halts. Immediate
single-bit permission excludes its three-common-neighbor support.
Splitting the output-sixteen halt distinguishes the lower and upper
operational paths without changing their acquired information,
observations, numeric answer or first halt. It supplies a counted
legal-write configuration distinction, rather than an extra source
fact. Partitioning legal words by initial $0$ or $10$ gives counts
$a_d=a_{d-1}+a_{d-2}$, with $a_0=1,a_1=2$, hence $a_5=13$.
Thus $\Gamma_5$ has enough legal names for eleven states, but its
neighborhoods fail the universally forced path.
Cardinality and representation alone do not grant the necessary write
permission. The conditional atomic-write service grants that operation;
the six-bit certificate does not prove its physical availability.

These statements concern one fixed acquired entry. A single finite
table has only finitely many fixed halt constants and cannot return
every unbounded lag. Other labels, rows, cuts and Read budgets need
their own acquired-fiber and controller proofs. This result establishes
neither an all-input controller for $q=17$, a uniform finite memory
bound over unbounded lags, a global resource frontier, nor completion
of the space/time/boundary/memory programme. $\square$

**Definition 20.4 (mathematical supplier correspondence).** Native
definitions and results used here are the exact §§4.1, 5.2, 5.3,
9.1 and 11.1 in [NARC at the fixed base][NARC-RW-base]. Those
sections, together with the class-one coordinate certificate of
Theorem 11.5, are also the same text in the immutable
[native supplier revision][NARC-RW-source]. Integration status of
other theory increments is not a mathematical hypothesis. The
following correspondence specifies the retained semantic parameters.

| Supplier at the native supplier revision | Exact parameter or semantic correspondence | Boundary of its use |
| --- | --- | --- |
| [NAR Definitions 1.1--1.2 and Reuse 16.2][NAR-RW] | Actual ordered trees, homomorphic $\rho$, four-valued literal Read, entire exterior and reached-hole partition; acquired literals compute their clocks | No hidden-origin, epoch, subtree or hidden-visible comparison port |
| NARC Theorem 5.2 and Definition 5.3 | $q=16,z=17,C=e_{16}^{-1}(1)$; $n=17+a-b$, $\ell=17-b$; guarded $E/P/S$ laws | Whole-row compatibility is retained; no interval age-identification formula |
| NARC Assumptions 4.1 and 9.1; [AOF Definitions 8.2 and 10.1][AOF-RW] | Common installed table, complete mutable state, fixed literals and complete outputs; chronological two-Read budget and shortest native representatives | The Moore restriction is added explicitly; fixed-reference and interval numerical optima are not applied |
| NARC Definition 11.1 and class-one certificate of Theorem 11.5 | Actual right offset sixteen; code inverse class $C$; offsets $10,-1,13$ at $h=17$ | No premise about the rest of the full encoder or its packing |
| [GenealogicalFiberTransport: `Source`, `substitution`][RW-Source] | `FreeMagma Bool`, `true` = $\alpha$, `false` = $\beta$; actual homomorphic leaf images | Semantic correspondence only |
| [ActualTreeReadoutAcquisition: `Address`, `Reply`, `readout`][RW-Read] | `List Bool`, `false` = $L$, `true` = $R$; a nonempty suffix at a leaf returns absence | Its distinct-address payment is not chronological Read count |
| [DelayedOriginalReadout: `rightClock`, `right_clock_iterate`, `right_clock_readout`][RW-Clock] | Literal clock increases by the substitution count; $R^s$ yields thresholds $2s,2s+1$ | A decoder supplied a known epoch does not recover an unknown lag |
| [ActualCutPartitionDecoder: `literalRecord`, `actualPartition`, `canonicalRow_record_iff`][RW-Row] | Prefix-free cut $\{L\}$; complete exterior and all reached-hole equality pairs | Singleton partition adds no hidden-visible comparison or acquisition trace |
| [NativeCutFibers: `legal_values_row`, `rowFiberEquiv`][RW-Fiber] | Legal fillings and actual complete-row fibers | Filling coordinates in a proof are not accessible values |
| [ActualFibonacciSupportChain: local recurrence in `actual_fibonacci_support_chain`][RW-Orbit] | $T_n=\rho^n\alpha$ and $T_{n+2}=\langle T_{n+1},T_n\rangle$ | The support-chain conclusion supplies no controller optimum |

The response-write supplier is [FIB §§45--47 at its immutable
revision][FIB-RW], with its Definitions 26.1--26.2 and Theorem
27.2. The exact support is $\mathcal C_s$ of (NARC.19.2), the
source transition is identity, and the target coordinate is the full
lag. FIB45.1--45.4 supply the conditional complete-word service,
separate costs and injective supported-edge criterion. FIB46.2
reuses the classical cube obstruction; here Theorem 18.1 supplies
the missing universal native-task premise. FIB47.1 supplies the
actual-path refinement contract met by Proposition 19.3.

FIB47.2's generic finite-history refinement uses [Cabello--Eppstein--
Klavžar, Corollary 3.6][CEK-RW]: for a finite tree $T$,
$\operatorname{fdim}(T)=\operatorname{idim}(T)=|E(T)|$ under
isometric embedding. That is a safe existence supplier for a larger
history refinement, not the optimum eleven or six. Isometric tree
dimension is not a lower bound for the weaker edge-preserving
shared-halt encoding used here. No tree-dimension proof is repeated.

The cube obstruction and Fibonacci degree counts consumed in Theorem
20.1 are literature-attested intermediate results. The increment is
the repo-derived universal acquired-native-query/support correspondence
and its attained conditional resource separation. It asserts no global
originality. The ordinary arguments do not assert a new Lean theorem,
current kernel verification or any digestion or frozen-state status.

The primary mathematical citations attached to these consuming proofs
are Ivan Havel and Jaroslav Morávek, *B-valuations of graphs*,
Czechoslovak Mathematical Journal 22(2), 338--351 (1972),
DOI [10.21136/cmj.1972.101102][HM-RW], Propositions 1--2 and
Example 1, [primary text pp.340--342][HM-RW-full]; Sandi Klavžar,
Michel Mollard and Marko Petkovšek, *The degree sequence of Fibonacci
and Lucas cubes*, Discrete Mathematics 311(14), 1310--1322 (2011),
DOI [10.1016/j.disc.2011.03.019][KMP-RW-doi], Corollary 3.4 and
Theorem 4.6, [author manuscript pp.7 and 12][KMP-RW]; and Sergio
Cabello, David Eppstein and Sandi Klavžar, *The Fibonacci Dimension
of a Graph*, The Electronic Journal of Combinatorics 18(1), P55
(2011), DOI [10.37236/542][CEK-RW], Corollary 3.6,
[primary preprint pp.7--8][CEK-RW-full].

[NARC-RW-base]: https://github.com/the-omega-institute/trureturing/blob/8d16d2f170a857dc60923345f02127947dc53f11/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md
[NARC-RW-source]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md
[NAR-RW]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[AOF-RW]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[FIB-RW]: https://github.com/the-omega-institute/trureturing/blob/8d9ce47ac151e4ff332c8b1fb44759ebd0e0f11c/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md
[RW-Source]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean
[RW-Read]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[RW-Clock]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[RW-Row]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[RW-Fiber]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[RW-Orbit]: https://github.com/the-omega-institute/trureturing/blob/154126ff1e0d3bf6c7283e3765b6c496e69ca005/D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.lean
[HM-RW]: https://doi.org/10.21136/cmj.1972.101102
[HM-RW-full]: https://dml.cz/bitstream/handle/10338.dmlcz/101102/CzechMathJ_22-1972-2_15.pdf
[KMP-RW]: https://users.fmf.uni-lj.si/klavzar/preprints/DegSeqRevised.pdf
[KMP-RW-doi]: https://doi.org/10.1016/j.disc.2011.03.019
[CEK-RW]: https://doi.org/10.37236/542
[CEK-RW-full]: https://arxiv.org/pdf/0903.2507

## 追加锚（本行以下为增补区）

## 21. Chronological interaction and complete mutable word width

**Assumption 21.1 (one entry and a variable Read allowance).** Retain
Assumption 17.1, the exact acquired entry (NARC.17.2), and all the
complete-state and conditional immediate-write requirements of
Assumption 17.4. Replace only its two-Read allowance by at most
$k$ chronological native Reads, where $k\ge0$ is a finite integer.
The stationary actual sources, full numeric lag target, legal literal
addresses, reply alphabet and response-write permission are identical
for every $k$.

In particular, conditional compilation uses only the common acquired
entry and public data. It installs one table and one initial word for
all fifteen origins of Proposition 17.2, then discards and closes access
to acquisition inputs and compilation workspace. The current word is
the entire mutable accessible configuration. Running or halting type,
the fixed literal at a running word, its four successor words, and the
complete integer at a halt are immutable functions of that word. The
current reply is used only for the immediate zero-or-one legal bit
update and is discarded. There is no retained reply, program counter,
clock, counter, history, mutable decoder or internal write phase.
All installed words count, including halts and unused words. Acquisition,
compilation, immutable tables, initialization and physical services retain
the separate conditional supply and charges of §§17 and 20.2.

**Definition 21.2 (the conditional width frontier).** For a positive
integer $d$, let $\mathfrak W(k,d)$ contain every controller satisfying
Assumption 21.1 on an arbitrary installed subset of $\Gamma_d$ of
(NARC.17.6). Every declared successor must be installed and equal to
its running word or differ by one legal bit. Every original must reach
its correct first halt within $k$ Reads from the common initial word.
Set

$$
L(k)=\min\{d\ge1:\mathfrak W(k,d)\ne\varnothing\},
\qquad \min\varnothing=\infty.
\tag{NARC.21.1}
$$

The family includes arbitrary finite literal lengths, every installed
subset, repeated and constant Reads, early halts, duplicated output
halts, shared control and cycles in the union of different-source
transitions. There is no prescribed installed-state count. The two-Read
case is exactly Definition 17.5's competition, so Theorem 20.1 supplies
$L(2)=L_2=6$.

The full fiber, both realization directions and target are those of
Proposition 17.2 and Definition 17.3:

$$
\begin{aligned}
C&=\{(1,0),(1,1),(0,1)\}
 \cup\{(15,j),(j,15):0\le j\le5\},\\
\ell_{a,b}&=17-b,\qquad
Y_{a,b}=\langle T_{17+a-b},T_{33}\rangle,\qquad
g(D)=\{2,12,13,14,15,16,17\}.
\end{aligned}
\tag{NARC.21.2}
$$

Every member realizes the entire acquired row at its own lag, and the
label and entire row exclude every other history. All lags are at
least two, so either lag convention retains the same fifteen members.
Hidden age $n=17+a-b$ is only a proof coordinate. Reads keep that
source stationary; the chronological budget is not the generation lag.

## 22. A five-bit actual controller with three Reads

**Definition 22.1 (twelve complete words and four literal instructions).**
The common initial word is `00000`. Install exactly the following four
running rows. The successor columns are in the order
$\bot,\alpha,\beta,\mathsf b$ of Assumption 17.1.

| Running word | Complete original-root literal | Length | $\bot$ successor | $\alpha$ successor | $\beta$ successor | $\mathsf b$ successor |
| --- | --- | --- | --- | --- | --- | --- |
| `00000` | `LRRRRRRRRRRRRRR` | $15$ | `00001` | `00010` | `01000` | `10000` |
| `00001` | `LRRRRRRRR` | $9$ | `01001` | `10001` | `10001` | `00101` |
| `00101` | `LRRRRRRRRR` | $10$ | `00101` | `00100` | `00101` | `10101` |
| `10000` | `LRRRRRRRRRRRRRRR` | $16$ | `10000` | `10010` | `10001` | `10100` |

Install exactly these eight halting rows, with no Read or response
transition at a halt:

| Halting word | Installed complete numeric lag | Exact hidden-age support |
| --- | --- | --- |
| `00010` | $13$ | $\{28\}$ |
| `00100` | $17$ | $\{18\}$ |
| `01000` | $14$ | $\{29\}$ |
| `01001` | $2$ | $\{2,3,4,5,6,7\}$ |
| `10001` | $16$ | $\{16,17,31\}$ |
| `10010` | $15$ | $\{30\}$ |
| `10100` | $17$ | $\{32\}$ |
| `10101` | $12$ | $\{27\}$ |

Thus the installed set is

$$
\begin{aligned}
K=\{&00000,00001,00010,00100,00101,01000,01001,\\
    &10000,10001,10010,10100,10101\}.
\end{aligned}
\tag{NARC.22.1}
$$

The entries in (NARC.22.1) denote binary words, including leading
zeros. The remaining ambient legal word `01010` has no installed row.
The repeated output seventeen is a complete constant at two distinct
halt words; the single word `10001` contains the complete output
sixteen. No halt performs subtraction, source selection or decoding.
The four running literals are fully materialized; $P_{28},P_{16},
P_{18},P_{30}$ are their hidden-relative functions in proof notation,
not runtime address generators.

**Theorem 22.2 (whole-fiber first-halt attainment).** Under Assumption
21.1's conditional services, Definition 22.1 is a faithful member of
$\mathfrak W(3,5)$. Every installed word is reached. There are twelve
installed words, four running words, eight halts and sixteen total
successor entries. Every actual step flips exactly one bit, and every
original first halts with its full numeric lag after at most three Reads.

For an individual run define the resource vector

$$
V=(d,r,b,p,s),
\tag{NARC.22.2}
$$

where $d$ is the complete mutable width, $r$ the chronological Read
count, $b$ the response bit-write count, $p$ the peak submitted literal
length and $s$ the sum of those lengths on that same run. Initialization
writes and immutable installation costs are separate. Number bit
coordinates from the left by $1,\ldots,5$.
The complete attainment certificate is:

| Original $(a,b)$ | Proof age $n$ | Full lag output | Literal submissions in order | Actual replies | Word path through first halt | Flipped coordinates | Literal lengths | Same-run $V$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $(0,15)$ | $2$ | $2$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `00000` → `00001` → `01001` | $(5,2)$ | $(15,9)$ | $(5,2,2,15,24)$ |
| $(1,15)$ | $3$ | $2$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `00000` → `00001` → `01001` | $(5,2)$ | $(15,9)$ | $(5,2,2,15,24)$ |
| $(2,15)$ | $4$ | $2$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `00000` → `00001` → `01001` | $(5,2)$ | $(15,9)$ | $(5,2,2,15,24)$ |
| $(3,15)$ | $5$ | $2$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `00000` → `00001` → `01001` | $(5,2)$ | $(15,9)$ | $(5,2,2,15,24)$ |
| $(4,15)$ | $6$ | $2$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `00000` → `00001` → `01001` | $(5,2)$ | $(15,9)$ | $(5,2,2,15,24)$ |
| $(5,15)$ | $7$ | $2$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\bot$ | `00000` → `00001` → `01001` | $(5,2)$ | $(15,9)$ | $(5,2,2,15,24)$ |
| $(0,1)$ | $16$ | $16$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\alpha$ | `00000` → `00001` → `10001` | $(5,1)$ | $(15,9)$ | $(5,2,2,15,24)$ |
| $(1,1)$ | $17$ | $16$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR` | $\bot,\beta$ | `00000` → `00001` → `10001` | $(5,1)$ | $(15,9)$ | $(5,2,2,15,24)$ |
| $(1,0)$ | $18$ | $17$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR`, `LRRRRRRRRR` | $\bot,\mathsf b,\alpha$ | `00000` → `00001` → `00101` → `00100` | $(5,3,5)$ | $(15,9,10)$ | $(5,3,3,15,34)$ |
| $(15,5)$ | $27$ | $12$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRR`, `LRRRRRRRRR` | $\bot,\mathsf b,\mathsf b$ | `00000` → `00001` → `00101` → `10101` | $(5,3,1)$ | $(15,9,10)$ | $(5,3,3,15,34)$ |
| $(15,4)$ | $28$ | $13$ | `LRRRRRRRRRRRRRR` | $\alpha$ | `00000` → `00010` | $(4)$ | $(15)$ | $(5,1,1,15,15)$ |
| $(15,3)$ | $29$ | $14$ | `LRRRRRRRRRRRRRR` | $\beta$ | `00000` → `01000` | $(2)$ | $(15)$ | $(5,1,1,15,15)$ |
| $(15,2)$ | $30$ | $15$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRRRRRRRRR` | $\mathsf b,\alpha$ | `00000` → `10000` → `10010` | $(1,4)$ | $(15,16)$ | $(5,2,2,16,31)$ |
| $(15,1)$ | $31$ | $16$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRRRRRRRRR` | $\mathsf b,\beta$ | `00000` → `10000` → `10001` | $(1,5)$ | $(15,16)$ | $(5,2,2,16,31)$ |
| $(15,0)$ | $32$ | $17$ | `LRRRRRRRRRRRRRR`, `LRRRRRRRRRRRRRRR` | $\mathsf b,\mathsf b$ | `00000` → `10000` → `10100` | $(1,3)$ | $(15,16)$ | $(5,2,2,16,31)$ |

**Proof, native replies and full outputs.** Proposition 17.2 supplies
the original and its own actual $Y_{a,b}$ for each row. The literal
representatives of Definition 5.3, exhausted in (NARC.18.2), give
the following exact reply cells on each reached running support:

| Running word | Exact arriving ages | $\bot$ ages | $\alpha$ ages | $\beta$ ages | $\mathsf b$ ages |
| --- | --- | --- | --- | --- | --- |
| `00000` | $D$ | $\{2,3,4,5,6,7,16,17,18,27\}$ | $\{28\}$ | $\{29\}$ | $\{30,31,32\}$ |
| `00001` | $\{2,3,4,5,6,7,16,17,18,27\}$ | $\{2,3,4,5,6,7\}$ | $\{16\}$ | $\{17\}$ | $\{18,27\}$ |
| `00101` | $\{18,27\}$ | $\varnothing$ | $\{18\}$ | $\varnothing$ | $\{27\}$ |
| `10000` | $\{30,31,32\}$ | $\varnothing$ | $\{30\}$ | $\{31\}$ | $\{32\}$ |

The root $P_{28}$ sends age twenty-eight to output thirteen and age
twenty-nine to output fourteen. Its absence successor executes
$P_{16}$: ages two through seven halt with two, ages sixteen and
seventeen halt with sixteen, and ages eighteen and twenty-seven
continue to `00101`. Its $P_{18}$ replies there are respectively
$\alpha$ and $\mathsf b$, selecting seventeen and twelve. The root
branch successor executes $P_{30}$ on ages thirty, thirty-one and
thirty-two, selecting fifteen, sixteen and seventeen. These cells
exhaust all fifteen originals and give precisely $17-b$ in every row.
The chronological submissions are the displayed whole-tree literals;
no hidden-age calculation occurs during a run.

**Proof, all declared writes.** All twelve words have length five and
contain no adjacent ones. The changed coordinates for all sixteen
entries, in reply order, are

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\ \hline
00000&5&4&2&1\\
00001&2&1&1&3\\
00101&0&5&0&1\\
10000&0&4&5&3.
\end{array}
\tag{NARC.22.3}
$$

Here zero means staying at the same installed word. Every nonzero
entry changes exactly that coordinate to the indicated legal installed
word. The three self-loop completions, at `00101` on absence or
$\beta$ and at `10000` on absence, have empty actual response
support. Every supported entry changes one bit; none uses an extra
phase. The total rows do not assert termination from unsupported
source-word pairs.

**Proof, exact supports and first halt.** For each installed word $w$
take

$$
\mathcal C_w=\{(\ell_{a,b},Y_{a,b}):(a,b)\in C
                 \text{ and its displayed path visits }w\}.
\tag{NARC.22.4}
$$

The age coordinate is injective on $C$, so the running-cell table and
the eight halt supports specify these sets exactly. Initially all
fifteen sources lie in $\mathcal C_{00000}$. The cell calculation
preserves the same pair $(\ell_{a,b},Y_{a,b})$ at its prescribed
successor; the source transition is identity. Every reached halt has
its correct complete constant. Assign proof rank

$$
\operatorname{rank}(00000)=3,\quad
\operatorname{rank}(00001)=2,\quad
\operatorname{rank}(00101)=\operatorname{rank}(10000)=1,\quad
\operatorname{rank}(h)=0\quad(h\in H).
\tag{NARC.22.5}
$$

Every supported Read strictly decreases rank. Thus each run has its
correct first halt within three Reads, with exactly the displayed
paths. This is the stationary-source specialization of [FIB, Theorem
27.2][FIB-RW]'s initial coverage, legal action, successor closure,
rank descent and halt correctness certificate, together with its
immediate-write criterion in Theorem 45.4. Supports and ranks are
proof data, never accessible control fields.

Each halt and running word occurs in the fifteen-row table, proving
that all installed words are reached. Each step contributes one Read,
one response bit write and its displayed literal length. Taking peak
and sum on that individual path proves every vector in (NARC.22.2).
The undirected supported cycle
`00000`--`00001`--`10001`--`10000`--`00000` combines edges from
different originals; no stationary actual run follows it as a cycle.
Global acyclicity of the union support is not a premise. $\square$

## 23. The all-budget four-bit obstruction and the exact frontier

**Theorem 23.1 (four bits cannot recover the whole fiber).** Under
Assumption 21.1, for every finite integer $k\ge0$ and every
$1\le d\le4$, $\mathfrak W(k,d)=\varnothing$. More strongly,
no such controller can terminate correctly on all fifteen sources
even if only eventual termination, with no common Read cap, is required.

**Proof.** The complete legal set at length four is

$$
\{0000,0001,0010,0100,0101,1000,1001,1010\}.
\tag{NARC.23.1}
$$

These are binary words. Appending trailing zeros embeds every shorter
legal-word set into this set, so there are at most eight available
complete configurations at any $d\le4$.
The seven distinct required full integers in (NARC.21.2) need at least
seven distinct installed halting words: one fixed halt word has one
fixed complete output. Therefore at most one word is running. Duplicate
output halts, unused installations or additional halt labels can only
consume more of the same eight-word capacity.

The common initial word must run because the target is not constant
on $C$. Fix one actual stationary source. At that sole running word
the entire accessible configuration fixes its literal. The source fixes
the reply, and the immutable response row fixes its successor. If that
successor is the same running word, the same configuration, source,
literal, reply and successor repeat forever. There is no retained
count, clock, reply or writing phase to make a later visit different.
Consequently every correctly terminating source must reach a halt
directly after its first Read. Four replies can reach at most four
distinct complete outputs, contradicting the required seven.

This uses no restriction on the literal beyond the four-valued native
interface. It covers all finite addresses, every installed subset,
output duplication, early halts, constant or repeated Reads, shared
control and cycles. Its stationary repetition argument is per actual
source, not a prohibition on union-support cycles. It is an ordinary
universal exclusion proof, independent of controller enumeration.
$\square$

**Theorem 23.2 (the complete conditional interaction-width frontier).**
For the identical acquired entry, target and services of Assumption
21.1, the frontier of Definition 21.2 is

$$
\boxed{
L(k)=\begin{cases}
\infty,&k=0,1,\\
6,&k=2,\\
5,&\text{every finite integer }k\ge3.
\end{cases}}
\tag{NARC.23.2}
$$

In particular, the minimum worst-case chronological Read count at
five mutable bits is exactly three.

**Proof.** A common initial halt yields only one output. If the initial
word runs, a budget of one Read requires every actual successor to
halt immediately. That one fixed literal has only four replies, hence
at most four different full halt outputs. Neither zero nor one Read
can supply the seven required integers, at any finite word width.

For $k=2$, Assumption 21.1 is exactly the writable contract of
Assumption 17.4. Theorem 20.1's lower bound ranges over every finite
installed-state budget and all literal queries, using the all-address
and forced-support proof of Theorem 18.1. Proposition 19.2 supplies
the matching six-bit actual certificate on these same fifteen histories.
Thus $L(2)=6$. The result is reused with its whole controller family;
no restriction to a particular two-Read table is introduced.

Theorem 22.2 gives $L(3)\le5$. The same table still first halts within
three Reads when any larger finite at-most allowance is available,
so $L(k)\le5$ for every $k\ge3$. Theorem 23.1 excludes all shorter
widths at each such allowance. This proves equality. The two-Read
exclusion also proves the lower half of the stated minimum Read count
at width five, and the new table attains its upper half. $\square$

## 24. Changed native supports, joint resources and supplier boundaries

**Proposition 24.1 (interaction changes the supported write geometry).**
The attained five-bit strategy changes the first literal function from
$P_{27}$ to $P_{28}$. It changes the native supports and the required
immediate-write graph while keeping all original histories and numeric
targets fixed. It is not a relabeling of the two-Read certificate.

**Proof.** In §19 the first $P_{27}$ directly halts at ages twenty-seven
and twenty-eight, routes $D_L$ to $P_{16}$, and routes
$D_U=\{29,30,31,32\}$ to $P_{30}$. The universally forced lower
and upper running neighborhoods have degrees at least four and five
by Theorem 18.1. Theorem 20.1 excludes their common-predecessor path
from $\Gamma_5$, regardless of recoding or added installed states.

With first $P_{28}$, age twenty-nine instead has a first halt, and the
upper support becomes $\{30,31,32\}$. Its $P_{30}$ running word
requires only three halt neighbors plus its predecessor; these fit
at `10000`. Age twenty-seven joins $D_L$ at `00001`. The fixed
$P_{16}$ Read there merges ages eighteen and twenty-seven in branch,
but their complete outputs are seventeen and twelve. The actual
additional $P_{18}$ Read at `00101` distinguishes them. This is a new
source observation; postprocessing the earlier branch reply could not
separate the pair. Output sixteen is shared at `10001`, while output
seventeen is duplicated at `00100` and `10100`.

The changed first query alters both the arriving sources and which
successor distinctions must be written. The legal words in Definition
22.1 realize that altered graph. A word renaming that preserved the
old actual query/reply paths would still face the two-Read obstruction;
it could not supply the new five-bit capability. $\square$

**Proposition 24.2 (same-origin resource comparisons).** Let
$V^{(6)}_{a,b}$ be the vector (NARC.22.2) for Definition 19.1 and
$V^{(5)}_{a,b}$ the vector for Definition 22.1. On each same original
they are exactly:

| Original $(a,b)$ | $V^{(6)}_{a,b}$ | $V^{(5)}_{a,b}$ |
| --- | --- | --- |
| $(0,15)$ | $(6,2,2,15,24)$ | $(5,2,2,15,24)$ |
| $(1,15)$ | $(6,2,2,15,24)$ | $(5,2,2,15,24)$ |
| $(2,15)$ | $(6,2,2,15,24)$ | $(5,2,2,15,24)$ |
| $(3,15)$ | $(6,2,2,15,24)$ | $(5,2,2,15,24)$ |
| $(4,15)$ | $(6,2,2,15,24)$ | $(5,2,2,15,24)$ |
| $(5,15)$ | $(6,2,2,15,24)$ | $(5,2,2,15,24)$ |
| $(0,1)$ | $(6,2,2,15,24)$ | $(5,2,2,15,24)$ |
| $(1,1)$ | $(6,2,2,15,24)$ | $(5,2,2,15,24)$ |
| $(1,0)$ | $(6,2,2,15,24)$ | $(5,3,3,15,34)$ |
| $(15,5)$ | $(6,1,1,15,15)$ | $(5,3,3,15,34)$ |
| $(15,4)$ | $(6,1,1,15,15)$ | $(5,1,1,15,15)$ |
| $(15,3)$ | $(6,2,2,16,31)$ | $(5,1,1,15,15)$ |
| $(15,2)$ | $(6,2,2,16,31)$ | $(5,2,2,16,31)$ |
| $(15,1)$ | $(6,2,2,16,31)$ | $(5,2,2,16,31)$ |
| $(15,0)$ | $(6,2,2,16,31)$ | $(5,2,2,16,31)$ |

The new table installs twelve words rather than eleven, and its four
independently stored running literals contain fifty letters rather than
forty. These are attained table coordinates. The new coordinatewise
maxima are three Reads, three response writes, peak sixteen and sum
thirty-four, but no actual run realizes all those maxima jointly.

**Proof.** Proposition 19.2 and Theorem 22.2 provide the two actual
paths on each original. Their individual Read and flip counts and
literal lengths give the displayed vectors directly. In particular
$(1,0)$ gains one Read, $(15,5)$ gains two, and $(15,3)$ loses one.
Increasing the worst-case allowance from two to three therefore does
not mean one extra Read on each history.

The new three-Read runs have vector $(5,3,3,15,34)$; the runs whose
peak is sixteen have vector $(5,2,2,16,31)$. Thus peak sixteen and
sum thirty-four belong to different histories. The independent literal
count is $15+9+10+16=50$, compared with Proposition 20.2's forty.
It does not assert a minimum representation charge or address optimum.

Apply the separate service account (NARC.20.5) to each new path with
its own $m$, $p_t$, $w_t$, replies and complete output $17-b$.
Initial and later acquisition, export and discard, continuation,
compilation, installation, initialization, immutable literal/transition/
output storage and Read/write/output services remain separately supplied
and charged. The vector comparison therefore entails neither a total
physical storage advantage nor a latency, energy or scalar cost ordering.
No unmeasured service is made free by reducing the mutable word width.
$\square$

**Definition 24.3 (consumed mathematical correspondence and remaining
scope).** The native suppliers are [§§17--20 at their immutable
source][NARC-3R-parent]. Proposition 17.2 supplies both directions of
the acquired-row fiber, Definition 17.3 the full lag target, and
Assumption 17.4 the complete-state and immediate-write services.
Theorem 18.1 covers every native literal function and arbitrary state
budgets; its quantified two-Read obstruction and Theorem 20.1 are
consumed only at $k=2$. Equations (NARC.18.2) and Definition 5.3
supply the actual replies and materialized literals of Theorem 22.2.
[FIB, Theorem 27.2 and §§45--47][FIB-RW] supply support/rank,
conditional one-bit writing, separate charges and actual-path refinement,
with the same target-source pairs and identity source transition.

The following mature mathematical models clarify distinct parts of
this correspondence. Their cited results are intermediate suppliers
and model boundaries, not additional numerical native bounds.

| Primary source | Consumed relation | Exact transfer boundary |
| --- | --- | --- |
| Robert D. Nowak, *The Geometry of Generalized Binary Search*, [arXiv:0910.4397v5][Nowak-3R], §§I--II.A, Definition 1, pp.1--3 | A fixed unknown source gives a reply function on the permitted query family; query-response signatures determine transcript partitions. This explains why Proposition 24.1 changes an actual permitted experiment. | Nowak identifies an entire binary-valued hypothesis and supplies binary-query bounds under additional hypotheses. Here replies are four-valued, the target is only a repeated lag, and complete mutable updates are constrained. Its numerical identification bounds do not supply (NARC.23.2). |
| Allan Borodin and Stephen Cook, *A Time-Space Tradeoff for Sorting on a General Sequential Model of Computation*, SIAM Journal on Computing 11(2), 287--297 (1982), [§2, p.289][BC-3R] | Access depth and shared configuration capacity are distinct. Their branching-program model explicitly abstracts from storage representation and manipulation, locating the additional obligation met by the word table. | Their model is a leveled directed acyclic graph with integer input access and space capacity measured by logarithmic node count. Unrolling an actual native path is a proof representation, not an uncharged runtime level or PC. Their sorting bound supplies no no11-width bound here. |
| Randal E. Bryant, *Graph-Based Algorithms for Boolean Function Manipulation*, IEEE Transactions on Computers C-35(8), 677--691 (1986), [§2, Definitions 1--5 and Theorem 1][Bryant-3R], electronic pp.4--6 | Sharing residual computations distinguishes a decision graph from a transcript tree, as the shared output-sixteen word in Definition 22.1 illustrates. | Binary tests with fixed increasing variable order imply acyclicity in Bryant's model. Its reduced-graph canonicity and size minimum do not transfer to arbitrary native controllers or to legal immediate-write layouts. Merging equal-output halts need not preserve an embedding. |
| Ivan Havel and Jaroslav Morávek, *B-valuations of graphs*, [Propositions 1--2][HM-RW-full], pp.340--341 | Their injective adjacency-preserving cube coding is the binary state-transition correspondence reused in FIB45.4. Theorem 22.2 supplies actual supported edges and legal words for it. | An unrestricted cube encoding does not impose no11 legality. The required map preserves edges, not all nonedges or distances. The explicit word certificate supplies the extra restriction; ordinary cube embeddability or bipartiteness alone does not. |
| Sergio Cabello, David Eppstein and Sandi Klavžar, *The Fibonacci Dimension of a Graph*, [arXiv:0903.2507v1][CEK-3R], definition and Corollary 3.6, pp.1, 7--8 | Isometric Fibonacci-cube tree encodings supply the general finite-history existence route already used in FIB47.2. | Isometric dimension preserves all distances. The present shared controller requires only immediate edges. The tree theorem is neither a lower bound for this weaker encoding nor a minimum installed-state theorem, and refinement need not preserve width or state count. |

The new mathematical content is the repo-derived actual native
$P_{28}/P_{16}/P_{18}/P_{30}$ immediate-write construction and the
all-budget four-bit obstruction. The frontier combines them with the
reused two-Read endpoint. These are ordinary conditional statements;
no global literature novelty is assigned to the finite native increment.

The minimum installed-state count and minimum running-state count at
five bits are unresolved here; twelve and four are attained counts.
Best peak and summed address costs, their joint optimization with other
resources, and total physical cost remain unresolved. Allowing explicit
internal write phases defines a different competition and its tradeoffs
are not supplied by these theorems. Genuine acquisition, stationarity,
discard, compilation and physical interface availability remain premises.

The recovered integer is the substitution count relative to the acquired
original, not elapsed physical time. The cut and entire boundary row are
already acquired; they are not recovered by the controller. The six
origins $(j,15)$ still share the same reply transcript and halt, so the
result does not reconstruct all original trees. It gives one exact
exchange of chronological interaction allowance against legal internal
memory geometry at this fixed fiber, not a uniform frontier over other
labels, cuts, acquired rows or unbounded lags.

[NARC-3R-parent]: https://github.com/the-omega-institute/trureturing/blob/570727d8fa74341c576bee694ff0e2cd4e79b936/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md
[Nowak-3R]: https://arxiv.org/pdf/0910.4397v5
[BC-3R]: https://www.cs.toronto.edu/~bor/Papers/time-space-tradeoffs-sorting-general.pdf
[Bryant-3R]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
[CEK-3R]: https://arxiv.org/pdf/0903.2507v1

## 追加锚（本行以下为增补区）
## 25. Counted internal processing on the same acquired fiber

**Assumption 25.1 (query, internal and halt rows in one complete word).**
Retain Assumption 17.1, Proposition 17.2's entire fifteen-origin fiber,
Definition 17.3's complete numeric lag target, and the stationary native
Read interface. For a positive integer $d$, install any subset
$W\subseteq V(\Gamma_d)$, with $\Gamma_d$ as in (NARC.17.6), and
one common initial word $w_0\in W$. Partition the installed words as
$W=Q\sqcup I\sqcup H$. Each word has exactly one immutable row:

- A query word $q\in Q$ submits one fixed fully materialized
  original-root literal $\operatorname{addr}(q)\in\{L,R\}^\ast$.
  Its total row $\delta(q,\cdot):\mathcal A\to W$ immediately uses
  the actual reply to choose the same word or one legal bit flip,
  and then discards the reply.
- An internal word $i\in I$ has one predetermined successor
  $\eta(i)\in W$, again the same word or one legal bit flip. It
  obtains no source input, performs no Read and emits no target output.
- A halt word $h\in H$ contains one fixed complete natural-number
  output $\lambda(h)$ and has no outgoing step.

The current word contains all mutable accessible configuration. Row
type and every choice above depend only on that word, with the current
reply used solely by its query row's immediate response update. There
is no separately accessible reply, program counter, actuator phase,
clock, history, counter, mutable address, output accumulator, conditional
external decoder or source-bearing input. The acquired entry and all
compilation workspace are closed after the common installation and
initialization. Immutable instruction, address and complete-output
storage, its access, acquisition, compilation and atomic writing remain
separately stipulated and charged services, as in §§17 and 20.2.

For each actual original $(a,b)\in C$, run on its own stationary
$Y_{a,b}$ from the common $w_0$. Require a finite first halt with
output $17-b$, at most $k$ chronological Reads, and finitely many
internal steps. Every invocation counts, including a repeated literal.
Every intermediate word is installed and counted. Initial internal
processing, shared states and paths, duplicate outputs at different
halts, arbitrary literals, unused rows, unsupported self updates and
cycles in the union of different-source transitions are permitted.
No global directed acyclic graph or tree topology is assumed.

This explicitly enlarges the query/halt-only operational contracts of
Assumptions 17.4 and 21.1 by allowing counted internal rows. It leaves
their no-extra-phase theorems under their stated hypotheses.

**Definition 25.2 (enlarged competition and separate logical counts).**
Let $\mathfrak W_{\rm int}(k,d)$ be all installations satisfying
Assumption 25.1, at every installed-state count. Define

$$
\begin{aligned}
L_{\rm int}(k)&=\min\{d\ge1:
              \mathfrak W_{\rm int}(k,d)\ne\varnothing\},\qquad
              \min\varnothing=\infty,\\
N_{\rm int}(2)&=\min\{|W|:d\ge1,\quad
              \mathcal K\in\mathfrak W_{\rm int}(2,d)\}.
\end{aligned}
\tag{NARC.25.1}
$$

On one actual path through its first halt, count Reads $r$, internal
steps $u$, response bit writes $b_Q$, internal bit writes $b_I$, and
submitted literal lengths separately. A same-word update contributes
one step of its row type and zero bit writes. Initialization is a
separate account. Hidden age, Read index, remaining budget and path
position are proof coordinates, never row inputs. Thus $r+u$ measures
primitive recovery transitions, whereas $r$ measures new interactions
with the stationary source.

**Lemma 25.3 (actual repetition and source-independent internal paths).**
In any successful installation of Assumption 25.1, a running word is
visited at most once on each actual first-halt path. Sources that enter
one common word follow the same internal path until the next query or
halt. If no further Read is allowed on those sources, their common
word determines one complete eventual output. Consequently

$$
r+u\le |Q|+|I|,\qquad b_Q=r,\qquad b_I=u
\tag{NARC.25.2}
$$

on every successful actual path, with initialization excluded.

**Proof.** Fix the actual source. A query's fixed literal has one
fixed actual reply on this stationary source. Together with the fixed
rows, this defines a deterministic next-word function on running
words. A repeated running word repeats its entire future; the segment
between repetitions becomes periodic and cannot later reach a first
halt. In particular no actual same-word update can terminate later.
Each successful transition therefore changes one bit, and distinct
running visits give all three counts in (NARC.25.2).

An internal row has the same successor for every source. Induction
along internal rows gives a common path until a query or halt. This
path is finite on a nonempty actual arriving support because every
member first halts. If no further query may execute, the path ends
at one fixed-output halt. Two different required outputs cannot merge
at a common word after their respective last Reads. None of these
claims restricts unsupported source-word pairs or cycles assembled
from different actual sources. $\square$

## 26. The actual-arrival and last-Read output-port lemma

**Lemma 26.1 (separate entry and output neighbors).** More generally,
let complete configurations be vertices of a simple graph $G$, with
self updates also permitted. Give them fixed query/internal/halt rows,
source-independent internal successors, and fixed complete halt outputs.
A query has a fixed response-to-successor map and discards the reply
at that update. On a stationary source $s$, its fixed experiment has
one fixed actual reply $r_q(s)$; no row reads an additional phase.
Require every nonself response or internal update to be an edge of $G$.
Suppose a query vertex $q$ occurs as the last Read on a collection
$\mathcal S$ of actual terminating runs requiring $m\ge1$ distinct
complete outputs. Suppose also that there is a genuine immediate
actual arrival $p\to q$, with $p\ne q$. Then $q$ has $m$ distinct
nonquery immediate response-successor neighbors and a further distinct
incoming neighbor $p$. In particular,

$$
\deg_G(q)\ge m+1.
\tag{NARC.26.1}
$$

The arrival may be on any actual run of this same fixed-row controller;
it need not be the source chosen to witness one of the $m$ outputs.
Other uses of $q$ need not be last Reads. Under stationary actual
first-halt termination, every noninitial visit supplies a nonself
predecessor, by Lemma 25.3.

**Proof.** Choose one visit from $\mathcal S$ for each distinct
required output, and let $v_j$ be its immediate post-reply word.
Each $v_j$ is nonquery: otherwise that run would execute another
Read. In particular $v_j\ne q$, so $v_j$ is a neighbor of $q$.
From $v_j$ the chosen run follows only fixed internal rows to a
fixed-output halt. If $v_j=v_l$, those internal paths and final
constants coincide, contradicting the two different required outputs.
Hence the $m$ response successors are distinct.

The actual predecessor $p$ is a further neighbor, since its transition
is nonself. It cannot be a halt. If it is query, it differs from every
nonquery $v_j$. If it is internal, its fixed next word is $q$.
Selecting $v_j=p$ after the last Read would therefore execute
$q\to p\to q$ on that chosen source and issue another Read.
This again contradicts lastness, irrespective of which actual source
witnessed the incoming edge. Thus $p$ is distinct from every $v_j$.
These are $m+1$ distinct neighbors. $\square$

**Proposition 26.2 (the arrival hypothesis and fixed-row boundary).**
An initial query without an actual incoming transition need not have
the additional neighbor in (NARC.26.1). A processing word used both
before and after $q$ cannot evade Lemma 26.1 by changing its behavior
unless the complete configuration or the fixed-row hypotheses change.

**Proof.** For the first assertion, use the legal words
$0000,1000,0100,0010,0001$ of $\Gamma_4$. Make $0000$ the
initial query; assign its four replies in order to those four unit-word
halts, with complete outputs $1,2,3,4$, respectively. Let the four
stationary sources be indexed by $o\in\mathcal A$ and define that
query's observation on source $o$ to be $o$. Each first halts in one Read.
The query has degree four, exactly the four output neighbors, and
has no actual incoming transition. This is a counterexample to an
unconditional fifth-neighbor requirement, not a controller for the
fifteen-origin native task.

For the second assertion, a fixed internal predecessor necessarily
returns to $q$ if selected as a response successor. Routing toward
$q$ before acquisition but toward a halt afterward requires a retained
reply, phase, history or other distinction. If that distinction is
accessible, it belongs in the complete word; the two configurations
then count separately. Permitting another query after $q$ also removes
the selected last-Read hypothesis. $\square$

## 27. Exhaustive native query rigidity with internal paths

**Theorem 27.1 (forced functions, without direct query adjacency).**
Every controller in $\mathfrak W_{\rm int}(2,d)$ has three distinct
reached query words $R,A,B$. All sources first query $R$, with
function $P_{27}$. Its absence support $D_L$ follows a common internal
path to second query $A$, whose function is $P_{16}$. Its branch
support $D_U$ follows a common internal path to second query $B$,
whose function is $P_{30}$. Every member of those two supports has
its last Read there. Thus $A$ requires three distinct complete outputs
and $B$ four. Direct edges $R-A$ and $R-B$ are not part of this
conclusion.

**Proof, exhaustive literal functions.** On the exact sources
$Y_{a,b}=\langle T_n,T_{33}\rangle$, every original-root literal
is $\varepsilon$, $Rp$ or $Lp$. The empty word returns branch;
$Rp$ reads the same $T_{33}$ for all origins and is constant, even
when absent. The word $Lp$ has exactly the relative reply on $T_n$.
An empty relative suffix gives $E$, constant branch on $D$.

The native laws of Definition 5.3 and (NARC.18.2) cover every nonempty
relative word as follows. Give $L$ weight one and $R$ weight two.
For $p\ne\varepsilon$, every edge requires its proper-prefix filling
to be a branch. The last such guard is strongest, because prefix
weights strictly increase. Writing $p^-$ for deletion of the final
letter, traversal is possible precisely when
$n\ge w(p^-)+2$. When reached, the filling is $T_{n-w(p)}$.
If the final letter is $R$, let $t=w(p)\ge2$; the guard is
$n\ge t$ and the function is $P_t$. If the final letter is $L$,
let $t=w(p)+1\ge2$; the guard is again $n\ge t$ and the function
is $S_t$. Explicitly, in reply order,

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\ \hline
P_t&n<t&n=t&n=t+1&n\ge t+2\\
S_t&n<t&\text{never}&n=t&n\ge t+1.
\end{array}
\tag{NARC.27.1}
$$

There is no $P_1$; the relative weight-one word $L$ realizes $S_2$.
Arbitrarily long literals and uniformly absent functions are included.
This correspondence reuses the literal laws, without turning hidden
age or query indices into runtime inputs.

**Proof, one remaining Read after internal processing.** Suppose an
actual support enters a common word with at most one Read remaining.
By Lemma 25.3 it follows one common internal path to a halt or query.
A halt requires a constant target. A query has at most four realized
reply cells; each immediate successor must then follow an internal-only
path to a fixed-output halt. Its reply cells must therefore be
target-constant. This necessary condition includes arbitrary processing
before and after that remaining Read and all merged arriving supports.

Use the actual subset $D_0=\{2,16,17,18\}$, with full outputs
$(2,16,16,17)$. For $P_t$ with $t\le15$, ages $17,18$ both
return branch but require different outputs. For $t\ge17$, ages
$2,16$ both return absence but require different outputs. Only
$P_{16}$ survives, and it solves all $D_L$, with output tuple
$(2,16,16,17)$ in reply order. For $S_t$, $t\le16$ merges
$17,18$ in branch, while $t\ge17$ merges $2,16$ in absence.
Constants fail. Thus $P_{16}$ is the only one-Read solver function
for $D_0$, and consequently for $D_L$.

The set $D_0\cup\{27\}$ has no one-Read solver: its sole candidate
$P_{16}$ merges $18,27$ in branch, with outputs $17,12$.
It cannot halt at one constant either.

**Proof, the first query.** Seven required outputs prevent a common
initial halt. The source-independent initial internal path therefore
ends at a common first query $R$. A constant first function leaves
seven outputs for one remaining four-valued Read and fails.
If its function is $P_t$ with $t\le26$, the branch cell contains
$28,29,30,31,32$, with five distinct outputs $13,14,15,16,17$.
If $t\ge28$, the absence cell contains $D_0\cup\{27\}$, which
the preceding argument excludes. Thus only $P_{27}$ survives.
For $S_t$, $t\le27$ has the same five-output branch obstruction,
and $t\ge28$ has the same unsolvable absent subset. These cases
exhaust every native first function, including $E$ and constant
original-root queries.

**Proof, the second queries and actual arrivals.** The $P_{27}$ cells
are $D_L,\{27\},\{28\},D_U$. Every member of one cell has the
same immediate successor and follows the same internal path until
a query or halt. Both $D_L$ and $D_U$ are target-nonconstant,
so their paths reach respective second queries $A,B$. The lower
subset argument forces $P_{16}$ at $A$.

On $D_U=\{29,30,31,32\}$, four different outputs require four
different replies. Constants and every $S_t$ have too few. For
$P_t$ with $t\le29$, ages $31,32$ merge in branch; with $t\ge31$,
ages $29,30$ merge in absence. Only $P_{30}$ works, with output
tuple $(14,15,16,17)$. The fixed functions $P_{27},P_{16},P_{30}$
are different on $D$, so $R,A,B$ are distinct complete words.
The lower and upper runs already read $R$; their visits to $A,B$
are second and last Reads. Each has an actual immediate predecessor
different from itself, by Lemma 25.3, however long its internal
arrival path. No contraction of that path gives a new cube edge.

The singleton first replies $27,28$ have not been assumed to halt
immediately or to remain separate: they may merge and use another
second query. Adding their support to a shared word can only add
requirements. In particular they cannot join the lower path to $A$,
whose $P_{16}$ branch already serves output $17$ at age $18$;
their required outputs are $12,13$. They cannot join the upper path
to $B$, whose $P_{30}$ absence already serves $14$ at age $29$.
Any shared internal path into either query has that same conflict.
The forced lower and upper paths cannot merge before their second
query, since their union requires five different outputs. Other
shared paths and equal-output suffixes remain allowed. $\square$

## 28. Universal five-bit exclusion and eleven installed states

**Theorem 28.1 (all legal installations fail at five bits and two Reads).**
For every positive $d\le5$,
$\mathfrak W_{\rm int}(2,d)=\varnothing$. This exclusion permits
arbitrary finite internal processing and every installed subset.
Zero-length words likewise fail if admitted.

**Proof.** At zero length the sole word cannot supply seven distinct
halt outputs. For positive lengths, apply Lemma 26.1 to the actual last-Read supports of
Theorem 27.1. The three complete outputs at $A$ and four at $B$
require

$$
\deg_{\Gamma_d}(A)\ge4,\qquad
\deg_{\Gamma_d}(B)\ge5.
\tag{NARC.28.1}
$$

For $d<5$, the second inequality exceeds the maximum possible
one-bit degree $d$. For $d=5$, the complete ambient degree roles are:

| Ambient degree | All legal words with that degree |
| --- | --- |
| $5$ | `00000` |
| $4$ | `00001`, `10000` |
| $3$ | `00010`, `00100`, `00101`, `01000`, `10001`, `10100`, `10101` |
| $2$ | `01001`, `01010`, `10010` |

These are the thirteen legal words, exhausted by the disjoint
initial-$0$/initial-$10$ recursion. Their degrees follow by removing
any existing one or inserting a one precisely at a zero with no
neighboring one. Equivalently the degree is five minus the number
of zero positions blocked by adjacent ones. This gives every role
in the table. The unique degree-five and two degree-four counts are
also the literature-attested cases $n=5,m=0,1$ of
[Klavžar--Mollard--Petkovšek, Corollary 3.4][KMP-RW], manuscript p.7;
both meet $n\ge2m+2$. These classical graph facts are intermediate
premises of the native obstruction.

Necessarily $B=00000$. Since $A\ne B$ and has degree at least four,
$A$ is `00001` or `10000`. Either is an ambient neighbor of $B$.
Choose an actual upper-support arrival $p_B\to B$. The last-Read
lemma requires four distinct nonquery response successors of $B$
and the separate neighbor $p_B$. None of the four successors can
be $A$, which is query. Nor can $p_B=A$: that upper source would
execute $R$, then $A$, then $B$, giving three Reads. Equivalently,
its path after $R$ and before $B$ consists only of internal rows.
Thus all five required neighbors avoid $A$, while $B$ has only
five ambient neighbors including $A$. This is impossible.

The $A-B$ edge here is ambient adjacency, not an asserted executed
transition. Every required arrival and successor must be installed;
deleting ambient words cannot increase degree. Extra internal or
query rows, empty-support rows and duplicate halts cannot supply
the missing neighbor. Shared internal suffixes cannot reduce the
number of different-output successors, by Lemma 25.3. Unsupported
self loops and cycles formed by different source supports remain
permitted. Only actual terminating paths enter the contradiction.
Hence no additional controller configuration or topology assumption
is omitted. $\square$

**Theorem 28.2 (exact two-Read installed-state minimum).** Over all
finite word lengths in Assumption 25.1,

$$
N_{\rm int}(2)=11.
\tag{NARC.28.2}
$$

**Proof.** Seven distinct full lag outputs require seven distinct
halt words. Theorem 27.1 requires three distinct query words $R,A,B$,
disjoint from them. Fewer than ten installed words are impossible.
If exactly ten are installed, these exhaust $W$: there are no
internal rows, additional queries, duplicate halts or unused words.
The common initial word is consequently $R$. Its forced lower and
upper transitions are now genuine direct one-bit edges to $A,B$.
The unique halt $H_{16}$ for output sixteen and the unique halt
$H_{17}$ for output seventeen are each direct response successors
of both second queries. Thus $A,B$ have three distinct common
neighbors $R,H_{16},H_{17}$, forming a $K_{2,3}$ subgraph.

The classical cube obstruction of [Havel--Morávek, Propositions
1--2 and Example 1][HM-RW-full], pp.340--342, applies to injective
adjacency-preserving coding. Directly, two distinct binary words
with a common one-bit neighbor differ in exactly two coordinates.
Their only common neighbors are the two words obtained by changing
one or the other differing coordinate. They cannot have three.
Every $\Gamma_d$ is a cube subgraph, so ten installed words are
excluded at every finite width. Here the absence of internal words
is deduced from equality in the state count; internal paths have
not been contracted to manufacture the three edges.

For the upper bound, Definition 19.1 and Proposition 19.2 already
supply the complete eleven-word, six-bit, two-Read installation and
all fifteen actual first halts. Interpret its running rows as query
rows and take $I=\varnothing$. Its total successors, initial word
and full halt constants are unchanged. It satisfies Assumption 25.1
and attains eleven. $\square$

## 29. The enlarged all-budget frontier and separate costs

**Theorem 29.1 (four-bit obstruction including internal rows).**
At $1\le d\le4$, no installation of Assumption 25.1 can correctly
first halt on the whole fiber, even if only eventual finite termination
is required with no common Read cap.

**Proof.** Legal-word counts obey $a_0=1,a_1=2$ and
$a_d=a_{d-1}+a_{d-2}$ for $d\ge2$, by the disjoint $0$ and
$10$ prefixes. Thus $a_4=8$, and shorter lengths have fewer words.
The seven complete outputs need seven different reached halt words.
At most one installed running word remains, now counting both
query and internal rows. An initial halt cannot solve a nonconstant
target. If the sole running word is internal, there is no query;
its source-independent path yields only one output. If that word
is query, there is no internal row or other query. Each successful
actual successor must be a halt: a self successor repeats the same
stationary running word forever by Lemma 25.3. Four replies yield
at most four full outputs, contradicting seven. Duplicate halts and
unused rows consume the same eight-word capacity. This directly
covers internal rows; it does not infer the enlargement from Theorem
23.1's query/halt-only statement. $\square$

**Theorem 29.2 (unchanged entire finite Read/width frontier).**
For the same acquired fiber and the conditional services of Assumption
25.1, the frontier is

$$
\boxed{
L_{\rm int}(k)=
\begin{cases}
\infty,&k=0,1,\\
6,&k=2,\\
5,&\text{every finite integer }k\ge3.
\end{cases}}
\tag{NARC.29.1}
$$

In particular finite internal single-bit processing does not improve
Definition 21.2's width frontier, and the minimum worst-case Read
count at five bits remains exactly three.

**Proof.** With zero Reads, all sources follow one common internal
execution and produce one output. With at most one Read, common
initial processing reaches one common query or halt. Each of that
query's four replies selects an internal-only suffix to a fixed-output
halt. At most four different outputs are possible, at every finite
width. Seven outputs make both budgets impossible.

At two Reads, Theorem 28.1 excludes every width at most five;
the unchanged certificate of Definition 19.1 and Proposition 19.2
gives width six. At every finite $k\ge3$, Theorem 29.1 excludes
all widths at most four. Definition 22.1 and Theorem 22.2 give
the complete five-bit, twelve-word certificate with at most three
Reads. Taking $I=\varnothing$ makes it an unchanged member of
$\mathfrak W_{\rm int}(k,5)$ for each larger at-most budget.
These are exactly the existing attained endpoints, including their
total rows and all fifteen same-source first-halt traces. They are
reused without a new construction or duplicated table. The new
lower bounds establish their robustness in the larger controller
family. Comparison with (NARC.23.2) gives the stated equality of
frontiers. $\square$

**Proposition 29.3 (processing, interaction and the extended account).**
In Assumption 25.1 the exact frontier concerns mutable recovery width
and chronological Reads. An actual path has a separate service account

$$
\begin{aligned}
\mathcal C_{\rm int}={}&C_{\rm setup}+C_{\rm immutable}\\
&+\sum_{t:w_t\in Q}
 \bigl(C_{\rm table}(w_t)+C_{\rm submit}(p_t)
       +C_{\rm Read}(p_t,Y_{a,b})
       +C_{\rm response\ write}(w_t,o_t)\bigr)\\
&+\sum_{t:w_t\in I}
 \bigl(C_{\rm table}(w_t)+C_{\rm internal\ step/write}
          (w_t,\eta(w_t))\bigr)\\
&+C_{\rm table}(h)+C_{\rm output}(17-b),
\end{aligned}
\tag{NARC.29.2}
$$

where $C_{\rm setup}$ retains every acquisition, export/discard,
continuation, later capture/parse, compilation/installation and
initialization charge of (NARC.20.5). Use nonnegative scalar or
vector accounts without double counting shared services. Peak storage
and other nonadditive resources require their own composition rule.

**Proof.** Sum each row's supplied services along this same actual
path. A query obtains a new native reply; an internal row acquires
nothing and has its own access, processing and write charge. The
terminal service emits the full installed constant. Setting
$I=\varnothing$ recovers the account of Proposition 20.2. Both
reused certificates have $u=b_I=0$ on all fifteen paths, and their
$r,b_Q$, address peaks and sums are precisely Proposition 19.2,
Theorem 22.2 and Proposition 24.2. Their attained resource triples
$(d,|W|,\max r)$ remain $(6,11,2)$ and $(5,12,3)$.

The three-Read certificate changes the information schedule as in
Proposition 24.1: ages $18,27$ share the $P_{16}$ branch word but
require outputs $17,12$. Fixed internal processing from that word
cannot distinguish them; its $P_{18}$ query acquires the needed
distinction. Theorem 28.1 excludes every redesigned five-bit two-Read
controller, not merely substitution of internal rows in this table.
Entry and completed-answer routing compete in the last query's
neighborhood even when internal time is allowed.

Neither witness uniformly reduces sourcewise Read cost: age $27$
uses one versus three Reads, while age $29$ uses two versus one.
Literal letters are logical address costs, not physical latency.
The eleven/twelve installed-word counts and forty/fifty independently
stored literal letters retain their representation-specific meanings
from §§20.2 and 24.2. Conditional service availability and immutable
storage are additional to five or six mutable recovery bits.
Equation (NARC.29.2) therefore supplies no total physical storage,
time, energy or scalar-cost optimum. $\square$

## 30. Operational suppliers and the retained recovery boundary

**Definition 30.1 (exact source and operational correspondences).**
The native task and attained endpoints are [§§17--24 at the immutable
native source][NARC-IP-parent]: Assumption 17.1 supplies the common
acquired entry and services, Proposition 17.2 both directions of the
exact actual fiber, Definition 17.3 the full target, and Definition
5.3 the guarded native literals. Definitions 19.1 and 22.1 and their
Proposition 19.2 and Theorem 22.2 supply the reused complete tables
and first-halt traces. Assumptions 17.4 and 21.1 restrict their original
competition to query/halt rows; Assumption 25.1 changes that restriction.
Theorem 27.1 re-establishes forcing for internal paths and does not
import Theorem 18.1's direct $R-A,R-B$ adjacency.

The following suppliers match portions of the operational semantics;
the ordinary correspondence keeps every intermediate complete word.

| Supplier | Parameter and relation correspondence | Boundary |
| --- | --- | --- |
| [FIB §§26--27 and 45--47][FIB-RW] | Target $z=17-b$, source $s=Y_{a,b}$, and exact support $C_w$ consisting of the actual target-source pairs reaching $w$. A query has identity source transition and its native reply; an internal action has identity source transition and constant observation. Remaining primitive transitions to first halt give a rank on $(z,s,w)$. | Theorem 27.2 then counts all actions, including internal ones, not only Reads. Rank is proof data. Definition 45.1 itself excludes intermediate instructions; its immediate-edge criterion cannot be applied to contracted internal paths. Section 47's finite-history refinement can change both width and installed-state budgets. |
| [DecoderOperationTrace][IP-Trace] | Take configuration type $C=W$ and input alphabet $I=\mathcal A$. Query $q$ maps to acquire with successor $o\mapsto(\delta(q,o),[])$; internal $i$ to internal with successor $\eta(i)$ and empty output batch; halt to stopped with a separate fixed terminal label $\lambda$. | Generate each source's adaptive actual reply sequence from its requested literals, extending only after first halt. Induction identifies the consumed reply with $\operatorname{Read}(Y_{a,b},\operatorname{addr}(q))$; an arbitrary external stream is not an extra source oracle. Every trace vertex is counted. Acquired-input and output fields are proof bookkeeping, not row arguments. |
| [NativeExecutionTransport and its GuardedPhaseExecution import][IP-Transport] | Take control type $W$, addresses the literal words, replies $\mathcal A$, and $\operatorname{obs}(j,p)=\operatorname{Read}(Y_{a,b},p)$ independent of $j$. Query/internal/halt rows match read/update/halt, with terminal labels separate. | Exact instruction and observation compatibility under a control equivalence and address map permits run transport, including address collisions. The update epoch advances on internal updates; Read does not advance it. That proof epoch is neither unknown lag nor an accessible runtime clock. Word legality and costs require their own correspondence. |

For the trace correspondence, step uniqueness and internal-drain
acquisition invariance express determinism and absence of new input
during processing. Stationary repeated-word consistency still uses
the native-source correspondence of Lemma 25.3, not uniqueness for
an arbitrary changing input stream. The supplier's `actual_cut_exists`
requires unbounded output liveness on its selected streams. Finite
first halts with empty operational output batches do not satisfy that
hypothesis, so its liveness conclusion is not transferred.

The classical encoding premises remain those attached to Theorems
28.1--28.2: Fibonacci-cube degree roles and the Havel--Morávek
adjacency-preserving cube obstruction. Neither induced nor isometric
embedding is required. Generic tree refinements in FIB47 give
existence at changed budgets, not a fixed-five-bit competitor.
The arrival/output lemma is proved here under its actual-arrival
and fixed-row hypotheses; it is not attributed to those graph papers.

[Borodin--Cook, §2, p.289][BC-3R], *A Time-Space Tradeoff for Sorting
on a General Sequential Model of Computation*, SIAM Journal on
Computing 11(2), 287--297 (1982), DOI
[10.1137/0211022](https://doi.org/10.1137/0211022), distinguishes
input-access depth from logarithmic program-node capacity and expressly
abstracts storage representation and manipulation between accesses.
This is the relevant resource comparison: the present model instead
charges internal rows and constrains every mutable transition. Their
sorting lower bound, leveled directed acyclic graph and capacity
measure do not supply the native frontier or authorize a free program
counter. Unrolling actual paths need not preserve installed-state count.

The new repo-derived conditional content is the internal-path rigidity,
the consumed general last-Read entry/output lemma, and their enlarged
controller exclusion and frontier consequences. The existing endpoint
certificates and classical graph facts are reused. No global originality,
new Lean evidence or physical interface realization is asserted.

The exact eleven-state minimum applies at two Reads. Twelve words
remain an attained three-Read count; no minimum-twelve theorem,
optimal internal-step/write count, address optimum or immutable-storage
optimum follows. All acquisition, stationarity, discard and service
premises remain explicit. The target is one substitution lag on this
fixed acquired fiber. The cut and entire later boundary row are already
acquired, and equal lag outputs still merge distinct originals and
hidden trees. Neither full spatial reconstruction, elapsed physical
time nor a uniform result over other labels, rows, cuts or unbounded
lags follows from (NARC.29.1).

[NARC-IP-parent]: https://github.com/the-omega-institute/trureturing/blob/a005e8ce6a54bf153892e359522aaf436c54eb85/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md
[IP-Trace]: https://github.com/the-omega-institute/trureturing/blob/f5f62083edaef047ada3f01fd44fa94c0f03afd5/D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.lean
[IP-Transport]: https://github.com/the-omega-institute/trureturing/blob/6053f37a2c61f3ddb2c275b437184f623d4c06f0/D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport.lean

## 追加锚（本行以下为增补区）

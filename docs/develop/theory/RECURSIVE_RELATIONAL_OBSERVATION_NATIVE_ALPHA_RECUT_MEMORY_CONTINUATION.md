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

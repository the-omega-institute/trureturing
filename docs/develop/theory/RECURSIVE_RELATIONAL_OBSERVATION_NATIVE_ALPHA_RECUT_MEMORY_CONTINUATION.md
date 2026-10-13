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

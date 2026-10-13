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

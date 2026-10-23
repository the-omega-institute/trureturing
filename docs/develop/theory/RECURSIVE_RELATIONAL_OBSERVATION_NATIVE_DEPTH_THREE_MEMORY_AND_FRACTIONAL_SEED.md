# Recursive relational observation: native depth-three memory and a fractional seed

## 1. The stationary native interface

**Definition 1.1 (actual sources, literals and requests).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,
\qquad h(\langle x,y\rangle)=1+\max\{h(x),h(y)\}.
$$

Pairing is ordered. For every finite word $w$ in $L,R$, including
$\varepsilon$, the literal reply $r_t(w)$ is alpha or beta at a leaf,
branch at a pair, and absent beyond a leaf. Every such word is legal.
Define the homomorphism

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{D3.1}
$$

For each public integer $D\ge1$, use exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},
\qquad W_D=\{q:|q|\le D-1\},
\qquad\mathcal P_D=\{Rq:q\in W_D\}.
\tag{D3.2}
$$

One actual initial source remains stationary throughout acquisition;
$\rho^kt$ is a prediction target. There is no subtree, equality,
source-identity, age, reset, copying, navigation or free-advice port.
Child notation denotes a mathematical component, never an additional
operational input. These are the source and task of
[LTR, Definitions 1.2–1.4](RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_ONE_READ_MEMORY.md).
In
[`GenealogicalFiberTransport`](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
`Source` is `FreeMagma Bool`, true labels alpha, false labels beta,
and `substitution` is (D3.1). In
[`ActualTreeReadoutAcquisition`](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean),
`Address` is `List Bool`, false means $L$, true means $R$, and
`Reply` and `readout` give precisely these four replies on every finite
word. Its separate recognition objective is not the prediction task.

**Assumption 1.2 (complete paid export and late prediction).** A single
deterministic effective preparation starts from common source-independent
initialization, with public $D$ and common installed tables. It does not
receive the later request. Every acquired source distinction comes from
charged original-root literal Reads. It terminates on every source and
exports a finite code $E(t)$. All accessible surviving source dependence
is included in that code: selectors, operands, buffers, transcripts,
control, lengths, allocation, handles, counters and accessible timing
distinctions. Any other accessible field is a fixed function of the code
and public data. A separately paid handoff isolates every other acquired
distinction, including earlier transcripts, and supplies lawful reader
entry. Source continuity, isolation, export, entry and authentication are
declared services, without an assumed physical erasure operation.

Only after export is a public source-independent $p\in\mathcal P_D$
supplied. One common deterministic effective reader, given $E(t),D,p$
and the common tables, chooses at most one fresh literal Read of the same
stationary source. Its word can be any finite original-root word chosen
from those inputs. Zero-Read branches are permitted. It exports a final
predictor $Z$ satisfying

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad\text{for every }t\in\mathcal F_D,
\ p\in\mathcal P_D,\ k\ge0,
\tag{D3.3}
$$

with no further Reads. The authentic integer $k$ is supplied only after
the query; it is not acquired or authenticated by the predictor itself.
Define

$$
M_1(D)=\min |E[\mathcal F_D]|.
\tag{D3.4}
$$

Only the complete attained retained alphabet is optimized. Preparation
work and workspace, installed tables, post-request workspace, final
predictor size, submitted address length and letters, count
representation, paid services and physical time are separate resource
coordinates. This is LTR's handoff contract, rather than an inference
of these services from the tree algebra. The paid common-start interface
of [NBP, Assumption 14.1 and Theorem 14.4](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md)
has a different known-row predecessor objective.

**Definition 1.3 (the supplied all-count factor).** Put
$s(q)=\#L(q)+2\#R(q)$ and $e(\alpha)=0,e(\beta)=1$. Use the
factor $\Gamma_q(u)=(b,c)$ of
[AAR, Definition 12.2, Theorem 12.3 and Proposition 13.3](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md).
It is $(0,0)$ at an original branch endpoint. Otherwise let $\ell$
be the first original leaf along $q$, at address $a$, and write $q=ar$.
Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{D3.5}
$$

The supplied factor law and decoder are

$$
r_{\rho^ku}(q)=\operatorname{Pred}(\Gamma_q(u),k),\qquad
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{D3.6}
$$

On attained factors $c=1$ implies $b\ge2$. Conversely the complete
trajectory determines $b$ as its first branch count and $c$ by the
presence of an alpha stage. Thus equality of factors is exactly equality
of all-count trajectories. In the actual wrapper,

$$
\Gamma_{Rq}(\langle\alpha,v\rangle)=\Gamma_q(v),\qquad
r_{\rho^k\langle\alpha,v\rangle}(Rq)=r_{\rho^kv}(q),
\qquad b\le2D.
\tag{D3.7}
$$

These are reused temporal laws, including the last-edge guard for an
initially absent target. The original blocking leaf is actually present;
transport is not applied at the absent target. The corresponding
`original_present_transport` in
[`NativeDepthPatterns`](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean)
has precisely that presence premise; `original_prefix_locality` supplies
all-count dependence on the original finite boundary. AAR's passive
fixed-menu quotients and known-menu acquisition theorems retain their
original request order.

**Definition 1.4 (canonical native fibers and fractional covers).** Write

$$
A=\alpha,\quad B=\beta,\quad C=\langle A,A\rangle,
\quad T=\{A,B,C\},
\quad\mathcal G=\{g_{xy}=\langle x,y\rangle:x,y\in T\},
$$

$$
S_1=T,\qquad S_{d+1}=\{A,B\}\sqcup
\{\langle x,y\rangle:x,y\in S_d\},\qquad N_d=|S_d|.
\tag{D3.8}
$$

Thus $S:=S_2=\{A,B\}\sqcup\mathcal G$ has eleven actual trees, and
$S_3=\{A,B\}\sqcup\langle S,S\rangle$ has $123$, where
$\langle X,Y\rangle=\{\langle x,y\rangle:x\in X,y\in Y\}$.
The depth-three target menu is

$$
W_3=\{\varepsilon,L,R,LL,LR,RL,RR\}.
$$

A nonempty $H\subseteq S_d$ is admissible if, for every $q\in W_d$,
the factor $\Gamma_q$ is constant on $H$ or there is an $a\in W_d$
such that

$$
u,v\in H,\quad r_u(a)=r_v(a)
\quad\Longrightarrow\quad \Gamma_q(u)=\Gamma_q(v).
\tag{D3.9}
$$

The witness may depend on both $H$ and $q$ and may be off-target.
Let $\mathcal H_d$ be all admissible sets and define

$$
z_d=\min\left\{\sum_{H\in\mathcal H_d}w_H:
w_H\ge0,\quad\sum_{H\ni u}w_H\ge1\ (u\in S_d)\right\}.
\tag{D3.10}
$$

Here the canonicalization $\pi_d(v)$ keeps all reached constructors
through depth $d-1$, replacing each branch at that depth by $C$.
[FMR, Lemma 2.2 and Theorems 2.3–2.5](RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md)
supply the exact integral-cover correspondence with $M_1(d)$, the
factor equality $\Gamma_q(\pi_d(v))=\Gamma_q(v)$, and simulation of
every arbitrary longer native word. On $S_d$, a length-$d$ word returns
alpha exactly when its length-$(d-1)$ parent is branch and otherwise
absent; longer words are absent. The outer root and left cone have
source-independent replies. Thus this finite menu retains every
original experiment without restricting queries to target prefixes.
The canonical boundary is actually acquired at all words $Rq$,
$q\in W_d$, with sufficient costs

$$
T_{\rm prep}\le2^d-1,\qquad Q_{\rm prep}\le d,\qquad
A_{\rm prep}\le(d-1)2^d+1.
\tag{D3.11}
$$

On a fixed fiber (D3.9) is a functional dependency from one reply
column to one target column of a finite relation. This is the relation
notion in Gogacz–Toruńczyk,
[*Entropy bounds for conjunctive queries with functional dependencies*,
arXiv:1512.01808v1](https://arxiv.org/html/1512.01808v1).
Their fixed-schema entropy exponents do not identify a cover whose
dependency witness varies with the fiber and target. In Gál–Miltersen's
systematic-storage model,
[*The Cell Probe Complexity of Succinct Data Structures*, BRICS RS-03-44](https://www.brics.dk/RS/03/44/BRICS-RS-03-44.pdf),
the preserved input and retained index correspond to the native boundary
reply array and $E$. Here that array is constrained by tree syntax, the
whole code is accessible, acquisition is charged, and one four-symbol
source reply is the later probe. Likewise the sketch in Garg et al.,
[*Systematic Data Structure Lower Bounds via the Query-with-Sketch
Model*, Definition 2.1, arXiv:2609.18024v1](https://arxiv.org/html/2609.18024v1),
precedes coordinate probes, but its matrix problem and conditional
min-entropy hypotheses supply no numerical native bound here.
Narodytska et al.,
[*Learning Optimal Decision Trees with SAT*, IJCAI 2018, §§2–3](https://www.ijcai.org/proceedings/2018/0189.pdf),
use binary features and tree-size optimization; replacing a native
four-valued probe by multiple binary tests does not preserve this
one-probe resource. A clausal refutation in the
[DRAT proof format](https://www.cs.utexas.edu/~marijn/drat-trim/)
concerns its specified formula; correspondence with (D3.9) is an
additional mathematical obligation. None of these problem-specific
optima is substituted for (D3.4) or (D3.10).

## 2. A full-family three-name obstruction

**Definition 2.1 (side ranges on the child universe).** Put

$$
\gamma(A)=(2,1),\qquad\gamma(B)=(1,0),\qquad\gamma(C)=(0,0).
$$

The side table supplied by FMR Theorem 5.1 is

$$
\begin{array}{c|cc}
u&\Gamma_L(u)&\Gamma_R(u)\\\hline
A&(3,0)&(4,1)\\
B&(2,0)&(3,1)\\
g_{xy}&\gamma(x)&\gamma(y).
\end{array}
\tag{D3.12}
$$

Each column has five distinct values. For $U\subseteq S$, write

$$
\ell(U)=|U\cap\{A,B\}|,\qquad
J_L(U)=\{x:\exists y,\ g_{xy}\in U\},\qquad
J_R(U)=\{y:\exists x,\ g_{xy}\in U\},
\qquad d_s(U)=|\Gamma_s[U]|.
$$

The same table gives the identities and counting bound

$$
d_s(U)=\ell(U)+|J_s(U)|,\qquad
|U\cap\mathcal G|\le |J_L(U)|\,|J_R(U)|.
\tag{D3.13}
$$

These are set projections, without any admissibility assertion about
them. The count in (D3.13) is the unweighted form of the child-range
calculation in
[NCE, Lemma 3.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md).

**Lemma 2.2 (the uniquely forced double-leaf projection).** Suppose
$H_1,H_2,H_3\subseteq S_3$ cover $S_3$, and

$$
|\Gamma_q[H_i]|\le4\qquad(i=1,2,3,\ q\in W_3).
\tag{D3.14}
$$

Define projections of their branch parts by

$$
X_i=\{x:\exists y,\ \langle x,y\rangle\in H_i\},\qquad
Y_i=\{y:\exists x,\ \langle x,y\rangle\in H_i\}.
$$

There is exactly one index $j$ for which $A,B\in Y_j$. For each
$i\ne j$, $Y_i$ contains exactly one of $A,B$, contains at least five
members of $\mathcal G$, and

$$
\max\{d_L(Y_i),d_R(Y_i)\}=4.
\tag{D3.15}
$$

Proof. Since $\Gamma_{LL}(\langle x,y\rangle)=\Gamma_L(x)$,
(D3.14) gives $d_L(X_i)\le4$, whereas $d_L(S)=5$. Hence $X_i\ne S$.
Similarly the targets $RL,RR$ give
$d_L(Y_i),d_R(Y_i)\le4$.

Fix $y\in S$. If it belonged to only one $Y_i$, all eleven actual
trees $\langle x,y\rangle$, $x\in S$, would have to lie in $H_i$.
This would force $X_i=S$. It cannot belong to no $Y_i$ either.
Thus every $y$ lies in at least two right projections, equivalently

$$
Y_i\cup Y_k=S\qquad(i\ne k).
\tag{D3.16}
$$

In particular each of $A,B$ occurs in at least two projections, so
some projection contains both. When $A,B\in Y_j$, (D3.13) gives
$|J_L(Y_j)|,|J_R(Y_j)|\le2$, and thus

$$
|Y_j\cap\mathcal G|\le4.
\tag{D3.17}
$$

Two such projections could together cover at most eight of the nine
members of $\mathcal G$, contradicting (D3.16). The index $j$ is
therefore unique. To give each leaf its second occurrence, the other
two projections must each contain one leaf, with different labels.
Their unions with $Y_j$ cover $S$, so each contains at least $9-4=5$
branches. If both its side ranges were at most three, (D3.13), with
$\ell=1$, would allow at most $2\cdot2=4$ branches. At least one
side range is therefore four, proving (D3.15). This uses the complete
actual branch grid $S\times S$ only for coverage; no $H_i$ is replaced
by a Cartesian product. $\square$

**Theorem 2.3 (exact original depth-three alphabet).** Under Assumption
1.2,

$$
\boxed{M_1(3)=4.}
\tag{D3.18}
$$

The lower bound excludes every original three-name encoder, with
arbitrary correlations and arbitrary native one-Read experiments. The
attaining four-code upper is the credited LTR Theorems 3.3–3.4
construction.

Proof. Restrict any correct encoder with at most three attained names
to the actual sources $\langle A,u\rangle$, $u\in S_3$. Let their
nonempty fibers be $H_i$; if necessary repeat a member to obtain three
covering sets. Fixing a name and a late target fixes the reader's stop
decision or entire literal before any reply or supplied $k$. A single
native reply has at most four values. Equal replies give identical final
predictors, and correctness for all $k$, with (D3.6), forces equal
factors. Consequently (D3.14) holds, including zero-Read branches.

Apply Lemma 2.2. The factors of the two parent root leaves are

$$
\begin{array}{c|cc}
u&\Gamma_{RL}(u)&\Gamma_{RR}(u)\\\hline
A&(5,0)&(6,1)\\
B&(4,0)&(5,1).
\end{array}
\tag{D3.19}
$$

Each entry lies outside the corresponding child range
$\Gamma_L[S]$ or $\Gamma_R[S]$ in (D3.12). Thus if either parent
leaf belongs to $H_i$, its addition to the branch part requires

$$
d_L(Y_i)\le3,\qquad d_R(Y_i)\le3.
\tag{D3.20}
$$

By (D3.15) this is impossible for $i\ne j$. Both parent leaves must
therefore belong to $H_j$. Also $A,B\in Y_j$, so for some $x,x'\in S$
the same fiber contains

$$
A,\quad B,\quad\langle x,A\rangle,\quad\langle x',B\rangle.
\tag{D3.21}
$$

For relative target $q=R$, that is actual request $p=RR$, their factors
are respectively

$$
(4,1),\quad(3,1),\quad(2,1),\quad(1,0),
\tag{D3.22}
$$

all distinct. The actual original-root query $R$ has replies alpha,
beta, branch, branch, merging the last two. Every other actual literal
merges the first two: the outer root and left cone have equal replies,
and every strict extension of $R$ is absent on both
$\langle A,A\rangle$ and $\langle A,B\rangle$. This exhausts all
finite words, whatever $x,x'$ are. Zero Reads also merge these two
sources. No query can serve $RR$ on $H_j$, a contradiction.
This proves $M_1(3)\ge4$. Only the four legal requests
$RR,RLL,RRL,RRR$ were needed to test the mandatory all-target
correctness; every experiment remained available.

For completeness, expand the existing LTR four-code upper on the entire
original family, not just $S_3$. Write $\tau(u)=0$ for a leaf and $1$
for a branch. Preparation submits the fixed three actual literals
$R,RL,RR$ and exports only

$$
E(\langle A,v\rangle)=
\begin{cases}
00,&v=A,\\
11,&v=B,\\
\tau(x)\tau(y),&v=\langle x,y\rangle.
\end{cases}
\tag{D3.23}
$$

These source distinctions come from the three replies, including absent
replies under a root leaf. Sufficient preparation charges are
$T=3,Q=2,A=5$. On the canonical family the full fibers are

$$
\begin{array}{c|c|r}
\text{name}&\text{right-subtree fiber}&\text{size}\\\hline
00&\{A\}\cup\langle\{A,B\},\{A,B\}\rangle&5\\
01&\langle\{A,B\},\mathcal G\rangle&18\\
10&\langle\mathcal G,\{A,B\}\rangle&18\\
11&\{B\}\cup\langle\mathcal G,\mathcal G\rangle&82.
\end{array}
\tag{D3.24}
$$

They partition all $123$ canonical states and attain all four names.
Equation (D3.23) also applies directly to every original tree of height
at most three, with arbitrary terminal labels and variable shapes.

For $p=Rq$, write the received name as $c_Lc_R$. Before any reply or
$k$, submit the single actual literal $Ra$, where

$$
a=
\begin{cases}
\varepsilon,&q=\varepsilon,\\
s,&q=s,\ s\in\{L,R\},\\
s,&q=su,\ c_s=0,\\
su,&q=su,\ c_s=1.
\end{cases}
\tag{D3.25}
$$

Define the endpoint decoder by

$$
\widehat\gamma(\alpha)=(2,1),\quad
\widehat\gamma(\beta)=(1,0),\quad
\widehat\gamma(\mathsf{branch})=(0,0).
\tag{D3.26}
$$

At the root target use this decoder. At a nonempty target, an absent
reply identifies the parent leaf: $A$ for name $00$, $B$ for name $11$;
output its $\Gamma_q$ from (D3.5). Indeed, on every branch source the
selected query is present: it is a child root, or a grandchild whose
parent the selected code bit certifies as branch. Mixed names cannot
give this absent case. If $q=su$, $c_s=0$, and the reply is present,
it is the actual leaf label $\ell$ of that child; output
$\Gamma_u(\ell)$. In all other present cases the query reaches the
target endpoint, so use (D3.26). These rules cover all seven targets
on every $v$ with $h(v)\le3$. The resulting factor, followed by
(D3.6), gives every authentic subsequent $k$ with no further Reads;
its first coordinate is at most six. The late address length is at most
three. Only the fixed-width name survives export; all other acquired
distinctions are isolated by Assumption 1.2. The upper and its two-bit
naming consequence are reused LTR results. Combining it with the new
lower proves (D3.18). $\square$

## 3. An explicit depth-three fractional seed

**Definition 3.1 (indexed native sets).** Enumerate the nine trees of
$\mathcal G$ by $g_i$, equivalently by $(x,y)\in T^2$ in the order
$A,B,C$ in each coordinate, and set

$$
H_A=\{A\}\cup\mathcal G,\qquad
H_B=\{B\}\cup\mathcal G,\qquad
T_i=\{A,B,g_i\},
$$

$$
P(X,Y)=\langle X,Y\rangle,\qquad
P_\ell(X,Y)=\{\ell\}\cup P(X,Y)\quad(\ell=A,B).
\tag{D3.27}
$$

The child sets $H_A,H_B,T_i$ are the credited maximal depth-two
admissible sets of FMR Theorem 5.1; their depth-two optimal fractional
value is $25/17$. The parent sets and weights below use those sets as
ingredients, without treating a parent projection as an admissible
fiber or imposing independent child codes on competitors.

**Theorem 3.2 (a rational admissible cover of weight $760/289$).** The
following $192$ specified sets in $S_3$, each with the displayed weight,
are an admissible fractional cover. The indices $i,j$ range independently
over all nine possibilities. Each query column is relative to $v$;
the actual original-root literal is its prefix by $R$.

| Family | Set | Multiplicity | Weight of each set | Target $LL$ | Target $LR$ | Target $RL$ | Target $RR$ |
| --- | --- | ---: | ---: | --- | --- | --- | --- |
| $1$ | $P(H_B,H_A)$ | $1$ | $521/2312$ | $LL$ | $LR$ | $RL$ | $RR$ |
| $2$ | $P(H_B,H_B)$ | $1$ | $521/2312$ | $LL$ | $LR$ | $RL$ | $RR$ |
| $3$ | $P(H_B,T_j)$ | $9$ | $23/1156$ | $LL$ | $LR$ | $R$ | $R$ |
| $4$ | $P_A(T_i,T_j)$ | $81$ | $73/11016$ | $L$ | $L$ | $R$ | $R$ |
| $5$ | $P_A(T_i,\mathcal G)$ | $9$ | $7/136$ | $L$ | $L$ | $RL$ | $RR$ |
| $6$ | $P_B(H_A,T_j)$ | $9$ | $1/17$ | $LL$ | $LR$ | $R$ | $R$ |
| $7$ | $P_B(H_A,\mathcal G)$ | $1$ | $7/17$ | $LL$ | $LR$ | $RL$ | $RR$ |
| $8$ | $P_B(T_i,T_j)$ | $81$ | $1/1377$ | $L$ | $L$ | $R$ | $R$ |

For each family, target $\varepsilon$ uses query $\varepsilon$, and
targets $L,R$ use queries $L,R$, respectively. In particular

$$
z_3\le\frac{760}{289}.
\tag{D3.28}
$$

Every set has a native one-query decoder for every target, and its
inverse image under $\pi_3$ has that same decoder on the full original
family. Acquiring membership information for all these lifted sets takes
at most seven actual Reads, maximum literal length three and seventeen
submitted letters.

Proof. First specify the entire reply-to-factor decoder. At target
$\varepsilon$, use (D3.26). At target $s\in\{L,R\}$, a present
reply gives (D3.26); an absent reply occurs only on the parent leaf
included in the indicated family, whose factor is $\Gamma_s(\ell)$.
Families 1–3 contain no parent leaf, so this case is unattained there.

For a target $su$ of length two whose table query is $s$, the child
set is $T_i$ or $T_j$. An absent reply is possible only on the known
parent leaf $\ell$ and gives $\Gamma_{su}(\ell)$. Otherwise alpha
or beta identifies child $A$ or $B$, and branch identifies the unique
child $g_i$ or $g_j$. Output respectively
$\Gamma_u(A),\Gamma_u(B)$, or $\gamma(x)$ for $u=L$ and
$\gamma(y)$ for $u=R$ when the identified branch is $g_{xy}$.
All these values are explicit in (D3.12).

For the remaining table entries the query is the target $su$ itself.
A present reply gives (D3.26). All attained absent replies are assigned
the following factors; a dash denotes a column using the preceding
child-root rule instead.

$$
\begin{array}{c|cccc}
\text{family}&LL&LR&RL&RR\\\hline
1&(2,0)&(3,1)&(3,0)&(4,1)\\
2&(2,0)&(3,1)&(2,0)&(3,1)\\
3&(2,0)&(3,1)&-&-\\
4&-&-&-&-\\
5&-&-&(5,0)&(6,1)\\
6&(3,0)&(4,1)&-&-\\
7&(3,0)&(4,1)&(4,0)&(5,1)\\
8&-&-&-&-.
\end{array}
\tag{D3.29}
$$

Values on unattained replies may be any fixed factor. For families
1–3, a direct grandchild query is absent exactly when its child is
the known leaf of $H_A$ or $H_B$, giving (D3.12). For families 4 and
8, the child-root rule separates the parent leaf from the three
possible child constructors. For family 5, right grandchildren are
present on every branch member, since its right child lies in
$\mathcal G$; their absent reply therefore identifies parent $A$.
Its left targets use the child-root rule.

The essential additional absorption in families 6 and 7 occurs on the
left: a direct left-grandchild query may be absent on parent $B$ or
on a branch whose left child is $A$. These two sources have equal
required factors, because

$$
\Gamma_{LL}(B)=(3,0)=\Gamma_L(A),\qquad
\Gamma_{LR}(B)=(4,1)=\Gamma_R(A).
\tag{D3.30}
$$

This verifies the left columns of (D3.29). On the right, family 6 uses
the identifying $T_j$ child-root reply; family 7 has right child in
$\mathcal G$, so absence identifies parent $B$. These exhaust every
row, index, target and attained reply, proving admissibility. The
collision (D3.30) is equality of complete temporal factors, not of
blocking-leaf descriptions.

To verify coverage, put

$$
a(x)=\mathbf1_{x\in H_A},\quad b(x)=\mathbf1_{x\in H_B},\quad
g(x)=\mathbf1_{x\in\mathcal G},\quad
n(x)=|\{i:x\in T_i\}|=
\begin{cases}9,&x=A,B,\\1,&x\in\mathcal G.\end{cases}
$$

The total coverage of a branch $\langle x,y\rangle$ is

$$
\begin{aligned}
\mathcal C(x,y)={}&
\frac{521}{2312}b(x)(a(y)+b(y))
+\frac{23}{1156}b(x)n(y)
+\frac1{136}n(x)n(y)\\
&+\frac7{136}n(x)g(y)
+\frac1{17}a(x)n(y)
+\frac7{17}a(x)g(y).
\end{aligned}
\tag{D3.31}
$$

Here the combined coefficient $1/136$ is
$73/11016+1/1377$. Substitution gives, with rows and columns
ordered $A,B,\mathcal G$,

$$
\begin{array}{c|ccc}
\mathcal C&A&B&\mathcal G\\\hline
A&9/8&9/8&1\\
B&1&1&1\\
\mathcal G&1&1&1.
\end{array}
\tag{D3.32}
$$

An entry involving $\mathcal G$ holds for every individual branch
there, since each such branch occurs in exactly one $T_i$. The two
parent root leaves receive respectively

$$
81\frac{73}{11016}+9\frac7{136}=1,\qquad
9\frac1{17}+\frac7{17}+81\frac1{1377}=1.
\tag{D3.33}
$$

Thus $121$ canonical states have coverage one and the two states
$\langle A,A\rangle,\langle A,B\rangle$ have coverage $9/8$.
The total weights of families 4–5 and of families 6–8 are each one.
The remaining total is

$$
2\frac{521}{2312}+9\frac{23}{1156}=\frac{182}{289}.
$$

Hence the full total is $2+182/289=760/289$.

For the original lift, actually submit the seven words $Rq$,
$q\in W_3$, including absent words. Their length sum is
$1+2\cdot2+4\cdot3=17$, and they determine $\pi_3(v)$. FMR
Lemma 2.2 preserves all the selected boundary replies and target
factors. Consequently each displayed decoder works on every
$v\in\pi_3^{-1}(H)$ with $h(v)\le3$, after prefixing its query
by $R$. This gives every authentic count by (D3.6). Fractional
coefficients describe a common public cover, not a fractional
source-dependent export. Whenever an integral cover is selected,
FMR Theorem 2.5 implements its first-containing-member index from
these paid observations and isolates every other acquired distinction.
No preassigned source color is supplied. $\square$

## 4. Paid recursive consequences and their scope

**Theorem 4.1 (the fractional seed gives a strict native rate upper).**
Set

$$
u_3=\frac{760}{289},\qquad u_{D+1}=u_D^2+1\quad(D\ge3),
\qquad H_N=\sum_{j=1}^N\frac1j.
\tag{D3.34}
$$

For every $D\ge3$ there is a paid effective preparation on the entire
original $\mathcal F_D$, with one common all-target, all-count reader,
such that

$$
M_1(D)\le H_{N_D}u_D,\qquad
T_{\rm prep}\le2^D-1,\quad Q_{\rm prep}\le D,\quad
A_{\rm prep}\le(D-1)2^D+1.
\tag{D3.35}
$$

The late reader makes at most one actual Read of length at most $D$.
For the original normalized rate, whose existence is supplied by FMR,

$$
\lambda=\lim_{D\to\infty}2^{-D}\log_2M_1(D)
\le L_u:=\lim_{D\to\infty}2^{-D}\log_2u_D
<\frac3{16}.
\tag{D3.36}
$$

The gluing, rounding, acquisition and rate comparison are the credited
FMR Lemmas 3.1, 4.3–4.4 and Theorems 2.5, 4.5; the new input is the
explicit cover in Theorem 3.2.

Proof. Starting with that rational cover, apply FMR's native fractional
gluing: pair cover members with product weights for branch roots and
add the two-leaf set $\{A,B\}$ with weight one. A branch
$\langle x,y\rangle$ receives the product of its two covering sums,
which is at least one; the leaves receive one. The total follows
(D3.34). A branch root target needs no Read. A child target uses that
child's single witnessing literal with its actual original-root prefix;
the two-leaf set uses its root reply to identify its label.

Constituent calls are implemented only at actually present occurrences.
For an actual occurrence $a$ of $x$, a virtual wrapper
$\langle A,x\rangle$ has constant replies at $\varepsilon$ and
in its left cone; a virtual literal $Rw$ is implemented by the one
actual literal $aw$. Thus neither artificial wrappers nor recursive
notation introduce a subtree, copying or free-navigation port.
The original source is unchanged. This is exactly FMR Lemma 3.1's
literal interpretation and Lemma 4.3's constructive upper, imposing
no product restriction on competing encoders.

Apply FMR's harmonic greedy rounding to the resulting public finite
fractional cover. It gives an integral cover with at most $H_{N_D}u_D$
members. To implement it, acquire all $Rq$, $q\in W_D$, compute
$\pi_D(v)$ and its first-containing-member index, and export only
that fixed-width complete name. The scan has (D3.35)'s costs. The
installed experiment and reply-to-factor table for that index and the
later target supplies at most one boundary Read. Canonical equality
and (D3.6) prove correctness for every original source and authentic
count. All selection state, acquired tables, buffers, lengths and
other source distinctions are isolated as in Assumption 1.2.
Installation, rounding work and workspace remain separate costs.

The scalar sequence $2^{-D}\log_2u_D$ is increasing, whereas
$2^{-D}\log_2(u_D+1)$ decreases, since
$u_D^2+2\le(u_D+1)^2$. Their difference is at most $2^{-D}$,
so they have a common limit $L_u$ and

$$
L_u\le2^{-D}\log_2(u_D+1).
\tag{D3.37}
$$

The supplied estimate $N_D+1\le2^{2^D}$ gives
$H_{N_D}\le1+(\ln2)2^D$, whose normalized logarithm vanishes.
Equation (D3.35) therefore gives $\lambda\le L_u$.

For the strict numerical claim, the rational recurrence gives exactly

$$
u_4=\frac{661121}{83521},\qquad
u_5=\frac{444056734082}{6975757441},\qquad
u_6=\frac{197235044275447727251205}{48661191875666868481}.
\tag{D3.38}
$$

The positive-integer identity

$$
4096\cdot48661191875666868481
-197283705467323394119686
=2032536455408099178490>0
\tag{D3.39}
$$

proves $u_6+1<4096=2^{12}$. Hence (D3.37) gives
$L_u<12/64=3/16$, without a decimal logarithm premise.

The previous FMR Theorem 5.2 seed $x_2=25/17$ gives
$x_3=914/289$ and $x_{D+1}=x_D^2+1$. Its construction limit
$L_{\rm old}$ satisfies $L_{\rm old}\ge\log_2(x_3)/8$.
Since

$$
914^2=835396>668168=8\cdot289^2,
$$

this lower bound on that construction's own limit exceeds $3/16$.
Thus the new upper improves the credited seed construction itself;
the credited exact depth-two seed and known four-code finite upper
are not new claims. $\square$

**Corollary 4.2 (separation of finite memory, fractional covering and
joint regularization).** With $K_3(n),Z_3(n),\sigma_3$ denoting the
unchanged all-correlated joint-block quantities of FMR Definition 6.1
and [NCM, Definition 1.5](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md),
one has

$$
\frac{33}{13}\le z_3\le\frac{760}{289}<4=M_1(3),
\tag{D3.40}
$$

$$
\left(\frac{33}{13}\right)^n\le Z_3(n)
\le\left(\frac{760}{289}\right)^n,
\qquad
K_3(n)\le H_{123^n}\left(\frac{760}{289}\right)^n,
\tag{D3.41}
$$

$$
\log_2\frac{33}{13}\le\sigma_3
\le\log_2\frac{760}{289}<2,
\qquad
\frac18\log_2\frac{33}{13}\le\lambda<\frac3{16}.
\tag{D3.42}
$$

In particular $K_3(n)\ge4^n$ cannot hold for every $n$.

Proof. NCE Theorems 6.1–6.2 supply the lower bounds against every
jointly admissible correlated fiber and every original encoder,
including arbitrary off-target experiments. In particular $Z_3(1)=z_3$
has the stated lower. Theorem 3.2 and $760<4\cdot289$ give the
remaining finite inequalities.

Products of the explicitly constructed cover members are jointly
admissible: a target uses its requested coordinate's witnessing query.
Their product weights cover each tuple, with total $(760/289)^n$.
This constructs particular covers, without assuming product competitors.
The finite harmonic rounding argument of FMR Lemma 4.4 applies to
their $123^n$ vertices, proving (D3.41). The native preparation and
all-word block interpretation are FMR Lemma 6.2, using full literal
prefixes at actual occurrences. Since $H_{123^n}\le1+n\ln123$,
its logarithm divided by $n$ vanishes. The supplied joint limit then
gives the upper on $\sigma_3$, strictly below two, and consequently
$K_3(n)<4^n$ for all sufficiently large $n$. NCE's original lower
and Theorem 4.1 give the interval for $\lambda$.

The finite obstruction uses the full support $S\times S$ to force
projection coverage, not a tensor mass bound for a correlated code
fiber. In particular it does not supply the missing all-joint lower
$4^n$, which (D3.41) rules out. Locally inadmissible projections can
still assist each other, as in NCM Proposition 6.1; off-target fibers
and higher-arity obstructions remain those of LTR §7 and FMR §7.
Neither a same-fiber prefix restriction nor independent child codes
are consequences of (D3.18).

The displayed inequalities do not identify exact $z_3$, $\sigma_3$,
general $M_1(D)$ for $D\ge4$, or sharp $\lambda$. FMR's relation
$\lambda=\sup_d2^{-d}\sigma_d$ retains its inner all-joint infima;
the explicit depth-two error supplied by NCM Theorem 4.1 does not
give a uniform effective error for every depth. A sequence of certified
lower endpoints converging effectively to the original rate remains
unspecified by these estimates. The exact recovery furnished here is

$$
(E(t),D,p,\text{at most one actual literal reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0},
\tag{D3.43}
$$

under the paid services and authentic-count input. Its inverse on
trajectories is first branch count and alpha-stage presence from
Definition 1.3. It does not invert the complete source or unobserved
history, nor derive authentic counts or a physical spacetime from that
factor. The finite-level existence theorem
`compact_observation_factorization` in
[`CompactObservationFactorization`](../../../D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.lean)
assumes compactness, compatible continuous surjective finite discrete
observations forming a fiber basis, and continuous finite readouts;
its finite action-window clause also assumes finitely many continuous
actions. Those topological hypotheses alone supply neither the charged
native acquisition bounds nor a rate convergence modulus. $\square$

## 追加锚（本行以下为增补区）

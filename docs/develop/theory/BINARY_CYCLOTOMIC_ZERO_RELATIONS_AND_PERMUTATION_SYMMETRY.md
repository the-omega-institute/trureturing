# Binary cyclotomic zero relations and permutation symmetry

**Definition 1 (Actual zero subsets and their integer relation quotient).**
Let $I$ be finite, let $A$ be an additive abelian group, and let

$$
w:I\longrightarrow A,\qquad
F=\mathbb Z^I,\qquad
\Phi:F\longrightarrow A,\quad \Phi(e_i)=w_i.
$$

For $S\subseteq I$, put $r_S=\sum_{i\in S}e_i$. Define

$$
\mathcal H=\{S\subseteq I:\textstyle\sum_{i\in S}w_i=0\},\qquad
L=\langle r_S:S\in\mathcal H\rangle_{\mathbb Z},\qquad
U=F/L,\quad u_i=e_i+L.
$$

Thus every defining row is an actual $0/1$ subset indicator. Write

$$
G=\{p\in\operatorname{Sym}(I):
 S\in\mathcal H\Longleftrightarrow p(S)\in\mathcal H\text{ for all }S\subseteq I\}.
$$

Products of permutations mean composition: $pq=p\circ q$.

**Theorem 2 (Exact zero subsets and universal descent).**
For every $S\subseteq I$,

$$
S\in\mathcal H\quad\Longleftrightarrow\quad\sum_{i\in S}u_i=0.
\tag{1}
$$

For an arbitrary abelian group $C$, a function $x:I\to C$ extends uniquely
to a homomorphism $U\to C$ taking $u_i$ to $x_i$ if and only if
$\sum_{i\in S}x_i=0$ for every $S\in\mathcal H$. Moreover, for every full
label permutation $p\in\operatorname{Sym}(I)$, the following are equivalent:

$$
 p\in G;\qquad P_p(L)=L;\qquad
 \exists!\,\alpha\in\operatorname{Aut}(U)\quad
 \alpha(u_i)=u_{p(i)}\quad(i\in I),
\tag{2}
$$

where $P_p(e_i)=e_{p(i)}$. In particular, no equality $L=\ker\Phi$ is needed.

*Proof.* Each generating row of $L$ is in $\ker\Phi$, so

$$
L\subseteq\ker\Phi.
\tag{3}
$$

If $S\in\mathcal H$, its row is a generator of $L$, hence its sum in $U$
vanishes. Conversely, a vanishing sum in $U$ says $r_S\in L$; (3) then
gives $\Phi(r_S)=0$. This proves (1).

The unique homomorphism $F\to C$ extending $x$ is
$\sum n_i e_i\mapsto\sum n_i x_i$. It factors through $F/L$ precisely
when it annihilates all the rows generating $L$, which is the stated
condition. Uniqueness follows because the $u_i$ generate $U$.

If $p\in G$, then $P_p(r_S)=r_{p(S)}$ permutes the entire generating
family of $L$. Thus $P_p(L)=L$, and $P_p,P_{p^{-1}}$ induce mutually
inverse homomorphisms of $U$. Conversely, any indicated automorphism
$\alpha$ gives

$$
\sum_{i\in S}u_i=0
\Longleftrightarrow
\alpha\left(\sum_{i\in S}u_i\right)=0
\Longleftrightarrow
\sum_{i\in p(S)}u_i=0.
$$

Equation (1) implies $p\in G$. Again, generation gives uniqueness. $\square$

**Theorem 3 (Canonical fibers and a chosen splitting).**
Put

$$
W=\{u_i:i\in I\},\quad I_v=\{i:u_i=v\},\quad m_v=|I_v|,
$$

$$
K=\{\alpha\in\operatorname{Aut}(U):
\alpha(W)=W,\ m_{\alpha(v)}=m_v\ (v\in W)\}.
$$

The unique automorphism in (2), denoted by $\alpha_p$, gives a canonical
exact sequence of finite groups

$$
1\longrightarrow\prod_{v\in W}\operatorname{Sym}(I_v)
\longrightarrow G\xrightarrow{\rho}K\longrightarrow1,
\qquad\rho(p)=\alpha_p,
\tag{4}
$$

and

$$
|G|=|K|\prod_{v\in W}m_v!.
\tag{5}
$$

For each $K$-orbit $O\subseteq W$, choose one set $E_O$ of the common
fiber size, and choose bijections $b_v:E_O\to I_v$, $v\in O$. These
choices split (4). They identify its kernel with
$\prod_{v\in W}\operatorname{Sym}(E_{O(v)})$, or with
$\prod_{v\in W}\operatorname{Sym}(m_v)$ after choosing numbered sets.
These coordinates and the splitting need not be canonical.

*Proof.* On generators, $\alpha_{pq}=\alpha_p\alpha_q$. Also $p$ maps
$I_v$ bijectively onto $I_{\alpha_p(v)}$, so $\rho$ maps into $K$.
Its kernel consists exactly of the independent permutations of the actual
sets $I_v$. Conversely, such permutations induce the identity on $U$,
so Theorem 2 puts them in $G$. This proves exactness at the first two
terms. An element of $K$ lifts by choosing a bijection
$I_v\to I_{\alpha(v)}$ for every $v$ and taking their disjoint union;
Theorem 2 shows that union belongs to $G$. Hence $\rho$ is onto.
Restriction $K\to\operatorname{Sym}(W)$ is injective, because $W$
generates $U$. Thus $K$ is finite, and counting fibers of $\rho$
proves (5).

For $i\in I_v$, define

$$
s(\alpha)(i)=b_{\alpha(v)}b_v^{-1}(i).
$$

The sets used by these two bijections have the same domain $E_{O(v)}$.
Cancellation of the intermediate bijections gives
$s(\alpha)s(\beta)(i)=b_{\alpha\beta(v)}b_v^{-1}(i)$, and
$\rho s(\alpha)=\alpha$. This is a splitting. More explicitly, every
element has unique destination-fiber coordinates

$$
p_{\sigma,\alpha}(i)
=b_{\alpha(v)}\sigma_{\alpha(v)}b_v^{-1}(i),\qquad i\in I_v,
$$

and direct composition yields

$$
(\sigma,\alpha)(\tau,\beta)=(\eta,\alpha\beta),\qquad
\eta_w=\sigma_w\circ\tau_{\alpha^{-1}(w)}.
\tag{6}
$$

If $b'_v$ is another enumeration with the same domains, the permutation
$h|_{I_v}=b'_vb_v^{-1}$ lies in the kernel and satisfies
$s'(\alpha)=hs(\alpha)h^{-1}$. This specifies the dependence on choices.
$\square$

**Proposition 4 (Comparison with the given arithmetic group).**
There is a unique comparison homomorphism

$$
\bar\Phi:U\longrightarrow A,\qquad\bar\Phi(u_i)=w_i,
$$

with kernel $\ker\Phi/L$ and image $\operatorname{im}\Phi$. It is an
isomorphism onto $A$ exactly when $L=\ker\Phi$ and the weights generate
$A$. If relation completeness holds without generation of $A$, it
identifies $U$ with $\operatorname{im}\Phi$.

*Proof.* Equation (3) defines the map. A class $f+L$ is in its kernel
exactly when $f\in\ker\Phi$, and its image is exactly the set of all
integer combinations of the weights. These descriptions prove all claims.
If $I=\varnothing$, then $F,U,G,K$ are trivial. A singleton is an edge
exactly when its weight is zero, so $u_i=0$ exactly when $w_i=0$.
The zero fiber is fixed by $K$; singleton fibers contribute trivial
permutation factors. If every weight is zero, the singleton relations give
$U=0$ and $G=\operatorname{Sym}(I)$. These cases require no extra
hypotheses. Equality of original weights, however, need not imply equality
of quotient classes: for weights $1,1\in\mathbb Z$, only the empty subset
is zero, so $L=0$ and the two coordinate classes in $U=\mathbb Z^2$ are
different. $\square$

*Mathematical citation 4.1.* Free abelian universal properties and quotient
factorization are standard algebra; see Mathlib's [Free abelian groups][1]
and [Quotient groups and isomorphism theorems][2]. The application of these
constructions to the full actual zero-subset relation family in Theorems
2–3 is repo-derived. The constructions themselves are not attributed as new.

**Definition 5 (Binary cyclotomic weights).**
For integers $q,m\ge1$, let

$$
\ell=3q,\qquad M=2^{2q}+2^q+1,\qquad
I=\operatorname{Fin}(m)\times\mathbb Z/\ell,\qquad
w(a,j)=\overline{2^j}\in\mathbb Z/M.
\tag{7}
$$

We use canonical representatives $0\le j<\ell$ for integer exponents.
Since

$$
2^{3q}-1=(2^q-1)M,
\tag{8}
$$

and $M$ is odd, $2$ is a unit modulo $M$, and the modular weight is
well-defined on cyclic colors. The notation $F,L,U,\mathcal H,G$ is that
of Definition 1 for these weights.

**Theorem 6 (Actual masks reconstruct every abelian-group solution).**
Assume $q,m\ge2$. Put $a_j=(0,j)$, $b_j=(1,j)$, and select

$$
\begin{aligned}
T_{a,j}&=\{(a,j),a_{j+q},a_{j+2q}\}
 &&(1\le a<m,\ j\in\mathbb Z/\ell),\\
R_t&=\{a_t,a_{t+q},a_{t+2q}\}
 &&(0\le t<q),\\
D_n&=\{a_n,b_n,a_{n+q+1},a_{n+2q+1}\}
 &&(0\le n<2q).
\end{aligned}
\tag{9}
$$

All indices in sets are cyclic. These are $\ell m$ distinct actual zero
subsets. For any abelian group $C$ and function $X:I\to C$, their
finite-set sums all vanish if and only if there is a unique $c\in C$
such that

$$
Mc=0,\qquad X(a,j)=2^j c\quad(a\in\operatorname{Fin}(m),\ 0\le j<\ell).
\tag{10}
$$

Every such $X$ annihilates all of $\mathcal H$, not just the selected
family.

*Proof.* In a $T$-mask the nonzero-copy vertex is distinct from the two
copy-zero vertices; their colors differ by $q$. In an $R$-mask the
three colors differ by $q$ and are distinct. The copy-zero offsets of a
$D$-mask are $0,q+1,2q+1$, with
$0<q+1<2q+1<3q$. Its fourth vertex has copy index $1$, so its four
vertices are distinct. Thus these sums really are sums over sets, without
repeated occurrences of a label. Reduction using (8) shows that the triple
weight sums are $2^jM$ and the $D_n$ weight sums are $2^{n+1}M$ modulo
$M$; they all vanish.

Each $T_{a,j}$ has the unique nonzero-copy vertex $(a,j)$, which
distinguishes all its indices. The $R_t$ use only copy zero and are
pairwise disjoint. Each $D_n$ has the unique nonzero-copy vertex $b_n$,
which distinguishes its index, and has size four rather than three.
Consequently the masks are all distinct and their number is

$$
\ell(m-1)+q+2q=\ell m.
\tag{11}
$$

Now set $x_j=X(0,j)$. The $q$ equations from $R_t$ imply

$$
x_j+x_{j+q}+x_{j+2q}=0\qquad(j\in\mathbb Z/\ell),
\tag{12}
$$

because writing $j=t+sq$, $0\le t<q$, just cyclically permutes the
three terms of $R_t$. Subtract (12) from the $T_{a,j}$ equation to get
$X(a,j)=x_j$ for every copy. The $D_n$ equation therefore becomes

$$
2x_n+x_{n+q+1}+x_{n+2q+1}=0.
$$

Subtracting (12) at $j=n+1$ gives

$$
x_{n+1}=2x_n\qquad(0\le n<2q).
\tag{13}
$$

This subtracts equal group elements and cancels no integer scalar. With
$c=x_0$, induction gives $x_j=2^jc$ for $0\le j\le2q$. Substituting
in $R_0$ yields $Mc=0$. For $1\le t<q$, the remaining colors follow
from $R_t$:

$$
x_{2q+t}=-x_t-x_{q+t}=-(2^t+2^{q+t})c=2^{2q+t}c,
$$

where the final equality is $2^tMc=0$. This proves (10), and $c=X(0,0)$
proves uniqueness. Conversely, if $Mc=0$, (8) makes $2^jc$ independent
of the cyclic representative. For any $S\in\mathcal H$, its sum of
canonical integer weights is an integer multiple $hM$, so
$\sum_{(a,j)\in S}2^jc=hMc=0$. This proves the converse and the final
assertion for arbitrary torsion in $C$. $\square$

**Proposition 7 (Inverse quotient maps, then an integral basis).**
In Theorem 6, the selected rows span exactly $L=\ker\Phi$, and their
$\ell m$ distinct indicator rows form a free integer basis of that
subgroup. Under the natural comparison,

$$
U\cong\mathbb Z/M,\qquad u_{a,j}\longmapsto\overline{2^j}.
\tag{14}
$$

*Proof.* Let $L_*$ be the span of the selected rows and $Q=F/L_*$.
Since all selected masks are actual edges,

$$
L_*\subseteq L\subseteq\ker\Phi.
\tag{15}
$$

Apply Theorem 6 to $C=Q$, $X(a,j)=e_{a,j}+L_*$. For $c=e_{0,0}+L_*$
it gives $Mc=0$ and $e_{a,j}+L_*=2^jc$. Hence define

$$
\beta:\mathbb Z/M\to Q,\quad\bar n\mapsto nc,
\qquad
\gamma:Q\to\mathbb Z/M,\quad f+L_*\mapsto\Phi(f).
$$

Both are well-defined. On $1$, $\gamma\beta$ is the identity, and on
each generator $e_{a,j}+L_*$, $\beta\gamma$ is the identity. They are
therefore inverse homomorphisms. In particular, if $f\in\ker\Phi$, the
injectivity of $\gamma$ implies $f\in L_*$. Equation (15) proves the
claimed span equality and (14), before any rank argument.

Write $n=\ell m$ and regard the selected rows as vectors in
$\mathbb Q^n$. Since the quotient is annihilated by $M$, each vector
$Me_i$ belongs to $L_*$; since $M\ne0$, the rational span of the
selected rows contains every $e_i$. There are exactly $n$ selected
rows by (11), and $\mathbb Q^n$ has dimension $n$, so these rows are
linearly independent over $\mathbb Q$. Any integer dependence would be
a rational dependence, hence is zero. They already span $L_*$ over
$\mathbb Z$, so the row-to-generator map $\mathbb Z^n\to L_*$ is
bijective. This proves freeness and the stated integer basis. $\square$

**Theorem 8 (Exact binary order and the full cyclic action).**
For every $q\ge1$, including composite $M$,

$$
\operatorname{ord}_M(2)=3q=\ell.
\tag{16}
$$

Whenever the natural comparison $U\to\mathbb Z/M$ in Definition 5 is an
isomorphism, the full label symmetry group is the regular wreath product

$$
G\cong\operatorname{Sym}(m)^\ell\rtimes C_\ell
=\operatorname{Sym}(m)\wr C_\ell,\qquad
|G|=\ell(m!)^\ell.
\tag{17}
$$

Its unique destination-fiber coordinates and multiplication are

$$
p_{\sigma,k}(a,j)=(\sigma_{j+k}(a),j+k),\qquad
(\sigma,k)(\tau,h)=(\eta,k+h),\quad
\eta_r=\sigma_r\circ\tau_{r-k}.
\tag{18}
$$

In particular, (17)–(18) hold for $q,m\ge2$.

*Proof.* The order $d$ of the unit $2$ divides $3q$ by (8). If
$d<3q$, write $3q=ed$ with $e\ge2$. Then
$d\le3q/2<2q$, so $0<2^d-1<M$, contradicting
$M\mid2^d-1$. This proves (16).

Under the assumed comparison, $W=\{2^j:0\le j<\ell\}$ has $\ell$
distinct elements and each fiber has $m$ labels. An additive
automorphism of $\mathbb Z/M$ is multiplication by its value at $1$:
it has this form because $1$ generates, and the value is a unit because
the inverse homomorphism supplies an inverse multiplier. To preserve $W$
it must take $1$ to $2^k$. Conversely, multiplication by $2^k$
permutes $W$. Thus $K=C_\ell$, acting regularly on the colors.
Theorem 3 now gives (17) and the common shift in (18).

For completeness, any permutation in (18) sends the sum of the weights of
every subset to $2^k$ times that sum. This unit multiplication preserves
zero in both directions, so it preserves the entire hypergraph. Finally,

$$
p_{\sigma,k}p_{\tau,h}(a,j)
=(\sigma_{j+h+k}(\tau_{j+h}(a)),j+h+k).
$$

At destination $r=j+h+k$, this gives exactly the product in (18), with
$\eta_r=\sigma_r\circ\tau_{r-k}$. Uniqueness of $k$ follows from
(16), and the restrictions to the fibers uniquely determine $\sigma$.
$\square$

*Mathematical citation 8.1.* The regular wreath product and its action on a
product set are standard; [3] gives the convention whose base coordinate at
$r$ is multiplied against the second base coordinate at $r-k$.
Theorems 6–8 identify this established group with the particular full
zero-subset symmetry group by the actual-mask reconstruction; that
identification is repo-derived.

**Theorem 9 (One copy: independent triples).**
For $m=1$ and every $q\ge1$, the actual zero subsets are exactly the
unions of the disjoint triples

$$
R_t=\{t,t+q,t+2q\},\qquad0\le t<q.
\tag{19}
$$

Consequently

$$
U\cong\mathbb Z^{2q},\qquad
G\cong\operatorname{Sym}(3)^q\rtimes\operatorname{Sym}(q),\qquad
|G|=6^q q!.
\tag{20}
$$

The top group acts on its $q$ blocks, so this is the imprimitive wreath
product $\operatorname{Sym}(3)\wr\operatorname{Sym}(q)$.

*Proof.* Put $B=2^q$. For a subset $S\subseteq\{0,\ldots,3q-1\}$, its
unsigned binary integer $N=\sum_{j\in S}2^j$ lies between $0$ and
$B^3-1=(B-1)M$. Thus it is zero modulo $M$ exactly when $N=kM$ for
some $0\le k\le B-1$. Write the unique $q$-bit expansion
$k=\sum_{t=0}^{q-1}\epsilon_t2^t$. Then

$$
kM=\sum_{t=0}^{q-1}\epsilon_t
(2^t+2^{t+q}+2^{t+2q}).
$$

All displayed bit positions are different, so there are no carries.
Uniqueness of binary expansion forces $S$ to be exactly the union in
(19) indexed by the nonzero $\epsilon_t$. Conversely each triple has
weight $2^tM$, so every such union is zero. This proves both directions
of the zero-set description.

Their rows give $L=\bigoplus_t\mathbb Zr_{R_t}$. On each triple the
map $\mathbb Z^3\to\mathbb Z^2$,
$(h_0,h_1,h_2)\mapsto(h_0-h_2,h_1-h_2)$, is onto and has kernel
$\mathbb Z(1,1,1)$. It gives the claimed quotient, with coordinate
classes $a_t,b_t,-a_t-b_t$ in its $t$-th direct summand. These $3q$
vectors are all distinct: their coordinate pairs are $(1,0),(0,1),(-1,-1)$,
and vectors from different direct summands cannot coincide. The minimal
nonempty edges are exactly the
$R_t$, so any hypergraph automorphism permutes those triples and
permutes their three elements. Conversely all such permutations preserve
every union of triples. This proves (20), including its order. By Theorem
3 the fiber kernel is trivial, so this is also the entire support
automorphism group of $U$. The internal $\operatorname{Sym}(3)$
factors permute three distinct quotient vectors; they do not come from
equal original arithmetic weights, which are distinct by (16). $\square$

**Theorem 10 (Two copies of three colors).**
For $q=1,m=2$, the zero subsets are exactly the empty subset, the eight
three-element transversals of the three color fibers, and the full subset.
Moreover

$$
U\cong\mathbb Z^2,\qquad
G\cong\operatorname{Sym}(2)^3\rtimes\operatorname{Sym}(3),\qquad |G|=48.
\tag{21}
$$

*Proof.* A subset with color counts $c_j\in\{0,1,2\}$ has integer weight
$N=c_0+2c_1+4c_2$, between $0$ and $14$. Divisibility by $7$
requires $N=0,7,14$. The endpoints force count vectors $(0,0,0)$ and
$(2,2,2)$. For $N=7$, $c_2=0$ is impossible because
$c_0+2c_1\le6$; $c_2=2$ is impossible because $N\ge8$. Therefore
$c_2=1$, and $c_0+2c_1=3$ has the sole permitted solution
$c_0=c_1=1$. Such a subset chooses either copy of each color,
giving $2^3=8$ transversals, all of weight $7$.

Put

$$
r=e_{0,0}+e_{0,1}+e_{0,2},\qquad
d_j=e_{1,j}-e_{0,j}\quad(0\le j<3).
$$

The baseline transversal and one-copy replacements have rows $r$ and
$r+d_j$, so $r,d_j\in L$. Conversely, every transversal row is
$r+\sum_{j\in J}d_j$, and the full row is exactly

$$
r_I=2r+d_0+d_1+d_2.
\tag{22}
$$

The zero-set description therefore proves $L=\langle r,d_0,d_1,d_2\rangle$.
The map $F\to\mathbb Z^3$ summing coordinates of the same color is
onto and has kernel $\langle d_0,d_1,d_2\rangle$: in each two-coordinate
fiber, a vector with sum zero is an integer multiple of the difference.
The remaining row maps to $(1,1,1)$. The explicit two-coordinate quotient
map from Theorem 9 gives $U\cong\mathbb Z^2$, whose three distinct
support values are $v_0=a,v_1=b,v_2=-a-b$, each with multiplicity two.

Any permutation of these three vectors respects their sole relation and
therefore defines a homomorphism of $U$; the inverse permutation gives
its inverse. Thus their support group is exactly
$K=\operatorname{Sym}(3)$. Theorem 3 gives (21). Equivalently, the
hypergraph itself recognizes each two-element fiber: two distinct
vertices are in the same fiber exactly when no three-edge contains both,
since any two differently colored vertices extend to a transversal.
Thus all its label symmetries are precisely the independent fiber swaps
and permutations of the three fibers.

The comparison $U\to\mathbb Z/7$ is onto, with
$(v_0,v_1,v_2)\mapsto(1,2,4)$, but is not injective. Indeed, the support
swap $v_0\leftrightarrow v_1$ sends the kernel element $2v_0-v_1$ to
$2v_1-v_0$, whose image is $3\ne0\pmod7$. It cannot descend to the
arithmetic target. Counting only support multipliers in that target would
give $2^3\cdot3=24$, missing half the full label group. $\square$

**Theorem 11 (Three copies restore the missing relations).**
For $q=1,m\ge3$, actual zero subsets force

$$
U\cong\mathbb Z/7,\qquad
G\cong\operatorname{Sym}(m)^3\rtimes C_3,\qquad |G|=3(m!)^3.
\tag{23}
$$

There are $3m$ distinct actual zero masks whose rows form an integer
basis of $L=\ker\Phi$.

*Proof.* Use the triples $T_{a,j}$ of (9), now modulo $3$, the baseline
triple $R=\{(0,0),(0,1),(0,2)\}$, and the two four-element subsets

$$
\begin{aligned}
E_0&=\{(0,0),(1,0),(2,0),(0,2)\},\\
E_1&=\{(0,1),(1,1),(2,1),(0,0)\}.
\end{aligned}
\tag{24}
$$

Their count vectors are $(3,0,1)$ and $(1,3,0)$, with respective
integer weight sums $3+4=7$ and $6+1=7$. Copies $0,1,2$ are
distinct, so these really are $0/1$ masks. The triples have weight $7$.
They are distinct by their unique nonzero-copy vertex, except for $R$,
which uses only copy zero. The two four-masks differ in color counts,
and their cardinality distinguishes them from every triple. Their total
number is $3(m-1)+1+2=3m$.

Let $X:I\to C$ annihilate these masks, with $C$ any abelian group.
Subtracting $R$ from $T_{a,j}$ identifies all copies of each color,
so write their common values as $x_0,x_1,x_2$. The remaining equations
are exactly

$$
x_0+x_1+x_2=0,\qquad3x_0+x_2=0,\qquad3x_1+x_0=0.
$$

The second gives $x_2=-3x_0$; the first then gives $x_1=2x_0$, and
the third gives $7x_0=0$. Hence, with $c=x_0$,
$(x_0,x_1,x_2)=(c,2c,4c)$, $7c=0$, uniquely. Conversely every such
assignment annihilates every actual zero subset: if its counts are
$0\le c_j\le m$, its integer weight is $c_0+2c_1+4c_2$, and it is
zero modulo $7$ exactly when that integer is a multiple of $7$.
Its $X$-sum is the same multiple of $7c$, hence zero.

To determine the integral quotient, let $L_*$ be the selected span and
$Q=F/L_*$. The just-proved reconstruction applied to coordinate classes
gives $e_{a,j}+L_*=2^jc$, $7c=0$. The maps
$\beta:\mathbb Z/7\to Q$, $\bar n\mapsto nc$, and
$\gamma:Q\to\mathbb Z/7$ induced by the actual weights are inverse:
$\gamma\beta$ fixes $1$, and $\beta\gamma$ fixes every coordinate
generator. Therefore $L_*=\ker\Phi$, and since all selected rows are
actual zero rows, $L_*=L$. There are $3m$ selected rows; each
$7e_{a,j}$ lies in their span, so the rational-span and independence
argument of Proposition 7 proves that they form a free integer basis.
Finally Theorem 8, with $M=7$ and exact order three, proves (23) for the
full hypergraph. The repeated quotient classes are exactly the copies of
each color, whereas the three arithmetic values $1,2,4$ are distinct.
$\square$

**Corollary 12 (Sharp multiplicity classification).**
For every $q,m\ge1$, the quotient and full group are given by the
following disjoint cases:

| Parameters | $U$ | $G$ | Order |
| --- | --- | --- | --- |
| $m=1$ | $\mathbb Z^{2q}$ | $\operatorname{Sym}(3)^q\rtimes\operatorname{Sym}(q)$ | $6^q q!$ |
| $q=1,m=2$ | $\mathbb Z^2$ | $\operatorname{Sym}(2)^3\rtimes\operatorname{Sym}(3)$ | $48$ |
| $q\ge2,m\ge2$, or $q=1,m\ge3$ | $\mathbb Z/M$ | $\operatorname{Sym}(m)^\ell\rtimes C_\ell$ | $\ell(m!)^\ell$ |

*Proof.* The cases exhaust the positive integers and follow respectively
from Theorems 9, 10, and 6–8 together with Theorem 11. For $m=1$, the
double-copy masks do not exist. For $q=1$, the proposed $D_n$ in (9)
would repeat the vertex $a_n$, since $2q+1=3q$; its four-term equation
is therefore not the sum over that set. At $m=2$, the three-copy
four-masks (24) do not exist, and Theorem 10 lists all actual zero subsets,
so no other actual row supplies their missing relations. At $m\ge3$,
(24) supplies them. Thus multiplicity changes the integral quotient and
its support group as well as the factors $m_v!$. $\square$

*Mathematical citation 12.1.* The parameter-specific mask reconstruction,
binary-block zero-set descriptions, and their combination with the
integer relation quotient in Theorems 6–12 are repo-derived. The free
abelian, quotient, and wreath-product constructions used in the proofs
are the established mathematics cited in [1]–[3]; no originality or
priority assertion is made for this combination.

**Proposition 13 (Conditional integral rigidity).**
Let integer weights $w_i=g v_i$ have $g>0$, $v_i\in\mathbb Z$.
Suppose the $v_i$ generate $\mathbb Z$, and the actual integer-zero
subset rows generate

$$
L=\ker\Psi,\qquad\Psi:F\to\mathbb Z,\quad\Psi(e_i)=v_i.
\tag{25}
$$

Then every full integer-zero symmetry satisfies
$v_{p(i)}=\epsilon v_i$ for a single $\epsilon\in\{1,-1\}$. Its full
group is trivial if and only if the $v_i$ are pairwise distinct and
their multiset is not invariant under negation. In particular, distinct
normalized weights and failure of negation invariance imply rigidity
under the two stated hypotheses of completeness and generation.

*Proof.* Multiplication by nonzero $g$ in $\mathbb Z$ is injective,
so the original and normalized weights have the same zero subsets and
$\ker\Phi_w=\ker\Psi$. Proposition 4 and (25) identify $U$ with
$\mathbb Z$; the unnormalized image is $g\mathbb Z$. An automorphism
of $\mathbb Z$ and its inverse send $1$ to integers $a,b$ with
$ab=1$, hence $a=b=1$ or $a=b=-1$. Theorem 2 proves the claimed
single sign. Theorem 3 identifies the kernel as the product of
permutation groups of equal normalized-weight fibers. A repeated value
allows a nontrivial transposition, so triviality requires distinctness.
The support group contains $-1$ exactly when the multiset is invariant
under negation. If it does, it has a lift by Theorem 3, and that lift is
nonidentity: generation ensures a nonzero weight, which changes sign.
If it does not, only $+1$ remains; with distinct fibers the entire group
is trivial. This proves both directions.

Absence of nonzero opposite pairs is sufficient for failure of negation
invariance, since generation guarantees a nonzero weight. These
conditions do not establish (25). For example, weights $1,2$ generate
$\mathbb Z$, are distinct, and have no opposite pair, but only the empty
subset is zero. Thus $L=0$, whereas $2e_0-e_1\in\ker\Psi$ is nonzero,
and the full label group is $\operatorname{Sym}(2)$. An application to
any particular integer family therefore requires independent proofs of
(25), generation, distinctness, and failure of negation invariance. The
following corollary discharges them for the stated exceptional19 family.
$\square$

**Corollary 13.1 (Exceptional19: an integral quotient and a rigid physical action).**
For every $r\in\mathbb N$, including $r=0$, put
$d=18r+12$, $B=2^d$, $I=\operatorname{Fin}(3d)$, and retain all original
physical labels. The actual integer weights and their primitive normalization are

$$
w_i=\operatorname{SourceWidth.actualSource}(3d,(B-1)(2B-3),i)
   =g v_i,\qquad g=19(B-1)>0,\qquad
v_i=\operatorname{primitive}(r,i).
$$

Let $S_k=\operatorname{selectedMask}(r,k)$, $k\in\operatorname{UpperIndex}(r)$,
be the archived selected family. Its $3d-1$ literal $0/1$ indicators form
an integer basis of $\ker\Phi_w=\ker\Psi$, where $\Psi(e_i)=v_i$;
each $S_k$ is an actual integer-zero subset. Hence
$L=\langle r_{S_k}\rangle_{\mathbb Z}=\ker\Psi$. Moreover, with
$\operatorname{place}(p,j)=pd+j$,

$$
-3v_{\operatorname{place}(0,0)}+2v_{\operatorname{place}(2,0)}=1,
\qquad U\xrightarrow[\ u_i\mapsto v_i\ ]{\sim}\mathbb Z,
\qquad \operatorname{im}\Phi_w=g\mathbb Z.
$$

Thus the primitive comparison is onto $\mathbb Z$; the actual comparison
$U\to\mathbb Z$ is multiplication by $g$ under this identification and
is an isomorphism onto $g\mathbb Z$, a proper subgroup of $\mathbb Z$.
For every abelian group $C$ (Lean: `AddCommGroup`) and every $X:I\to C$
annihilating the selected masks, reconstruction is

$$
X(i)=v_i c,\qquad
c=-3X(\operatorname{place}(0,0))+2X(\operatorname{place}(2,0)).
$$

This is integer scalar multiplication in $C$, with no torsion restriction;
the displayed unit relation makes $c$ unique. Conversely every such assignment
annihilates all actual integer-zero subsets. The verified weights are injective
and have no opposite pair $w_i=-w_j$, so the normalized weights are distinct
and their support is not negation-invariant. All four hypotheses of
Proposition 13 are therefore discharged here. In (4), every fiber $I_v$ is
a singleton and $K=1$, giving $G=1$ for the full original physical action.

The stronger verified endpoint says, for every $p\in\operatorname{Sym}(I)$,

$$
\left(\forall k\in\operatorname{UpperIndex}(r),\quad
       \sum_{i\in p(S_k)}w_i=0\right)\quad\Longleftrightarrow\quad p=1.
$$

Only these $3d-1$ image tests are required; $p$ need not permute the selected
family. This is a sufficiency statement, with no minimality claim. To see
the proof mechanism, apply reconstruction over $\mathbb Q$ to
$X(i)=w_{p(i)}$ and divide by the nonzero scale $g$, obtaining
$w_{p(i)}=a w_i$. Permutation invariance of the positive sum
$\sum_i w_i^2$ gives $a^2=1$. The no-opposite-pair result excludes
$a=-1$, and weight injectivity turns $a=1$ into $p=1$. A symmetry of the
full integer-zero family satisfies these tests, giving the full endpoint.

*Pinned formal inputs and scope.* In namespace
`D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis`, the inputs are
`actual_selected_upper_integer_basis` and `actual_selected_upper_span_eq_kernel`
in module [UpperBasis.Result][4], `actual_selected_upper_reconstruction` in
[UpperBasis.Reconstruction][5], and `card_upperIndex`, `selected_literal_zero`
in [UpperBasis.Family][6]. They are preserved from
`391268a84ffb37c55416046d7bcb50da25958f88` in the verified archive at
`debf516d5b45bd4a64f5098da774c34cad005c02`. The scale identity
`D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice.source_eq_scale_primitive`
is in [ZeroLattice.Weights][7]. At the latter pin, module
[PermutationStabilizer][8] proves
`D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer.actual_zero_family_perm_iff`
and, in the same namespace, `actual_selected_image_zero_perm_iff`;
[PermutationStabilizer.WeightSeparation][9] supplies its private lemmas
`actual_weights_injective` and `actual_weights_no_negative_pair`.
The links specify the full module paths at that immutable pin; source and
compiled-endpoint hashes are recorded in the companion source manifest.
These are kernel-verified formal inputs; the quotient/fiber interpretation
above is ordinary mathematical exposition, not a new formal verification.
This integral corollary neither
classifies the modular symmetry group nor proves unrestricted four-gap $J$;
the literature and attribution boundaries above remain unchanged.

**Proposition 14 (Reduction adds relations, not an automatic group inclusion).**
For integer weights and a positive modulus $h$, let $\mathcal H_{\mathbb Z}$
and $\mathcal H_h$ be their integer and modular zero-subset families, and
write $L_{\mathbb Z},L_h,U_{\mathbb Z},U_h$ for their relation groups
and quotients. Then $\mathcal H_{\mathbb Z}\subseteq\mathcal H_h$, but
this inclusion alone does not imply
$G_{\mathbb Z}\subseteq G_h$. The precise criterion for
$p\in G_{\mathbb Z}$ is

$$
p\in G_h\quad\Longleftrightarrow\quad
\alpha_p(\ker q_h)=\ker q_h,
\qquad
q_h:U_{\mathbb Z}\twoheadrightarrow U_h.
\tag{26}
$$

Under the completeness and generation hypotheses of Proposition 13,
however, every integer symmetry preserves modular zero subsets for
every $h$.

*Proof.* Integer zero implies modular zero, so
$L_{\mathbb Z}\subseteq L_h$ and
$q_h(f+L_{\mathbb Z})=f+L_h$ is a well-defined surjection with kernel
$L_h/L_{\mathbb Z}$. For $p\in G_{\mathbb Z}$, the preimage in $F$
of this kernel is $L_h$, and $\alpha_p$ is induced by $P_p$.
Consequently its invariance is exactly $P_p(L_h)=L_h$, equivalent to
$p\in G_h$ by Theorem 2. This proves (26).

For a full counterexample take indexed weights
$(w_0,w_1,w_2,w_3)=(1,-1,2,4)$ and $h=5$. A nonempty integer-zero
subset must contain the sole negative weight $-1$, and its positive
part must sum to $1$. The only possibility is the singleton weight
$1$; hence the integer-zero subsets are exactly
$\varnothing,\{0,1\}$. The swap $p=(2\ 3)$ preserves both, so
$p\in G_{\mathbb Z}$. But $\{0,3\}$ has weight $5$, zero modulo
$5$, while its image $\{0,2\}$ has weight $3$, nonzero modulo $5$.
Thus $p\notin G_5$, despite a nonempty integer-zero edge.

Finally Proposition 13 gives $w_{p(i)}=\epsilon w_i$ under its
completeness and generation hypotheses, irrespective of distinctness.
Every subset sum is then multiplied by the unit $\epsilon=\pm1$
modulo $h$, which proves the asserted group inclusion under those
additional hypotheses. No coprimality between $g$ and $h$ is needed.
A single modular symmetry failing over the integers would, by itself,
only witness a set difference; strict group inclusion also requires the
inclusion just proved or another proof of it. $\square$

*Mathematical citation 14.1.* The comparison and invariant-kernel argument
is the quotient correspondence of [2] applied to actual zero-subset
relations. The integral-rigidity application and the explicit modular
counterexample above are repo-derived.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/FreeAbelianGroup.html
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/QuotientGroup/Basic.html
[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/RegularWreathProduct.html
[4]: https://github.com/the-omega-institute/trureturing/blob/debf516d5b45bd4a64f5098da774c34cad005c02/D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Result.lean
[5]: https://github.com/the-omega-institute/trureturing/blob/debf516d5b45bd4a64f5098da774c34cad005c02/D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Reconstruction.lean
[6]: https://github.com/the-omega-institute/trureturing/blob/debf516d5b45bd4a64f5098da774c34cad005c02/D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Family.lean
[7]: https://github.com/the-omega-institute/trureturing/blob/debf516d5b45bd4a64f5098da774c34cad005c02/D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Weights.lean
[8]: https://github.com/the-omega-institute/trureturing/blob/debf516d5b45bd4a64f5098da774c34cad005c02/D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer.lean
[9]: https://github.com/the-omega-institute/trureturing/blob/debf516d5b45bd4a64f5098da774c34cad005c02/D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/WeightSeparation.lean

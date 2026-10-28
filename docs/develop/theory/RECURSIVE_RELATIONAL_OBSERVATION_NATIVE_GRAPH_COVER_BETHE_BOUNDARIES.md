# Recursive relational observation: native graph-cover and Bethe boundaries

The constructor-network representation is equality-aware and admits arbitrary
whole-block potentials. This volume gives exact native cycle families showing
why two proposed upper substitutions fail: unrestricted graph-cover domination
and an optimized Bethe value used as a per-template upper bound. The examples
are finite, positive-rational and amplify by disjoint products. They do not
rule out a different sound cofinal verifier.

## 1. A native binary-potential embedding

**Definition 1.1 (perfect binary leaves).** Fix $h\ge1$, put $d=h+1$ and
$m=2^h$. For a bit string $b\in\{0,1\}^m$, let $u_b$ be the actual perfect
height-$h$ tree whose leaves, in left-to-right order, are $\alpha$ for $0$ and
$\beta$ for $1$. These are elements of the unchanged canonical interface
$S_d$. Let $f:\{0,1\}^m\to\mathbb Q_{\ge0}$ and give every other state of
$S_d$ a fixed positive rational weight $\eta$. Write

$$
W=\sum_{x\in S_d}w(x),
\qquad w(u_b)=f(b),
\qquad \mu(x)=w(x)/W.
\tag{GCB.1}
$$

When $f$ is strictly positive, $\mu$ is strictly positive on all of $S_d$;
the incidence identity itself also allows zeros in $f$.

For every internal target $q$ with $|q|<h$, impose the constant factor
$\Gamma_q=(0,0)$. For every terminal target $q$ of length $h$, choose the
successor slot of that terminal in a cyclic partition of all terminal slots and
use one native donor literal at that successor slot, decoding

$$
\alpha\mapsto(2,1),
\qquad \beta\mapsto(1,0),
\qquad \mathsf{branch},\mathsf{absent}\mapsto(2,1).
\tag{GCB.2}
$$

The donor indices are arbitrary original block indices and may form cycles.
Every equation is a complete native target equation; no new query port is
introduced.

**Theorem 1.2 (exact binary incidence realization).** The solutions of this
complete native template are in bijection with assignments of one bit to each
terminal-slot class. In particular, for a binary potential incidence pattern
on the slots, the native mass is

$$
W^{-n}\sum_y\prod_i f(y|_{\text{slots of block }i}).
\tag{GCB.3}
$$

Each whole-block potential occurs once.

**Proof.** The internal equations force every strict internal target to be a
branch endpoint, hence the prescribed perfect shape. The terminal equations
force a labelled leaf and identify the donor leaf bit with the terminal bit.
Along a successor cycle all bits are equal, so one class bit remains. Restricting
to the classes and assembling the ordered perfect trees are inverse maps. The
product weight in (GCB.3) is therefore the native whole-block product, with no
replica multiplicity. $\square$

The equality and constructor conditions in this proof are exactly those of
[CBN, Theorems 2.2, 4.2 and 6.2]. In particular, the representation does not
replace a repeated reply by independent replicas and does not factor an
arbitrary block weight into pairwise constructor weights.

## 2. The two-state cycle calculation

For $`h=1`$ write $`u_{ab}=\langle\operatorname{bit}(a),\operatorname{bit}(b)\rangle`$
and let $`F=(f(a,b))_{a,b\in\{0,1\}}`$. Choose the successor pattern in which
block $`i`$ has state $`u_{b_i b_{i+1}}`$ on a cycle of length $`\ell`$. Then

$$
Z_\ell(F)=\frac{\operatorname{tr}(F^\ell)}{W^\ell}.
\tag{GCB.4}
$$

Take the positive rational matrices

```math
F_-=\begin{pmatrix}1&3\\3&1\end{pmatrix},
\qquad
F_+=\begin{pmatrix}3&1\\1&3\end{pmatrix},
```

and give each of the other seven states of $S_2$ weight $1/10$. In both cases
$W=87/10$. The eigenvalues are $4,-2$ for $F_-$ and $4,2$ for $F_+$, so

$$
Z_\ell(F_-)=\frac{4^\ell+(-2)^\ell}{W^\ell},
\qquad
Z_\ell(F_+)=\frac{4^\ell+2^\ell}{W^\ell}.
\tag{GCB.5}
$$

This is an actual complete native template, not a factor-graph analogy. The
single source and the one original-root late Read remain as in (JTC.2); a
terminal target uses the chosen actual literal before the authentic count, and
all later counts use the credited $\Gamma$ decoder.

## 3. Failure of unrestricted graph-cover domination

**Proposition 3.1 (a connected two-sheet lift increases native mass).** For
$F_-$, a triangle has raw mass

$$
4^3+(-2)^3=56.
$$

Its connected two-sheet crossed lift is a six-cycle and has raw mass

$$
4^6+(-2)^6=4160>56^2=3136,
\qquad \frac{4160}{56^2}=\frac{65}{49}.
\tag{GCB.6}
$$

**Proof.** The cycle formula (GCB.5) gives both traces. The crossed matching
is a connected two-sheet lift of the triangle and preserves the same native
terminal donor/decoder equations. $\square$

Pad the base by one fixed $u_{00}$ block and the lift by its two fixed copies.
The base and lift then have four and eight blocks, respectively, while their
raw masses remain $56$ and $4160$. After normalization the ratio is still
$65/49$. Taking $r$ disjoint padded gadgets multiplies the ratio to
$(65/49)^r$. Therefore the proposed unrestricted comparison

$$
Z(\text{a }k\text{-cover})\le Z(\text{base})^k
\tag{GCB.7}
$$

is false even for positive rational native weights, and no correction with
logarithm $o(n)$ can repair this rule on the displayed family. The obstruction
also occurs at dyadic lengths: take $r=2^j$, with base length $4r$ and
lift length $8r$. It is scoped to the rule itself; Ruozzi's graph-cover inequality has a
log-supermodularity hypothesis that the anti matrix does not satisfy.

A consistent relabelling of the three triangle bits cannot remove the example:
each anti edge would require opposite flip choices, whose xor around the
triangle is impossible. This is a native cycle obstruction, not a claim that
all reblocking or all global certificates fail.

## 4. Failure of an optimized Bethe upper substitution

For either displayed matrix put $P=F/4$. It is doubly stochastic. On an
$\ell$-cycle, a locally consistent edge law $\tau$ gives the Bethe objective

$$
\sum_i\left[H(B_{i+1}\mid B_i)+
\mathbb E\log_2\frac{F(B_i,B_{i+1})}{W}\right]
\le \ell\log_2\frac4W.
\tag{GCB.8}
$$

Indeed, each summand equals $\log_2(4/W)$ minus a nonnegative conditional
relative entropy against $P$. Uniform vertex marginals and edge law $P/2$
achieve equality, so the optimized Bethe mass is $(4/W)^\ell$.

For $F_+$ at length four, the exact native mass is
$272/W^4$, while Bethe gives $256/W^4$. The rational inequalities

$$
\left(\frac{40}{87}\right)^4
<\left(\frac{23}{50}\right)^4
<\frac{272}{(87/10)^4}
\tag{GCB.9}
$$

show that a cap chosen from the optimized Bethe value can be false on an
actual complete native template. Disjoint four-cycles amplify the ratio to
$(17/16)^r$. Consequently a correction whose logarithm is $o(n)$ cannot turn
this per-template upper substitution into a sound universal cap.

This does not say that every Bethe method is invalid: a theorem with explicit
loop or support hypotheses may have a different direction. It says that the
optimized Bethe value alone is an average-style quantity and is not an upper
bound for every arbitrary native template with owned joint weights.

**Convention 4.1 (the precise literature hypotheses).** Vontobel's graph-cover
identity identifies the optimized Bethe partition value with a limsup of
averaged finite-cover partition functions; it is not domination of each
individual cover. Ruozzi's upper comparison requires binary
log-supermodular factors, a hypothesis violated by $F_-$. Bounds for
permanents with a girth correction require a permanent support graph and a
specified girth, neither of which is a native all-template hypothesis. These
conditions explain why (GCB.7)--(GCB.9) are counterexamples to the proposed
unrestricted substitutions only.

**Proposition 4.2 (the explicit loop charge and global-cap boundary).**
For a disjoint union of $c$ displayed cycles with $n$ blocks, the exact
mass obeys

$$
Z=\prod_{j=1}^c\frac{4^{\ell_j}+(\pm2)^{\ell_j}}{W^{\ell_j}}
\le2^c(4/W)^n.
$$

This is a sound upper for that cycle subfamily. The false per-template
value $23/50$ in (GCB.9) is not a global cap shown to evade small-length
checks: for these same weights $\beta(\mu)\ge8/W$ already at length one.

**Proof.** Each eigenvalue correction has absolute value at most
$4^{\ell_j}$, giving the displayed bound by multiplication. The four
states $u_{00},u_{01},u_{10},u_{11}$ are locally admissible: the root is
branch and each leaf target uses its own literal. Their raw weight is
eight for either matrix. Thus they give the stated length-one pressure
lower. In particular the cycle calculation refutes the two defined
upper substitutions and their subexponential repairs; it does not show
an invalid global cap escaping every finite test or an obstruction at
optimizing weights. $\square$

[Vontobel]: https://arxiv.org/html/1012.0065v2
[Ruozzi]: https://arxiv.org/html/1202.6035
[DJPR]: https://arxiv.org/html/2609.02017v1

## 5. Paid full-family realizations of the counterexamples

The counterexamples can be embedded in the original finite source family. For
$n=2^H$ blocks, put the height-one states $u_{ab}$ at the frontier of the
public perfect height-$H$ scaffold in the right subtree and take $D=H+2$.
Every block literal is the full original-root word obtained by prefixing its
public scaffold address. Internal scaffold targets are constants and terminal
targets are the actual leaf literals used in (GCB.2).

For the padded anti base use $n=4,D=4$ and merge exactly the eight native
solutions into one canonical code name; all other canonical states receive
separate names. Since $|S_4|=15131$, the attained alphabet is
$15131-8+1=15124$. For its connected lift use $n=8,D=5$ and merge its
$64$ solutions; since $|S_5|=228947163$, the attained alphabet is
$228947163-64+1=228947100$. The preparation scans all $Rq$, $q\in W_D$, before
the request, using at most $2^D-1$ charged Reads, maximum literal length $D$
and $(D-1)2^D+1$ submitted letters. The merged name is isolated by the paid
handoff; the reader chooses at most one fresh original-root Read before any
authentic count and then uses the all-count decoder. These codes are attained
constructions, deliberately nonoptimal, and carry no free source identity,
subtree or navigation descriptor.

## 6. Boundary of the negative result

The cycle calculations reject the two stated comparison mechanisms on actual
native instances while preserving equality, correlations, cycles and whole
block weights. They do not establish a universal obstruction to finer cuts,
global recolouring, effective approximation, computability, or a different
finite proof language. They also do not change the credited interval
$\log_2(33/13)/8\le\lambda<3/16$.

A successful original solution still needs a sound cap for every complete
native template and accepted endpoints cofinal in the same unrestricted
$\sigma_d$, or a uniform effective finite-length error. The exact general
$M_1(D)$ and the broader space-time mutual-recovery programme remain open.

[CBN]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[JTC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_TARGET_CERTIFICATES.md
[FMR]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NCE]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md

## 追加锚（本行以下为增补区）

## 7. A direct simple-cycle graphical-norm class

**Convention 7.1 (original interface and credited carrier).** Retain the
source, substitution, replies and complete paid-export contract of
[NPC, Definitions 1.1 and 2.2 and Assumption 1.2][GCBNPC]. In particular,

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
W_D=\{q:|q|\le D-1\},\qquad \mathcal P_D=\{Rq:q\in W_D\}.
\tag{GCB.10}
$$

The source is stationary through source-blind preparation and later
acquisition. Preparation terminates on every source and obtains source
dependence only through charged original-root Reads. Its export contains
every accessible surviving distinction. A public source-independent
request arrives only after export; its reader makes at most one fresh
original-root Read before the reply and before any authentic count, then
predicts every subsequently supplied count without further Reads.
Handoff, isolation, lawful entry, source continuity and authentication
remain paid service premises.

Write $\operatorname{bit}(0)=\alpha$ and
$\operatorname{bit}(1)=\beta$. The canonical alphabets are

$$
C_0=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup\{\langle x,y\rangle:x,y\in S_d\}.
\tag{GCB.11}
$$

Use the credited full temporal factor $\Gamma_q$ and its all-count
decoder from [NPC, Convention 2.1][GCBNPC]. For the leaf factors used
below, if $e\in\{0,1\}$ and $r$ is a suffix, this says explicitly

$$
\Gamma_r(\operatorname{bit}(e))=
\begin{cases}
(2-e,1-e),&r=\varepsilon,\\
(\#L(r)+2\#R(r)+2-e,\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{GCB.12}
$$

It covers initially absent suffixes. A branch endpoint has factor
$(0,0)$. Equality of full factors is equality of all-count trajectories.

**Definition 7.2 (the credited positive binary cycle).** Fix $d\ge2$,
put $B=|S_d|+2$, and use exactly the whole-block probability of
[COK, Definition 21.1][GCBCOK]:

$$
\mu(\langle\alpha,\alpha\rangle)
=\mu(\langle\beta,\beta\rangle)=2/B,\qquad
\mu(x)=1/B\quad\text{on every other }x\in S_d.
\tag{GCB.13}
$$

This is positive on the entire canonical alphabet. Set

$$
M=\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad
\Phi(a,b)=M_{ab}/B.
\tag{GCB.14}
$$

For an even $N\ge4$, indices are modulo $N$. Let the actual owner of
bit $s_i$ be the $L$ reply of block $i$. At every block prescribe the
complete native equations

$$
\Gamma_\varepsilon(x_i)=(0,0),\qquad
\Gamma_{Lr}(x_i)=\Gamma_r(\operatorname{bit}(s_i)),\qquad
\Gamma_{Rr}(x_i)=\Gamma_r(\operatorname{bit}(s_{i-1}))
\quad(Lr,Rr\in W_d).
\tag{GCB.15}
$$

Each nonconstant equation queries that indicated owner's actual $L$
literal. On excluded donor replies branch and absent, its total decoder
returns the corresponding full alpha-leaf factor. At the immediate
owner target this factor has reply alpha, different from either excluded
input. Thus the self equation guards the owner's reply to be alpha or
beta; this is not an extra observation of its domain.

The complete solution set is precisely

$$
\mathcal C_N=\{x(s):s\in\{0,1\}^N\},\qquad
x_i(s)=\langle\operatorname{bit}(s_i),
                   \operatorname{bit}(s_{i-1})\rangle.
\tag{GCB.16}
$$

Indeed the root is branch, its guarded $L$ child is its owner leaf, and
the immediate $R$ factor forces the indicated previous owner's leaf.
These immediate equations force (GCB.16); conversely every such tuple
satisfies all the suffix equations (GCB.15). Reading its actual $L$
replies recovers its unique bit assignment. There are exactly $2^N$
solutions, each seed occurs in two blocks, and each whole-block weight
occurs once. This is the binary realization of Theorem 1.2 and the
single alternating reciprocal-cover cycle of [COK, Proposition
21.2][GCBCOK], with the cyclic blocks relabelled. The native realization,
positive law and trace calculation are credited suppliers.

In particular, the exact mass is

$$
Z_N=\sum_s\prod_i\Phi(s_i,s_{i-1})
   =\frac{\operatorname{tr}(M^N)}{B^N}
   =\frac{3^N+1}{B^N},
\tag{GCB.17}
$$

since the eigenvalues of $M$ are $3$ and $1$.

**Definition 7.3 (all positive same-pair compensations).** The graph
has the $N$ bit vertices and exactly the unordered edges $\{i,i-1\}$.
Choose arbitrary positive finite vertex measures $\tau_i(a)$ and
positive real pair tables $\Psi_i(a,b)$ on these same edge scopes,
subject only to the global pointwise identity

$$
\prod_i\bigl[\Psi_i(s_i,s_{i-1})\tau_i(s_i)\bigr]
      =\prod_i\Phi(s_i,s_{i-1})
\qquad(s\in\{0,1\}^N).
\tag{GCB.18}
$$

The measures need not be probabilities. The reported upper is one
application of the Sah--Sawhney--Stoner--Zhao graphical inequality on
this unchanged graph:

$$
U(\Psi,\tau)=\prod_i
 \|\Psi_i\|_{K_{2,2};\tau_i,\tau_{i-1}},
\tag{GCB.19}
$$

where the exact convention is

$$
\begin{aligned}
\|\Psi_i\|_{K_{2,2};\tau_i,\tau_{i-1}}^4
={}&\sum_{a,a',b,b'\in\{0,1\}}
 \Psi_i(a,b)\Psi_i(a,b')\Psi_i(a',b)\Psi_i(a',b')\\
&\hspace{8mm}\cdot\tau_i(a)\tau_i(a')
                 \tau_{i-1}(b)\tau_{i-1}(b').
\end{aligned}
\tag{GCB.20}
$$

All pointwise compensations between the pair scopes are allowed;
separate equality of each compensated table with its original is not
required. Allowing nonnegative tables would not enlarge this class:
every pair entry extends to an actual binary assignment with positive
right side in (GCB.18), so no such entry can vanish. The class contains
no scope enlargement, clustering, extra variables, residual loop rule,
higher graphical norm or additional proof leaf. The replicas in
(GCB.20) are analytical summation variables, not readable source copies.

**Proposition 7.4 (sound direction of the direct bound).** Every
choice in Definition 7.3 satisfies $Z_N\le U(\Psi,\tau)$.

Proof. The graph is a simple triangle-free cycle, with no isolated
vertices and degree two at every vertex. [Sah--Sawhney--Stoner--Zhao,
Theorem 1.12][GCBSSSZ] bounds its partition integral by the product of
$K_{d_v,d_u}$ edge norms. The finite binary spaces, positive finite
measures and nonnegative measurable pair functions meet its hypotheses;
their reversed degree order is $(2,2)$. The integral equals $Z_N$ by
(GCB.18), giving the claimed upper direction. The cited theorem and
its allowance of unnormalized measures supply this soundness step.
$\square$

## 8. Complete compensation normal form on the same cycle

**Theorem 8.1 (all pair compensations reduce to vertex ratios).** For
the data of Definition 7.3, put

$$
A_i(a,b)=\Psi_i(a,b)\sqrt{\tau_i(a)\tau_{i-1}(b)}.
\tag{GCB.21}
$$

There are positive functions $g_i:\{0,1\}\to(0,\infty)$ and
positive constants $c_i$ with $\prod_i c_i=1$ such that

$$
A_i(a,b)=c_{i-1}\Phi(a,b)\frac{g_i(a)}{g_{i-1}(b)}.
\tag{GCB.22}
$$

Conversely every choice of these $g_i,c_i$ and positive finite
$\tau_i$ gives an admissible compensation by solving (GCB.21) for
$\Psi_i$. Moreover

$$
\|\Psi_i\|_{K_{2,2};\tau_i,\tau_{i-1}}
       =\|A_i\|_{K_{2,2}},
\tag{GCB.23}
$$

where the last norm uses counting measures. Thus (GCB.22) describes the
entire optimization in (GCB.19), including vertex-measure choices.

Proof. Each vertex measure is split into a square root on its two
incident edges, so (GCB.18) becomes
$\prod_i A_i(s_i,s_{i-1})=\prod_i\Phi(s_i,s_{i-1})$.
In the fourth-power sum for the counting norm of $A_i$, each replicated
vertex appears twice. Its two square roots multiply to its one measure
factor in (GCB.20). This proves (GCB.23) exactly.

Define $r_i(a,b)=\ln(A_i(a,b)/\Phi(a,b))$. Then

$$
\sum_i r_i(s_i,s_{i-1})=0
\qquad(s\in\{0,1\}^N).
\tag{GCB.24}
$$

Fix all bits except $s_i,s_{i-1}$ and take the alternating mixed
finite difference in those two bits. Since $N\ge4$, no other edge
scope contains both, and each other summand cancels. Consequently

$$
r_i(0,0)+r_i(1,1)-r_i(0,1)-r_i(1,0)=0.
\tag{GCB.25}
$$

Explicitly set $u_i(a)=\exp(r_i(a,0))$ and
$v_i(b)=\exp(r_i(0,b)-r_i(0,0))$. Equation (GCB.25) gives
$A_i(a,b)/\Phi(a,b)=u_i(a)v_i(b)$ at all four inputs. Regrouping
the full product identity by vertices now gives

$$
\prod_j u_j(s_j)v_{j+1}(s_j)=1.
\tag{GCB.26}
$$

Varying just $s_j$ shows that $u_j(a)v_{j+1}(a)=c_j$ is constant
in $a$, and the constants have product one. With $g_j=u_j$, this
is exactly (GCB.22). Conversely the vertex ratios telescope for every
assignment, as do the $c_i$. Substitution into (GCB.21) therefore
recovers (GCB.18). No existence assumption about an optimizer entered
this characterization. $\square$

## 9. Exact convex optimization and the extensive residual

**Theorem 9.1 (sharp direct-cycle norm bound).** For every $d\ge2$
and every even $N\ge4$, optimizing over all the tables and vertex
measures of Definition 7.3 gives

$$
\boxed{\displaystyle
\inf_{\Psi,\tau}U(\Psi,\tau)=\frac{82^{N/4}}{B^N}.}
\tag{GCB.27}
$$

The infimum is attained by $\Psi_i=\Phi$ and counting vertex
measures. In particular the optimum includes arbitrary positive real
global compensations, not only independently normalized edge tables.

Proof. The constants $c_i$ in (GCB.22) cancel from the product of
norms by positive homogeneity. Put $h_i(a)=\ln g_i(a)$ and consider
the finite real-valued function

$$
F(h)=\sum_i\ln\left\|
 \Phi(a,b)\exp\bigl(h_i(a)-h_{i-1}(b)\bigr)
                         \right\|_{K_{2,2}}.
\tag{GCB.28}
$$

Each summand is one quarter of a log-sum-exp of affine functions of
all entries of $h$. The exponent in its $(a,a',b,b')$ term is
$2[h_i(a)+h_i(a')-h_{i-1}(b)-h_{i-1}(b')]$, with a positive
coefficient made from four entries of $\Phi$. Log-sum-exp is convex:
its Hessian is the covariance matrix of the affine coefficient vectors
under their normalized positive exponential weights. Hence $F$ is
convex on the whole finite-dimensional space.

Let $h_i^{\rm flip}(a)=h_i(1-a)$. Since
$\Phi(1-a,1-b)=\Phi(a,b)$, reindexing the four summation bits at
every edge gives $F(h^{\rm flip})=F(h)$. Convexity therefore gives

$$
F(h)\ge F\bigl((h+h^{\rm flip})/2\bigr)=F(0).
\tag{GCB.29}
$$

For the last equality, the midpoint has the constant value
$k_i=(h_i(0)+h_i(1))/2$ at vertex $i$. Its edge table is
$\exp(k_i-k_{i-1})\Phi$; those scalar multipliers telescope in
the product of homogeneous norms. Zero vertex functions are feasible,
so this proves both optimization inequalities without presuming that
an arbitrary minimizing sequence converges.

Finally, directly from (GCB.20) with counting measures,

$$
\|\Phi\|_{K_{2,2}}^4
=B^{-4}\operatorname{tr}\bigl((MM^{\mathsf T})^2\bigr)
=\frac{3^4+1}{B^4}=\frac{82}{B^4}.
\tag{GCB.30}
$$

Multiplying the $N$ identical optimal norms proves (GCB.27).
$\square$

**Corollary 9.2 (exact residual and failure of uniform vanishing error).**
Let $U_N^{\rm opt}$ be (GCB.27) and set
$\kappa=\tfrac14\log_2(82/81)>0$. Then

$$
\begin{aligned}
\log_2 U_N^{\rm opt}-\log_2 Z_N
 &=\frac N4\log_2\frac{82}{81}-\log_2(1+3^{-N})\\
 &>N\kappa-1,\\
\lim_{\substack{N\to\infty\\N\text{ even}}}
 \frac1N\log_2\frac{U_N^{\rm opt}}{Z_N}&=\kappa.
\end{aligned}
\tag{GCB.31}
$$

The same limit holds along actual dyadic lengths $N=2^H$, $H\ge2$.
Thus the defined direct-cycle contraction, even with all same-pair
compensations and vertex measures optimized, has no uniformly $o(N)$
per-template logarithmic error on the actual native family.

Proof. Divide (GCB.27) by (GCB.17) and take logarithms. The remaining
correction lies strictly between zero and one and tends to zero, proving
every assertion. At $N=4$ the bound is exact, consistently with a cycle
being $K_{2,2}$. At $N=8$ the optimal ratio is $6724/6562=3362/3281$.
Exactness at length four therefore supplies no vanishing-error premise
at larger lengths. $\square$

## 10. Credited paid realization on the full actual source family

**Proposition 10.1 (complete acquired names for the cyclic fibers).**
Fix $d\ge2$ and an even $N\ge4$, put $H=\lceil\log_2N\rceil$,
$K=2^H$ and $D=d+H$. The cycle of
Definition 7.2 has the full-family paid realization of [COK, Proposition
23.2 and Convention 23.4][GCBCOK], with exactly

$$
R_D=|S_D|-2^N+1
\tag{GCB.32}
$$

complete attained names on every variable-shape source in $\mathcal F_D$.
One sufficient source-blind preparation uses, on every source,

$$
T_{\rm prep}=2^D-1,\qquad Q_{\rm prep}=D,\qquad
A_{\rm prep}=(D-1)2^D+1.
\tag{GCB.33}
$$

Every permitted late target is answered using zero Reads or one actual
original-root Read of length at most $H+2\le D$, chosen before its
reply and every authentic count. These are credited sufficient
construction costs and an attained nonoptimal code, not acquisition
minima or a value of $M_1(D)$.

Proof of the resource correspondence. Put the $N$ actual blocks at the
first $N$ public frontier addresses $a_i$, $|a_i|=H$, of a perfect
scaffold with $K$ slots in the right subtree of
$t=\langle\alpha,v\rangle$; pad the other $K-N$ slots by alpha.
A single cycle of
the relative matching in COK Proposition 21.2 gives this even cycle,
up to the relabelling in Definition 7.2. At dyadic $N$ there is no
padding. The $2^N$ displayed canonical scaffold states are distinct members
of $S_D$.

Before receiving a target, the deterministic preparer actually submits
every original-root word $Rq$, $q\in W_D$, including absent replies,
in a fixed public order. These replies compute the credited canonical
completion $\pi_D(v)$. Merge exactly the displayed $2^N$ canonical
states into one fixed-width name and assign each other canonical state
its own name. Every name is attained because $\pi_D$ fixes $S_D$
and each of those canonical trees is an actual allowed right subtree.
This proves (GCB.32); the full-family fibers are the corresponding
inverse images under $\pi_D$. The name uses
$\lceil\log_2 R_D\rceil$ bits. Counting actual scan words gives
$\sum_{l=0}^{D-1}2^l=2^D-1$ Reads and
$\sum_{l=0}^{D-1}(l+1)2^l=(D-1)2^D+1$ submitted letters.

After a singleton name, all requested canonical factors are installed
and no Read is needed. After the merged name, a target above the
frontier or at a true block root has constant branch factor. A request
in a padded slot uses its fixed full alpha-leaf factor at the requested
suffix, with no Read. Every remaining request is $Ra_iLr$ or $Ra_iRr$.
The former queries $Ra_iL$ and
the latter queries $Ra_{i-1}L$. These are literal words on the same
stationary original source, of length $H+2$, not queries to a new
subtree root. Its one reply and the public suffix $r$ determine the
factor (GCB.12). These cases exhaust all requests of length at most
$D$, including initially absent suffixes. Canonicalization preserves
the queried replies and every requested full factor. Its scaffold and
owner occurrences are actually present, so homomorphic transport at
those occurrences, with COK's stated presence premise, applies at every
authentic subsequent count. The credited factor decoder then supplies
the entire required trajectory without another Read.

The scaffold, cyclic ordering, pairing and all tables are fixed public
installation. They are never source-varying free descriptors. Export
only the fixed-width name. The public allocation, fixed scan and padded
finite membership schedule accompany the declared paid handoff and
isolation of every other acquired distinction: constructor arrays,
selectors, buffers, lengths, control, transcripts and accessible timing.
Any extra surviving distinction would have to enlarge the complete
counted alphabet. This is precisely the credited COK construction;
neither the norm calculation nor its analytical replicas add an
operational port. $\square$

**Convention 10.2 (separate resources).** Public table generation and
installation, preparation work/control and temporary storage, selection
work, post-request workspace, address construction, final predictor
size, count representation, handoff, entry, isolation, authentication
and physical time remain separate resources. For a selected factor
$(b,c)$, $0\le b\le2D$ and $c\in\{0,1\}$, so the credited
$\lceil\log_2(2D+1)\rceil+1$ predictor bits are separate from the
complete retained name. No arbitrary competitor's preparation cost is
preserved, and no free total-efficiency or physical erasure claim is made.

## 11. Representation, optimized pressure and the remaining obligation

**Convention 11.1 (direct graph, equality lift and other certificate classes).**
In Definition 7.3 the vertices are the actual shared owner bits and the
edges carry their once-owned full pair potentials. The graph is $C_N$.
An equality-incidence representation instead introduces an analytical
factor tuple $y_i=(a,b)$ with atom measure $\Phi(a,b)$, keeps the
one bit vertex per owner, and attaches the two equality indicators
$\mathbf1_{y_{i,1}=s_i}$ and $\mathbf1_{y_{i,2}=s_{i-1}}$.
Its bipartite graph is $C_{2N}$. Equality forces exactly one tuple
$y_i=(s_i,s_{i-1})$ for each common bit assignment, with its potential
owned once. This is the credited equality-aware identity of [CBN,
Section 6][CBN] and [RRN, Theorem 5.2][GCBRRN]. The partition is
unchanged, but the norm inequality is applied to equality edges and
factor measures on different spaces. That lift is outside Definition
7.3; Theorem 9.1 asserts no optimized norm identity for it.

The cover comparison of Section 3 compares two different native
instances; Definition 7.3 keeps one instance and optimizes its pair
tables. The optimized Bethe substitution of Section 4 has its stated
direction and loop restrictions; Proposition 7.4 is a sound upper.
The whole-scope forest classes of [GDB, Sections 20--25][GCBGDB] mix
proper whole-star submodels or their entropy completions. They are not
the single contraction on all cycle edges optimized here. This theorem
also places no restriction on additional range, joint, scaffold,
stability, syndrome or recursive rules. Exact trace evaluation already
bypasses the specified norm error on this cyclic family.

**Proposition 11.2 (the chosen law is not pressure-optimal at depth two).**
For the law (GCB.13) at $d=2$, the credited unrestricted all-template
pressure is $\beta_2(\mu)=12/13$, while its minimum over whole-block
probabilities is $17/25$.

Proof by the credited depth-two formula. [RCE, Convention 14.1 and
Corollaries 15.1 and 15.3][GCBRCE] give

$$
\beta_2(w)=\max\{W-w(\alpha),W-w(\beta),
                    w(\alpha)+w(\beta)+\max_{g\text{ branch}}w(g)\},
\tag{GCB.34}
$$

and the probability minimum $17/25$. Here the raw total is $13$,
both root leaves have raw weight one, and the largest branch weight is
two. Thus the three normalized quantities are $12/13,12/13,4/13$.
This verifies the claimed value by direct application of that supplier.
The cycle mass has limiting root $3/13$, so this family is not near the
unrestricted pressure maximum at this law either. $\square$

**Open obligation 11.3 (the unchanged all-correlated goal).** For the
entire alphabet $S_d$, let

$$
\beta_d(\mu)=\sup_{n\ge1}\max_{\Theta}
 \left(\sum_{x\in C_\Theta}\prod_i\mu(x_i)\right)^{1/n},\qquad
b_d=\min_{\mu\in\Delta(S_d)}\beta_d(\mu)=2^{-\sigma_d},
\tag{GCB.35}
$$

where $\Theta$ ranges over every complete native template, including
arbitrary correlations, off-target donors, cycles, guards, repeated
seeds and compatibility zeros. The semantic equality and attained
minimum are credited [NPC, Theorems 5.3 and 6.2][GCBNPC]. Theorem
9.1 concerns a specified fixed law and per-template norm class. It
does not establish a separation after optimizing $\mu$, refute an
optimizer-cofinal grammar, give a new $M_1(D)$ or $\lambda$ bound,
or obstruct an effective error for the original $K_d(n)$.

The precise excluded premise is that optimal same-pair compensation
followed by this one direct SSSZ contraction has uniformly vanishing
normalized log error on every original native instance. A method that
requires that premise must replace the step, add a genuinely different
cyclic relation, or prove that a sufficient optimizing family avoids
these instances. No such optimizing-family theorem is assumed here.
The underlying SSSZ inequality remains sound.

The outstanding requirement is still a total computable finite verifier
accepting only caps valid for every length and every complete template,
with accepted endpoints optimizer-cofinal in the unchanged $\sigma_d$,
as in [NPC, Definition 8.1][GCBNPC]; alternatively, a uniform effective
length error yielding two-sided approximation of the original $\lambda$
would suffice. Arbitrary full nonnegative joint block weights must
remain owned once. Neither a per-input norm evaluation nor a different
exact incidence representation supplies that missing bridge.

The current credited endpoints, supplied by [NCE, Theorem 17.1 and
Corollary 17.2][GCBCURRENTNCE] and the credited D3 construction, are

$$
\frac18\log_2\frac{7792603}{3038031}\le\lambda<\frac3{16},\qquad
M_1(3)=4,\qquad M_1(6)\ge1874.
\tag{GCB.36}
$$

General exact memory, sharp rate, effective all-size convergence and
the minimal-relations/internal-observer mutual-recovery programme
remain open. Under the paid interface the recoverable information is
the requested temporal factor, equivalently its entire authentic-count
trajectory, from the acquired complete name and at most one actual
reply. No whole-source, unknown-age, hidden-history or physical
space-time recovery follows.

**Convention 11.4 (mathematical attribution).** The graphical inequality
and complete-bipartite norm convention are literature-attested:
Sah, Sawhney, Stoner and Zhao, *A reverse Sidorenko inequality*,
[arXiv:1809.09462v3, Theorem 1.12][GCBSSSZ], source labels
`thm:graph-BL` and `defn:graph-norm`. Its hypotheses are a triangle-free
graph, vertex measure spaces and nonnegative heterogeneous binary edge
functions, with $K_{d_v,d_u}$ on edge $uv$. This use requires no
hypergraph, source-loop or multigraph extension. Positivity and finiteness
of our two-point measures ensure every displayed integral is finite.

The native cycle, full-support law, trace identity and paid realization
are the credited GCB/COK suppliers identified above. Finite log-sum-exp
convexity and mixed finite differences are standard intermediates. The
complete compensation characterization, the convex symmetry optimum
and its exact $82/81$ residual are repository-derived ordinary
deductions in Sections 8--9. They carry no Lean certification,
worldwide-originality, exhaustive-literature or unrestricted
computability assertion. No finite common-extension, predecessor-row
controller or natural-join theorem is used to supply a missing native
acquisition or all-size pressure premise.

[GCBSSSZ]: https://arxiv.org/src/1809.09462v3
[GCBNPC]: https://github.com/the-omega-institute/trureturing/blob/3f89a8fc073a859012fba13e652362e5aebc16b8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[GCBCOK]: https://github.com/the-omega-institute/trureturing/blob/3f89a8fc073a859012fba13e652362e5aebc16b8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONDITIONAL_OWNER_KERNELS.md
[GCBRRN]: https://github.com/the-omega-institute/trureturing/blob/3f89a8fc073a859012fba13e652362e5aebc16b8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REPRESENTATIVE_REPLY_NORMAL_FORM.md
[GCBRCE]: https://github.com/the-omega-institute/trureturing/blob/3f89a8fc073a859012fba13e652362e5aebc16b8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RECURSIVE_CERTIFICATE_ESCAPE.md
[GCBGDB]: https://github.com/the-omega-institute/trureturing/blob/3f89a8fc073a859012fba13e652362e5aebc16b8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GLOBAL_DEPENDENCE_BOUNDARIES.md
[GCBCURRENTNCE]: https://github.com/the-omega-institute/trureturing/blob/3f89a8fc073a859012fba13e652362e5aebc16b8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md

## 追加锚（本行以下为增补区）

---
bibkey: fiolmartinezmontoyariosfukelman2020quiver
authors: B. Fiol; J. Martínez-Montoya; A. Rios Fukelman
year: 2020
title: "The planar limit of N=2 superconformal quiver theories"
doi: 10.1007/JHEP08(2020)161
url: https://arxiv.org/abs/2006.06379v2
claim: "Section 2.2, Conjecture 1 asserts that tree Ising polynomials with arbitrary positive configuration weights have all their x roots on the unit circle."
strata_touched:
  - D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/JHEP08(2020)161

Source: https://arxiv.org/abs/2006.06379v2

## Tree construction

Section 2.2, printed page 13 (PDF page 14), states:

> Take the graph G to be a tree T,
>
> 1. Assign a positive integer $n_i$ to each of the $e$ edges of the tree graph.
> 2. For every edge, split $n_i$ into two positive integers, $n_i=k_i+(n_i-k_i)$ and assign each of these two integers to one of the vertices at the ends of that edge.
> 3. Then, if a vertex has degree $d_j$ this procedure assigns to that vertex $d_j$ integers. Let $m_j$ be the sum of these integers at a given vertex; the magnetic field at that vertex is then $m_j H$.

Equation (2.30) is

$$
P(\tau,x,n_1,\dots,n_e)=
\sum_{k_1=1}^{n_1-1}\cdots\sum_{k_e=1}^{n_e-1}
\rho(k_i,n_i)\sum_{\text{all states}}
\tau^{e_\pm}\prod_{\text{vertices with spin up}}x^{m_j}.
$$

The accompanying sentence is:

> where $\rho(k_i,n_i)$ is a distribution that weights different configurations.

Here $e_\pm$ counts edges joining opposite spins. Equation (2.31) specifies
physical weights through binomial factors and the vertex factors $\mathcal V_i$.

## Conjecture 1

Section 2.2, printed page 14 (PDF page 15), states:

> Conjecture 1: For any tree with $e$ edges, any fixed positive integers $n_1,\dots,n_e$ and arbitrary $\rho(k_i,n_i)>0$ the polynomials $P(\tau,x,n_1,\dots,n_e)$ have all their $x$ roots on the unit circle.

The one-edge case, equations (2.32)–(2.33), is proved for $|\tau|\le1$
and arbitrary positive $\rho(n,k)$ through the palindromic-polynomial theorem
of Lakatos and Losonczi cited as reference [30].

## Formal scope

Issue [#15357](https://github.com/the-omega-institute/trureturing/issues/15357)
fixes the encoding: finite vertex and edge types, an injective list of undirected
edges whose graph is a tree, and an orientation recording which endpoint receives
$k_i$. The split sum uses $1\le k_i\le n_i-1$ with $n_i\ge2$, excluding
the empty-sum case $n_i=1$. Spins are Boolean, spin up is `true`, the coefficients
are real, and $\tau\in[-1,1]$. The weight is an arbitrary positive joint
function of the entire split configuration.

The repository refutation uses the three-vertex path oriented $0\to1\leftarrow2$,
$n=(4,4)$, $\tau=-1$, and the positive joint weight matrix
$W_{31}=\begin{pmatrix}1&1&1\\1&10&1\\1&1&31\end{pmatrix}$.
The vertex masses are $(k_1,8-k_1-k_2,k_2)$ on the allowed splits.
The same polynomial arises from $0\to1\to2$ with the second weight index reversed.
The kernel-checked settling result concerns this arbitrary-joint-weight scope.
The product-weight and physical-weight versions remain open.

## Physical split and assignment-summed boundary arguments

The following arguments concern the [tree Lee–Yang problem](../../Problems/fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang.md). They are repository derivations with the assumptions and unresolved boundaries stated below, rather than results attributed to the source paper. They remain prose evidence and introduce no kernel-checked declarations.

<a id="lee-yang-split"></a>

### Uniform raw split real-stability obstruction

The physical specialization has a uniform obstruction to one tempting
intermediate route. This is a statement about the raw split generating
polynomial, not about the Lee--Yang state sum. Keep $a,b\ge3$ fixed, put
$N=a+b$, and use the leaf-oriented incidence $0\to1\leftarrow2$ (equivalently,
reverse both printed arrows when reading the source convention). Set

$$
f(t)=\frac{(2t)!}{(t-1)!\,t!},\qquad
U_n(j)=\binom nj\binom n{j+1}.
$$

The source's (2.15) gives
$\mathcal V(t_1,\ldots,t_\alpha)=\frac{(d-1)!}{(d-\alpha+2)!}
\prod_i f(t_i)$, where $d=\sum_i t_i$. Thus the two leaves contribute
$f(k)/(k(k+1))$ and $f(\ell)/(\ell(\ell+1))$, while the degree-two
centre contributes $f(a-k)f(b-\ell)/(N-k-\ell)$. Including all three
vertex factors, as required by the physical product in (2.31), gives

$$
\rho_{k\ell}=\binom{2a}{2k}\binom{2b}{2\ell}
 \frac{f(k)}{k(k+1)}
 \frac{f(a-k)f(b-\ell)}{N-k-\ell}
 \frac{f(\ell)}{\ell(\ell+1)}.
$$

For every $1\le j<n$ the factorial cancellation is exact:

$$
\binom{2n}{2j}\frac{f(j)f(n-j)}{j(j+1)}
 =\binom{2n}{n}\binom nj\binom n{j+1}.
$$

Indeed, after cancelling $(2j)!$ and $(2n-2j)!$, use
$j!=j(j-1)!$ and $(j+1)!=(j+1)j!$; every factorial argument is
nonnegative on the displayed split range. Consequently

$$
\rho_{k\ell}=C_{ab}\,w_{k\ell},\qquad
C_{ab}=\binom{2a}{a}\binom{2b}{b}>0,\qquad
w_{k\ell}=\frac{U_a(k)U_b(\ell)}{N-k-\ell}.
$$

This is the source echo and scalar bridge; it does not replace the state
sum in (2.30). Define only the raw split polynomial

$$
K_{a,b}(u,v)=\sum_{k=1}^{a-1}\sum_{\ell=1}^{b-1}
 w_{k\ell}u^{k-1}v^{\ell-1}.
$$

At $\tau=-1$, the eight-state sum for a fixed split is
$(1-X^k)(1+X^{N-k-\ell})(1-X^\ell)$, so the physical polynomial is

$$
P^{\mathrm{ph}}_{a,b}(-1,X)=C_{ab}\sum_{k=1}^{a-1}\sum_{\ell=1}^{b-1}
w_{k\ell}(1-X^k)(1+X^{N-k-\ell})(1-X^\ell).
$$

The following calculation concerns $K_{a,b}$ only.

It has bidegree $(a-2,b-2)$. Apply
$\partial_u^{a-3}\partial_v^{b-3}$. Only
$k\in\{a-2,a-1\}$ and $\ell\in\{b-2,b-1\}$ survive. Writing

$$
A_n=U_n(n-2)=\frac{n^2(n-1)}2,\qquad B_n=U_n(n-1)=n,
$$

the four undifferentiated corner coefficients are

$$
\begin{pmatrix}
A_aA_b/4 & A_aB_b/3\\[2pt]
B_aA_b/3 & B_aB_b/2
\end{pmatrix};
$$

the denominators $4,3,3,2$ are respectively
$N-(a-2)-(b-2)$, $N-(a-2)-(b-1)$,
$N-(a-1)-(b-2)$, and $N-(a-1)-(b-1)$. Including the derivative
factors and dividing by the positive scalar
$(a-3)!(b-3)!A_aA_b/4$ gives exactly

$$
1+c_a u+c_b v+\frac98c_ac_buv,
\qquad
c_a=\frac{8(a-2)}{3a(a-1)},\quad
c_b=\frac{8(b-2)}{3b(b-1)}.
$$

Both $c_a$ and $c_b$ are strictly positive, including the corner case
$a=b=3$ (where no differentiation is taken). This calculation checks the
degree, all four central denominators, and every factorial scalar.

The closure step uses Borcea--Brändén--Liggett, *Negative Dependence and
the Geometry of Polynomials*, [arXiv:0707.2340](https://ar5iv.labs.arxiv.org/html/0707.2340), Proposition 3.1(2): a
partial derivative of a real-stable polynomial is real-stable or zero,
and positive coordinate scaling preserves real stability. The derivative
above is nonzero because its $uv$ coefficient is positive. After the
positive rescaling $x=c_au$, $y=c_bv$, a real-stable $K_{a,b}$ would force

$$
G(x,y)=1+x+y+\frac98xy
$$

to be real-stable. But the exact bilinear zero

$$
x=i,\qquad
y=-\frac{1+i}{1+9i/8}=-\frac{136}{145}+\frac{8}{145}i
$$

has both coordinates in the open upper half-plane and satisfies
$G(x,y)=0$. Thus $G$, the differentiated polynomial, and $K_{a,b}$ are
all non-stable. Multiplication by the positive physical scalar $C_{ab}$
does not change this conclusion. The same paper's Theorem 4.1 gives the
corresponding bilinear real-stability criterion; the displayed zero is a
direct witness, so no sign convention from that criterion is being used
implicitly here.

The mechanism is the degree-two central factor. In a $2\times2$ corner,
dividing the stable product coefficients by the successive central
degrees produces $1/M,1/(M-1),1/(M-1),1/(M-2)$, whose bilinear minor is

$$
\frac1{(M-1)^2}-\frac1{M(M-2)}
=-\frac1{M(M-2)(M-1)^2}<0\qquad(M\ge4).
$$

This rules out the raw split-real-stability lemma as a route for every
interior pair $a,b\ge3$. It does not produce a zero of
$P^{\mathrm{ph}}_{a,b}(-1,X)$ off the unit circle: that polynomial still
contains the three spin factors from (2.30); the scalar bridge only
relates the weights without identifying the two zero sets. The physical
two-edge Lee--Yang question for $a,b\ge3$, the full tree problem, other
$\tau$, general assignment sums, and Conjecture 2 therefore remain open. This is
source-grounded prose only, with no new Lean declaration, kernel claim,
or literature-priority assertion; alternative disk-specific or
interlacing routes remain available.

<a id="lee-yang-coefficient"></a>

### One fixed tree's assignment-summed formal coefficient

The following is a complete analytical calculation at $\tau=-1$, assessed
directly against the source and checked independently by hand. It is not a
new Lean theorem. The inherited frozen `QuiverTreeIsingRefutation.result`
concerns arbitrary positive joint split weights on a different, three-vertex
example. Its kernel verification does not extend to the calculation below.

Let $T$ have a unique degree-two centre $c$, two hubs $h_1,h_2$ adjacent to
$c$, and sixty leaves adjacent to each hub. Each hub has degree $61$;
$T$ has $123$ vertices, $122$ edges and $122$ odd-degree vertices. Replace
each occurrence of $\zeta(2n-1)$ in (2.19) by an independent commuting
formal generator $Z_{2n-1}$. Write $F_{0,T}$ for only this fixed unlabelled
tree's summand in (2.19). No algebraic independence of numerical odd zeta
values is assumed. The coefficient considered here assigns total three to
two edges and total two to the other $120$ edges.

For $X=\widetilde\lambda_2/\widetilde\lambda_1$ with
$\widetilde\lambda_1\ne0$, the result is

$$
[Z_5^2 Z_3^{120}]F_{0,T}
=200\,12^{120}\widetilde\lambda_1^{246}(1-X)^{122}Q(X),
$$

where, with $S_r=\sum_{j=0}^{r-1}X^j$,
$U=S_{61}$, $V=S_{62}$, $W=S_{63}$, $L=1+X$ and $H_r=1+X^r$,

$$
\begin{aligned}
Q={}&H_2(27691682V^2+20763180UW+1771440LUV+14280L^2U^2)\\
&+H_3(59048UV+960LU^2)+9H_4U^2.
\end{aligned}
$$

The polynomial $Q$ has degree $124$ and $124$ distinct simple roots, all on
the unit circle and none equal to $1$ or $-1$. Thus
$P=(1-X)^{122}Q$ has degree $246$, with $125$ distinct roots: $1$ has
multiplicity exactly $122$, and the other $124$ roots are simple. Its
constant and leading coefficients are both $50300599$. Homogenization
therefore adds no projective root at infinity, and zero is not a root.
These statements concern this one tree's contribution, this formal
monomial and this parameter; other trees also contribute to the same
formal coefficient of the full free energy.

**Source convention and interpretation.** Equation (2.19) explicitly
includes all $m+1$ vertices of an $m$-edge tree. Its vertex correlator is

$$
\mathcal V(t_1,\ldots,t_d)
=\frac{(M-1)!}{(M-d+2)!}\prod_j f(t_j),\qquad
f(t)=\frac{(2t)!}{(t-1)!t!},\qquad M=\sum_jt_j.
$$

The modified factor is
$\mathcal V(\widetilde\lambda_1^M+(-1)^d\widetilde\lambda_2^M)$.
Identifying this calculation with the Ising weight displayed in (2.31)
uses the editorial all-vertex reading: that display prints the upper
vertex-product index $m$, whereas the construction and (2.16)--(2.19)
include $m+1$ factors. No author-approved correction or established
erratum is asserted. The inspected arXiv record lists v2 as the latest
revision, and the inspected INSPIRE and Crossref records display no
related correction; this bounded observation does not determine authorial
intent or exclude a correction elsewhere. Equation numbers here follow
the PDF; the HTML labels are shifted.

The predecessor, Fiol--Martínez-Montoya--Rios Fukelman,
*The planar limit of N=2 superconformal field theories*,
[arXiv:2003.02879v3](https://arxiv.org/abs/2003.02879v3), Section 2.3
around (44)--(46), explains complementary-split orientation invariance
after the split sums and the edge-labelling factor $m!/|\operatorname{Aut}T|$
after the total sums. Individual correlator products before these sums
need not agree. The present assignment sum uses that distinction.

**All assignments and their automorphisms.** An assignment is a
two-element subset $A$ of the $122$ named edges, so there are
$\binom{122}{2}=7381$ assignments. The unique centre forces every
automorphism to interchange or fix the hubs and to permute their leaves;
thus $|\operatorname{Aut}T|=2(60!)^2$. Both selected edges are central,
exactly one is central, or neither is central. In the second case the
pendant lies at the same or opposite hub; in the third case the pendants
lie at the same or opposite hubs. This gives an exhaustive disjoint
partition:

| Placement of the two total-three edges | Multiplicity | Stabilizer order |
| --- | ---: | --- |
| Both central edges | $1$ | $2(60!)^2$ |
| Central edge and same-hub pendant | $2\cdot60=120$ | $60!59!$ |
| Central edge and opposite-hub pendant | $2\cdot60=120$ | $60!59!$ |
| Two same-hub pendants | $2\binom{60}{2}=3540$ | $2\cdot60!58!$ |
| Two opposite-hub pendants | $60^2=3600$ | $2(59!)^2$ |

Their multiplicities sum to $7381$. Each orbit contributes
$|O|/|\operatorname{Aut}T|=1/|\operatorname{Stab}A|$ times its
representative. Equal weighting of the five representatives would be
incorrect. Each ordered tuple of totals with two threes occurs once;
$122!/(2!120!)=7381$ already counts it. There is no additional factorial
or orbit divisor: the source's original $1/m!$ has already cancelled the
edge-labelling factor.

**Exact physical weights and spin sum.** For any up-spin vertex set $B$,
$\sum_{v\in B}\deg v=2|E(B)|+|\partial B|$. Consequently the complete
spin sum at $\tau=-1$ is

$$
\sum_{B\subseteq V(T)}(-1)^{|\partial B|}X^{\sum_{v\in B}M_v}
=\prod_v(1+(-1)^{\deg v}X^{M_v}).
$$

This retains every state and every edge sign. A total-two edge has only
the split $(1,1)$ and contributes $\binom42 f(1)^2=24$, since $f(1)=2$.
A total-three edge has the two endpoint allocations $(1,2),(2,1)$;
each contributes $\binom62 f(1)f(2)=360$, since $f(2)=12$.
Hence each assignment has exactly four allocations, each selected edge
adding one unit to one endpoint, including when that endpoint is a leaf.

Write $M_v=d_v+r_v$. The residual vertex factorial factor and its ratio
to the all-one endpoint baseline are

$$
f_d(r)=\frac{(d+r-1)!}{(r+2)!},\qquad
a_d(0)=1,\quad a_d(1)=\frac d3,\quad
a_d(2)=\frac{d(d+1)}{12}.
$$

Thus $a_2(1)=2/3$, $a_2(2)=1/2$, $a_{61}(1)=61/3$,
$a_{61}(2)=1891/6$ and $a_1(1)=1/3$; a leaf cannot receive two
increments here. The baseline product is $(60!)^2/2^{123}$, and

$$
\frac{(60!)^2}{2^{123}}24^{120}360^2
=16200(60!)^2 12^{120}=18C_0,\qquad
C_0=900(60!)^2 12^{120}.
$$

The endpoint changes are already in the two factors $360$ and must not be
inserted again in $a_d(r)$. Every mass is positive, so the $122$
odd-degree vertices each supply $(1-X)S_{M_v}$. The centre supplies
$H_{2+r_c}$. The factor $(1-X)^{122}$ is common even when a selected
pendant gives a leaf mass two.

After division by $C_0$ the seven allocation weights are: different
hubs, $18(61/3)^2=7442$; centre and hub,
$18(2/3)(61/3)=244$; twice centre, $18(1/2)=9$; twice one hub,
$18(1891/6)=5673$; hub and leaf, $18(61/3)(1/3)=122$; centre and
leaf, $18(2/3)(1/3)=4$; two distinct leaves, $18(1/3)^2=2$.

For each assignment let $P_A$ be the full split- and spin-summed physical
polynomial before the external source factors, and set
$P_A=C_0(1-X)^{122}q_A$. The five orbit polynomials are exactly

$$
\begin{aligned}
q_{CC}={}&7442H_2V^2+488H_3UV+9H_4U^2,\\
q_{CS}={}&5673H_2UW+122H_2LUV+244H_3UV+4H_3LU^2,\\
q_{CO}={}&7442H_2V^2+122H_2LUV+244H_3UV+4H_3LU^2,\\
q_{SS}={}&5673H_2UW+244H_2LUV+2H_2L^2U^2,\\
q_{SO}={}&7442H_2V^2+244H_2LUV+2H_2L^2U^2.
\end{aligned}
$$

For $CC$ the four allocations are the two hubs, centre and hub in two
ways, and twice centre. For $CS$ they are twice the common hub, hub and
leaf, centre and hub, and centre and leaf. For $CO$ they are both hubs,
central-edge hub and opposite leaf, centre and opposite hub, and centre
and leaf. For $SS$ they are twice the common hub, hub and leaf in two
ways, and both leaves. For $SO$ they are both hubs, hub and the other
leaf in two ways, and both leaves. In particular the same-hub double
increment uses $a_{61}(2)$, not $a_{61}(1)^2$.

Now $Q=q_{CC}+120q_{CS}+120q_{CO}+3540q_{SS}+3600q_{SO}$.
Every aggregate multiplier follows from the orbit counts:

$$
\begin{aligned}
[H_2V^2]:&\quad7442(1+120+3600)=27691682,\\
[H_2UW]:&\quad5673(120+3540)=20763180,\\
[H_2LUV]:&\quad122(120+120)+244(3540+3600)=1771440,\\
[H_2L^2U^2]:&\quad2(3540+3600)=14280,\\
[H_3UV]:&\quad488+244(120+120)=59048,\\
[H_3LU^2]:&\quad4(120+120)=960,\\
[H_4U^2]:&\quad9.
\end{aligned}
$$

The bracket labels in this display identify the displayed product terms,
not an assertion that these seven polynomials form an independent basis.

**Source prefactor.** Here $m=122$, $\sum_e n_e=246$ and
$\prod_e n_e=9\cdot2^{120}$. Equation (2.19) supplies

$$
\frac{(-2)^{122}(-1)^{246}}{9\cdot2^{120}|\operatorname{Aut}T|}
=\frac4{9|\operatorname{Aut}T|}.
$$

Multiplication by $C_0$ and $|\operatorname{Aut}T|=2(60!)^2$ gives
exactly $200\,12^{120}$. Also $\sum_v M_v=\sum_e n_e=246$,
so all vertex couplings together supply
$\widetilde\lambda_1^{246}$. This proves the stated homogeneous
coefficient identity, with no omitted scalar or vertex factor.

**Every monomial coefficient.** Put $q_k=[X^k]Q$, with $q_k=0$ outside
$0\le k\le124$. The complete coefficient list is specified by reflection
$q_{124-k}=q_k$ and

$$
\begin{gathered}
q_0=50300599,\qquad q_1=102402158,\qquad q_2=204758579,\\
q_k=104231678k-3720026\quad(3\le k\le60),\\
q_{61}=6331788166,\qquad q_{62}=6354351346.
\end{gathered}
$$

For $k\le60$ each underlying convolution $S_aS_b$ has coefficient $k+1$.
Let $K=27691682+20763180=48454862$. The small factors are $H_2$,
$H_2L=1+X+X^2+X^3$,
$H_2L^2=1+2X+2X^2+2X^3+X^4$, $H_3$,
$H_3L=1+X+X^3+X^4$ and $H_4$. For $3\le k\le60$ their convolution gives

$$
2Kk+1771440(4k-2)+14280(8k-8)+59048(2k-1)
+960(4k-4)+9(2k-2)=104231678k-3720026.
$$

At $k=61$ the finite lengths subtract
$20763180+1771440+2\cdot14280+59048+2\cdot960+2\cdot9=22624166$
from that linear formula; at $k=62$ they subtract
$2\cdot27691682+2\cdot20763180+4\cdot1771440+8\cdot14280+
3\cdot59048+6\cdot960+4\cdot9=104292664$.
The first three coefficients follow by the short initial convolutions;
reflection gives all remaining coefficients. The exact evaluations are
$Q(1)=400163878746$, $Q(-1)=41526378$ and $Q(i)=120034$.
Every coefficient of the degree-$246$ normalized polynomial is consequently

$$
[X^k]P=\sum_{j=0}^{122}(-1)^j\binom{122}{j}q_{k-j}.
$$

This is an exact product identity, not numerical root evidence.

**Complete root proof.** Each $S_r$ is real reciprocal of degree $r-1$,
$L$ of degree one and $H_r$ of degree $r$. Every displayed product term
of $Q$ has degree $124$. Their positive multipliers sum to $50300599$,
so $Q$ is nonzero of exact degree $124$, with that constant and leading
coefficient, and $Q(X)=X^{124}Q(1/X)$. Set

$$
F(\theta)=e^{-62i\theta}Q(e^{i\theta}),\qquad0\le\theta\le\pi.
$$

Reciprocity and real coefficients give
$\overline{F(\theta)}=e^{62i\theta}Q(e^{-i\theta})=F(\theta)$.
Thus $F$ is real and continuous; its zeros correspond exactly to roots
of $Q$ at $e^{i\theta}$.

For $a_j=2\pi j/61$, $1\le j\le30$, put $X=e^{ia_j}$.
Then $X^{61}=1$, $X\ne1$, $U=0$ and $V=1$. Only the first term survives,
and $X^{-62}=X^{-1}$ gives

$$
F(a_j)=27691682(X+X^{-1})=55383364\cos a_j.
$$

This is strictly positive for $j=1,\ldots,15$ and strictly negative for
$j=16,\ldots,30$; none of these points equals $\pi/2$.

For $b_j=\pi j/31$, $1\le j\le31$, put $X=e^{ib_j}$ and
$t=X+X^{-1}=2\cos b_j$. Now $X^{62}=1$, $X\ne1$, $V=0$,
$U=-X^{-1}$, $W=1$ and $X^{-62}=1$. The four surviving contributions are

$$
-20763180t,\qquad14280t(t+2),\qquad960(t^2+t-2),\qquad9(t^2-2),
$$

so $F(b_j)=15249t^2-20733660t-1938$. In particular the $H_3LU^2$
and $H_4U^2$ terms are retained. For $1\le j\le15$, $0<t\le2$, whence

$$
F(b_j)\le(30498-20733660)t-1938<0.
$$

For $16\le j\le31$, monotonicity of cosine gives
$t\le-2\sin(\pi/62)$. Concavity of sine on $[0,\pi/2]$ gives
$\sin u\ge2u/\pi$, hence $t\le-2/31$. The quadratic term is nonnegative,
so

$$
F(b_j)\ge\frac{41467320}{31}-1938
=\frac{41407242}{31}>0.
$$

At $b_{31}=\pi$ the exact value is $F(\pi)=Q(-1)=41526378$.
The extra midpoint is also explicit: at $X=i$, $U=1$,
$V=L=1+i$, $H_2=0$, $H_3=1-i$ and $H_4=2$. Therefore
$Q(i)=2(59048+960)+18=120034$, and $i^{-62}=-1$ gives
$F(\pi/2)=-120034<0$. Finally $F(0)=Q(1)=400163878746>0$.
Use the polynomial $Q$ itself at zero angle, so no denominator $1-X$
creates a singular endpoint.

For $1\le j\le30$,
$b_j<a_j<b_{j+1}$: the second inequality is equivalent to
$62j<61(j+1)$, which holds since $j<61$.
Also $a_{15}=30\pi/61<\pi/2<b_{16}=16\pi/31$. Thus

$$
0,b_1,a_1,\ldots,b_{15},a_{15},\pi/2,
b_{16},a_{16},\ldots,b_{30},a_{30},b_{31}=\pi
$$

is a strictly ordered list of $1+31+30+1=63$ points with strictly
alternating signs. The additional midpoint is essential: the two grids
alone do not provide $62$ sign changes. The intermediate value theorem
gives a root in each of the $62$ disjoint open intervals. Exponentiation
is injective on $(0,\pi)$, so these are $62$ distinct roots of $Q$ in
the open upper semicircle. Real coefficients give $62$ distinct conjugate
roots in the open lower semicircle, disjoint from the first set. A
nonzero degree-$124$ polynomial has at most $124$ distinct complex roots;
these exhaust its degree and each is simple. There is no additional,
off-circle, real-axis or repeated root. The nonzero endpoint evaluations
also directly exclude $1$ and $-1$. Since $Q(1)>0$,
$(1-X)^{122}$ adds exactly a root of multiplicity $122$ at $1$;
the nonzero source scalar changes no roots or multiplicities.

**Different fixed-labelled target and admission boundary.** The original
fixed-labelled physical candidate in
[issue #17677](https://github.com/the-omega-institute/trureturing/issues/17677)
places the two threes on the two central edges. Its exact target is the
universal fixed-assignment assertion `claimPhys`: every finite tree with
at least two edges, every fixed assignment of totals at least two, all
physical factorial factors and $\tau=-1$. Its proposed conclusion is
`result : Not claimPhys`. Its polynomial is
$C_0(1-X)^{122}q_{CC}$, not $C_0(1-X)^{122}Q$.
The four split weights there are $C_0(9,244,244,7442)$.

For completeness, its retained analytical obstruction uses, on $|z|=1$,
$a=1-z^{62}$, $b=1-z^{61}$, $c=\operatorname{Re}z$,
$K=(z+\bar z^2)/2$, $h=7442c$ and $d=9(2c^2-1)$:

$$
\begin{gathered}
(1-z)^2q_{CC}(z)=-2z^{63}E,\quad
E=h|a|^2+488\operatorname{Re}(a\bar bK)+d|b|^2,\\
hE=|ha+244\bar Kb|^2+(hd-244^2|K|^2)|b|^2,\\
hd-244^2|K|^2=7442(2c^3+3c-4)>0\quad(c\ge9/10).
\end{gathered}
$$

A root on this arc would force $a=b=0$ and then $z=1$, excluded by
$q_{CC}(1)=60972306$. If all roots were unit roots, counting them with
multiplicity and setting $v=\sum_r(1-r)^{-1}$,
$w=\sum_r(1-r)^{-2}$ gives $q_{CC}'(1)=q_{CC}(1)v$ and
$q_{CC}''(1)=q_{CC}(1)(v^2-w)$. The exact derivative is
$q_{CC}'(1)=3780282972=62q_{CC}(1)$. The excluded arc and
$\operatorname{Re}((1-r)^{-1}-(1-r)^{-2})=1/(2(1-\operatorname{Re}r))<5$
give the non-strict bound $\operatorname{Re}(v-w)\le620$, using
$\deg q_{CC}\le124$. Hence $\operatorname{Re}w\ge-558$ and
$q_{CC}''(1)\le4402q_{CC}(1)$, contrary to
$q_{CC}''(1)=269676602388$ and
$q_{CC}''(1)-4402q_{CC}(1)=1276511376>0$.
This source-assessed fixed-assignment argument has no new current kernel
theorem of its own. The non-strict multiset bound covers an empty multiset.
An unguarded generic strict variant fails at degree zero; its unused proposed
$n\ge1$, degree-$2n$ correction is not an accepted general theorem. The exact
universal physical claim is settled separately by the all-total-three e8 Lean
result above; this m60 calculation remains prose and does not change that
result's admission or scope.

Identifying the preregistered fixed-labelled assertion with a tree's
assignment-summed contribution in the source prose is a separate question.
The positive coefficient example and its analytical proof supply no new
admission basis and do not settle the source's general assignment-summed
physical conjecture. The earlier bind-only disposition for the two-edge
boundary formalization is unchanged. This m60 exposition supplies no new
declaration, proof-shape classification, escape witness, registration, freeze
or open-problem-resolution admission.

The fixed-labelled obstruction and the positive aggregate are compatible
because they concern different polynomials. One placement is not the whole
formal coefficient, and a positive aggregate does not establish the universal
fixed-labelled assertion for this 123-vertex calculation. Other multisets,
other trees, other $\tau$, the full coupling series, sums over trees
(Conjecture 2) and the conditional Wilson-loop questions remain unresolved
here. The general assignment-summed physical tree conjecture remains open; no
literature-priority or broader universal-conjecture resolution is claimed.

[Return to the problem dossier](../../Problems/fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang.md).

# Fiedler optimization on labelled K₃,ₘ at fixed total resistance

## 1. Conductances, counting measure and cited inputs

**Definition 1.1 (The independent conductance domain).** For each integer $m\ge3$,
put $n=m+3$. The labelled graph $K_{3,m}$ has hubs $a_1,a_2,a_3$, leaves
$x_1,\ldots,x_m$, and exactly the edges $\{a_a,x_i\}$, with
$1\le a\le3$ and $1\le i\le m$. Its conductances range independently over

$$
c=(c_{ai})\in(0,\infty)^{3m}.
$$

Write

$$
d_a=\sum_{i=1}^m c_{ai},\qquad
s_i=\sum_{a=1}^3 c_{ai},\qquad
W=\sum_{a,i}c_{ai},\qquad C=(c_{ai}).
$$

The Laplacian and inner product are

$$
L=\begin{pmatrix}
\operatorname{diag}(d_1,d_2,d_3)&-C\\
-C^{\mathsf T}&\operatorname{diag}(s_1,\ldots,s_m)
\end{pmatrix},\qquad
\langle z,y\rangle=\sum_{v\in V}z_vy_v.
$$

Thus vertex measure is counting measure. Its eigenvalues, with multiplicities,
are $0=\lambda_1<\lambda_2\le\cdots\le\lambda_n$. For distinct vertices
$p,q$, let $h_p=1$, $h_q=0$ and $(Lh)_v=0$ for $v\notin\{p,q\}$.
Define

$$
r(p,q)=\frac1{(Lh)_p},\qquad
R(c)=\sum_{\{p,q\}\subseteq V,\ p\ne q}r(p,q).
$$

Every unordered pair occurs once, including pairs which are not edges.
The optimization domain imposes neither symmetry nor a value of $W$.

The following classical identities fix the normalization used below:

$$
r(p,q)=(e_p-e_q)^{\mathsf T}L^+(e_p-e_q),\qquad
R(c)=n\operatorname{tr}L^+=n\sum_{j=2}^n\lambda_j^{-1}.
\tag{1.1}
$$

Here $L^+$ is inverse to $L$ on $\mathbf1^\perp$ and zero on
$\mathbb R\mathbf1$. To check these identities directly, the energy formula

$$
z^{\mathsf T}Lz=\sum_{a,i}c_{ai}(z_{a_a}-z_{x_i})^2
\tag{1.2}
$$

shows that $\ker L=\mathbb R\mathbf1$, because the graph is connected and
every conductance is positive. The Dirichlet matrix obtained by fixing the
two boundary values is positive definite: a zero-energy vector with zero
boundary values must be constant and hence zero. Consequently the harmonic
extension exists uniquely. If $I=(Lh)_p$, then

$$
Lh=I(e_p-e_q),\qquad I=h^{\mathsf T}Lh>0.
$$

Applying $L^+$ and taking the difference of the $p,q$ coordinates proves
the first identity in (1.1). Finally,

$$
\sum_{\{p,q\}\subseteq V,\ p\ne q}
(e_p-e_q)(e_p-e_q)^{\mathsf T}=nI-\mathbf1\mathbf1^{\mathsf T}.
$$

Taking its product with $L^+$ and then the trace proves the second identity.
In particular, for every $u>0$,

$$
L(uc)=uL(c),\qquad \lambda_2(uc)=u\lambda_2(c),\qquad
R(uc)=R(c)/u.
\tag{1.3}
$$

**Convention 1.2 (Sources and their mathematical scope).** The harmonic,
Laplacian and unordered-pair conventions are those of Cruz Ortega and
Menéndez-Conde, [*Maximal Algebraic Connectivity for Paths with Fixed Effective
Resistance*, arXiv:2306.08187v1](https://arxiv.org/pdf/2306.08187v1),
§§2–4. Section 5, equation (3), asks for maximal algebraic connectivity at
fixed total resistance, and the following paragraph observes the equivalent
scale-invariant product problem. Its explicit optimizers concern paths
$P_3$ and $P_4$. Formula (1.1) includes the factor $n$ in its displayed
spectral formula, irrespective of the subsequent description of that formula
as a trace.

For (1.1), the primary identity supplier is Ghosh–Boyd–Saberi,
[*Minimizing Effective Resistance of a Graph*, SIAM Review 50(1), 37–66,
DOI:10.1137/050645452](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf),
§2.4, equation (8), and §2.5, equations (13)–(15). Their $G$ is our $L$,
their edge conductances $g$ are our $c_{ai}$, and their $R_{\rm tot}$ is our
$R$. Their optimization (2) minimizes $R_{\rm tot}$ under
$\mathbf1^{\mathsf T}g=1$ and $g\ge0$.

Rosa–Harman, [*Laplacian Network Optimization via Information Functions*,
arXiv:2512.19279v1](https://arxiv.org/pdf/2512.19279v1), §§2.3–5, use
$\Phi_A=(n-1)/(\operatorname{tr}L^+) = n(n-1)/R$ and
$\Phi_E=\lambda_2$ in the present increasing eigenvalue convention. Thus
$\lambda_2R=n(n-1)\Phi_E/\Phi_A$. Their network problem (1) selects a
prescribed number of edges with given edge weights; their approximate-design
relaxation uses a linear allocation constraint. These give the A/E-design
interpretation, rather than an optimizer for the resistance level set here.

The [two-hub theorem](FIEDLER_RESISTANCE_K2M_OPTIMIZER.md), §§2–3, supplies
the complete optimizer for $K_{2,m}$; its §4, Problem 4.1, poses the
three-hub problem considered here. The [labelled $K_{2,3}$ refutation](../../../Blueprint/D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.md)
supplies a feasible asymmetric two-hub weighting and its comparison with
invariant weights. Its underlying private calculations also have exactly
two hubs and three leaves. Neither two-hub result is used as a theorem with
three hubs. The path and cycle optimization results in the neighbouring
volumes likewise concern their stated graph classes.

The institutional [Menéndez-Conde follow-up](https://repository.uaeh.edu.mx/revistas/index.php/icbi/article/view/16817)
is identified at the abstract and metadata level as concerning complete
graphs. Its complete article and theorem hypotheses are outside the
source access used here; no theorem of that article is invoked. The three
primary texts cited above are used at the explicitly indicated statements.
The second-excess estimate, its strict global comparison and the labelled
rigidity in §§2–3 are repo-derived deductions proved below. The cited
identities and A/E correspondence are intermediate inputs to those deductions.

## 2. A global comparison for every independent edge weight

**Lemma 2.1 (Spectral excess forced by three hubs).** For any conductances
in Definition 1.1, set

$$
t=\lambda_2(L),\qquad w=W/t,\qquad
P=I-\frac1n\mathbf1\mathbf1^{\mathsf T},\qquad
H=L/t-P.
$$

The matrix $H$ is positive semidefinite, $H\mathbf1=0$, and

$$
w\ge m,\qquad S:=\operatorname{tr}H=2w-m-2.
\tag{2.1}
$$

If $E$ denotes the second elementary symmetric sum of its eigenvalues, then

$$
E\ge\frac{2(w-3)}m.
\tag{2.2}
$$

If equality holds in (2.2), two of the normalized hub degrees $d_a/t$
are $1$, and the remaining one is $w-2$.

*Proof.* All positive eigenvalues of $L/t$ are at least $1$, while $P$ is
identity on $\mathbf1^\perp$ and zero on constants. This proves the two
matrix assertions. For the leaf-difference subspace

$$
U=\{z:z_{a_1}=z_{a_2}=z_{a_3}=0,\ \sum_i z_{x_i}=0\},
$$

choose an orthonormal basis $f_1,\ldots,f_{m-1}$. Its projection on leaf
coordinates is $I_m-\mathbf1_m\mathbf1_m^{\mathsf T}/m$, so

$$
m-1\le\sum_{k=1}^{m-1}f_k^{\mathsf T}(L/t)f_k
=\frac{m-1}{m}\sum_i\frac{s_i}{t}
=\frac{m-1}{m}w.
\tag{2.3}
$$

This uses Rayleigh's lower bound, with no invariance assumption on $U$.
It gives $w\ge m$. Also $\operatorname{tr}L=2W$ and
$\operatorname{tr}P=n-1=m+2$, proving (2.1).

Write $\delta_a=d_a/t$ and let $A$ be the $3\times3$ principal hub
submatrix of $H$. Distinct hubs are nonadjacent, so

$$
A=\operatorname{diag}(z_1,z_2,z_3)+\frac1n\mathbf1_3\mathbf1_3^{\mathsf T},
\qquad z_a=\delta_a-1,\qquad \sum_a z_a=w-3.
\tag{2.4}
$$

Let $E_A$ be the sum of the three second-order principal minors of $A$.
Expansion gives

$$
E_A=z_1z_2+z_1z_3+z_2z_3+\frac{2(w-3)}n.
\tag{2.5}
$$

Positive semidefiniteness of $A$ implies

$$
z_1z_2+z_1z_3+z_2z_3\ge0,
\tag{2.6}
$$

with equality precisely when at least two of the $z_a$ are zero and the
remaining one is nonnegative. Indeed, two negative entries would make the
quadratic form at their coordinate difference negative. If exactly one,
say $z_1$, is negative, each of $z_2,z_3$ must be strictly positive:
a nonpositive one would make the corresponding second-order principal
minor negative. The determinant condition

$$
0\le\det A=z_1z_2z_3+
\frac{z_1z_2+z_1z_3+z_2z_3}{n}
$$

then forces the sum in (2.6) to be strictly positive. If all $z_a$ are
nonnegative, the sum vanishes exactly when at most one is positive.
Conversely, that condition gives a positive semidefinite matrix in (2.4).
Thus

$$
E_A\ge\frac{2(w-3)}n
\tag{2.7}
$$

has exactly the stated degree equality conditions.

To transfer (2.7) to all of $H$, take Gram vectors $v_a,y_i$ for the hubs
and leaves, respectively. For example, use the columns of the symmetric
positive semidefinite square root of $H$. Then

$$
\langle v_a,v_b\rangle=\frac1n\quad(a\ne b),\qquad
\|v_a\|^2=\delta_a-1+\frac1n,\qquad
\sum_a v_a+\sum_i y_i=0.
\tag{2.8}
$$

The last assertion follows since the squared norm of that sum is
$\mathbf1^{\mathsf T}H\mathbf1=0$.

For vectors $u,v\in\mathbb R^n$, define $u\wedge v$ to have coordinates
$u_jv_k-u_kv_j$ for $j<k$. Expansion gives

$$
\|u\wedge v\|^2=\|u\|^2\|v\|^2-\langle u,v\rangle^2.
\tag{2.9}
$$

Hence the sum of these squared areas over all pairs of Gram vectors is
$E$: it is the sum of the second-order principal minors of $H$, equivalently
$((\operatorname{tr}H)^2-\operatorname{tr}(H^2))/2$.
Split it into hub pairs, leaf pairs and cross pairs:

$$
E=E_A+E_Y+E_C,
\quad E_Y=\sum_{i<j}\|y_i\wedge y_j\|^2\ge0,
\quad E_C=\sum_{a,i}\|v_a\wedge y_i\|^2.
$$

Put $V=v_1+v_2+v_3$. For each $a$, bilinearity and the elementary inequality
$\sum_i\|b_i\|^2\ge m^{-1}\|\sum_i b_i\|^2$, applied to
$b_i=v_a\wedge y_i$, yield

$$
E_C\ge\frac1m\sum_a\|v_a\wedge V\|^2.
\tag{2.10}
$$

Here $\sum_i y_i=-V$ by (2.8), so its sign disappears in the squared norm.
For completeness set $h_a=\|v_a\|^2$ and $T=\sum_a h_a=w-3+3/n$.
Then $\|V\|^2=T+6/n$ and $\langle v_a,V\rangle=h_a+2/n$.
Using (2.9),

$$
\begin{aligned}
\sum_a\|v_a\wedge V\|^2
&=T(T+6/n)-\sum_a(h_a+2/n)^2\\
&=T^2-\sum_a h_a^2+2T/n-12/n^2\\
&=2E_A+2(w-3)/n.
\end{aligned}
\tag{2.11}
$$

The last equality uses $E_A=\sum_{a<b}(h_ah_b-1/n^2)$.
Consequently

$$
\begin{aligned}
E&\ge\left(1+\frac2m\right)E_A+\frac{2(w-3)}{mn}\\
&\ge\left(1+\frac2m\right)\frac{2(w-3)}n+
\frac{2(w-3)}{mn}
=\frac{2(w-3)}m,
\end{aligned}
\tag{2.12}
$$

where $n=m+3$. Equality in (2.2) forces equality in (2.7), since its
coefficient $1+2/m$ is positive. By (2.4)–(2.6), two normalized hub
degrees are $1$ and their sum with the remaining degree is $w$. ∎

**Theorem 2.2 (Strict unrestricted comparison above the leaf trace bound).**
For every $m\ge3$ and every $c\in(0,\infty)^{3m}$, with $t,w$ as in
Lemma 2.1, define

$$
F_m(w)=\frac{(2m+4)w-m^2-2m-12}{(2m+2)w-m^2-m-6},
\qquad
B_m=m(m+3)+\frac{m^2}{m-2}.
$$

Then

$$
\frac{tR(c)}{m+3}\le m+2-F_m(w)\le\frac{B_m}{m+3}.
\tag{2.13}
$$

The second inequality is strict whenever $W>m\lambda_2(L)$.
If $tR(c)=B_m$, then $w=m$ and equality holds in (2.2).

*Proof.* On $\mathbf1^\perp$, the eigenvalues of $H$ are the
$m+2$ nonnegative numbers $q_j=\lambda_j/t-1$, $2\le j\le n$.
Its remaining eigenvalue is zero. Write $e_k$ for the elementary symmetric
sums of these $q_j$, with $e_0=1$. Thus $e_1=S$, $e_2=E$, and
all $e_k\ge0$. Expanding $\prod_j(1+xq_j)$ and differentiating at
$x=1$ gives the exact identity

$$
\sum_{j=2}^n\frac{q_j}{1+q_j}
=\frac{\sum_{k=1}^{m+2}k e_k}{\sum_{k=0}^{m+2}e_k}
\ge\frac{S+2E}{1+S+E}.
\tag{2.14}
$$

To justify the inequality without a rank assumption, the last ratio is
strictly less than $2$, because $2(1+S+E)-(S+2E)=2+S>0$.
Every omitted denominator term $e_k$, $k\ge3$, carries numerator
coefficient $k\ge3$, so adding these terms cannot decrease the ratio.
Equality holds exactly when all $e_k$ for $k\ge3$ vanish.

For fixed $S\ge0$, the derivative of $(S+2E)/(1+S+E)$ with respect
to $E$ is $(S+2)/(1+S+E)^2>0$. Substituting (2.1) and (2.2) into
(2.14) therefore yields

$$
\sum_{j=2}^n\frac{q_j}{1+q_j}
\ge\frac{S+4(w-3)/m}{1+S+2(w-3)/m}=F_m(w).
\tag{2.15}
$$

By (1.1),

$$
\frac{tR(c)}n=\sum_{j=2}^n\frac1{1+q_j}
=m+2-\sum_{j=2}^n\frac{q_j}{1+q_j}.
\tag{2.16}
$$

This proves the first inequality in (2.13). The denominator of $F_m$ is
positive for $w\ge m$: at $w=m$ it is
$m^2+m-6=(m-2)(m+3)>0$, and its slope is positive. Direct differentiation
and evaluation give

$$
F_m'(w)=\frac{12m}{((2m+2)w-m^2-m-6)^2}>0,
\qquad
F_m(m)=\frac{m^2+2m-12}{(m-2)(m+3)}.
\tag{2.17}
$$

In particular,

$$
m+2-F_m(m)=m+\frac{m^2}{(m-2)(m+3)}=\frac{B_m}{m+3}.
$$

This proves the remaining assertions in (2.13), including strictness for
$w>m$. If $tR=B_m$, strict increase forces $w=m$.
Strict increase with respect to $E$ in (2.15) then forces
$E=2(m-3)/m$, as asserted. ∎

## 3. Complete labelled equality class

**Theorem 3.1 (Product maximum and every equality conductance).** For every
integer $m\ge3$,

$$
\max_{c\in(0,\infty)^{3m}}\lambda_2(L(c))R(c)
=B_m=m(m+3)+\frac{m^2}{m-2}.
\tag{3.1}
$$

Equality holds exactly as follows: choose $t>0$ and one labelled hub
$a_*$, and set, for every leaf $x_i$,

$$
c_{a_*i}=\frac{t(m-2)}m,\qquad
c_{ai}=\frac tm\quad(a\ne a_*).
\tag{3.2}
$$

Every such conductance is strictly positive and has $\lambda_2=t$ and
$R=B_m/t$. For $m=3$ the three descriptions in (3.2) coincide in one
ray. For $m>3$ they are exactly three distinct rays in the labelled
conductance space.

*Proof.* The upper bound is Theorem 2.2. Suppose first that a conductance
attains it, and use $t=\lambda_2(L)$. That theorem gives $w=m$ and equality
in Lemma 2.1. In (2.3), all $m-1$ Rayleigh lower bounds must now be
equalities. In particular,

$$
\sum_{k=1}^{m-1}f_k^{\mathsf T}Hf_k=0.
$$

Every summand is nonnegative. For a positive semidefinite matrix,
$z^{\mathsf T}Hz=0$ implies $Hz=0$, as is seen from its orthogonal
spectral decomposition. Hence $H$ annihilates $U$. Since $P$ is identity
on $U$, this means $Lz=tz$ for every $z\in U$.

For any distinct leaves $i,j$, apply this equality to
$z=e_{x_i}-e_{x_j}$. Its three hub coordinates give

$$
c_{ai}=c_{aj}\quad(1\le a\le3),
\tag{3.3}
$$

and its $i,j$ leaf coordinates give $s_i=s_j=t$. Thus each hub row is
constant over all leaves, and the common leaf sum is $t$. This conclusion
accounts for every one of the $3m$ independent edge variables.

By the equality condition of Lemma 2.1, two hub degrees are $t$ and the
remaining one is $(m-2)t$. Equation (3.3) now divides each degree equally
among its $m$ incident edges, proving (3.2). For $m=3$ all three degrees
are $t$, so the same conclusion holds without a distinguished hub.

For sufficiency, homogeneity permits $t=1$. Relabel the chosen hub as
$a_1$ only for this spectral calculation, and put
$p=(m-2)/m$ and $q=1/m$. The leaf-difference subspace $U$ is invariant
with eigenvalue $1$ and dimension $m-1$. Independently,
$e_{a_2}-e_{a_3}$ is an eigenvector with eigenvalue $mq=1$.
Their common orthogonal complement has the orthonormal basis

$$
e_{a_1},\qquad \frac{e_{a_2}+e_{a_3}}{\sqrt2},\qquad
\frac1{\sqrt m}\sum_i e_{x_i}.
$$

The representing matrix there is

$$
T_m=\begin{pmatrix}
m-2&0&-(m-2)/\sqrt m\\
0&1&-\sqrt{2/m}\\
-(m-2)/\sqrt m&-\sqrt{2/m}&1
\end{pmatrix}.
\tag{3.4}
$$

Its kernel contains $(1,\sqrt2,\sqrt m)^{\mathsf T}$, representing the
constant vector. Its trace is $m$. The sum of its three second-order
principal minors is

$$
(m-2)+\left((m-2)-\frac{(m-2)^2}{m}\right)
+\left(1-\frac2m\right)=\frac{(m+3)(m-2)}m.
$$

Therefore its remaining two eigenvalues $\alpha\le\beta$ satisfy

$$
\alpha+\beta=m,\qquad
\alpha\beta=\frac{(m+3)(m-2)}m,
\quad
\det(\mu I-T_m)=\mu\left(\mu^2-m\mu+
\frac{(m+3)(m-2)}m\right).
\tag{3.5}
$$

They are real since $T_m$ is symmetric, and strictly positive by
connectedness and (1.2). Evaluating their quadratic at $1$ gives

$$
(1-\alpha)(1-\beta)=\frac{2(m-3)}m\ge0.
$$

Since $\alpha+\beta=m\ge3$, they cannot both be at most $1$.
It follows that $1\le\alpha\le\beta$; if $m>3$ both inequalities
$1<\alpha,\beta$ are strict, while for $m=3$ the roots are $1,2$.
The full spectrum, retaining repetitions, is consequently

$$
0,\quad 1\ \text{($m$ times)},\quad\alpha,\beta.
\tag{3.6}
$$

Its smallest positive eigenvalue is $1$, and (1.1) gives

$$
R=(m+3)\left(m+\frac1\alpha+\frac1\beta\right)
=(m+3)\left(m+\frac{m^2}{(m+3)(m-2)}\right)=B_m.
$$

Scaling by $t$ proves all the sufficiency assertions. When $m>3$,
$m-2>1$, so the unique larger hub row determines $a_*$ from the
conductances themselves. Distinct choices cannot be scalar multiples:
each ray has $\lambda_2=t$, and normalizing that value to $1$ fixes the
scale. They therefore give exactly three distinct labelled rays.
For $m=3$, (3.2) assigns $t/3$ to all nine edges, independently of $a_*$. ∎

## 4. Every positive resistance level

**Theorem 4.1 (Finite strictly positive attainment and all optimizers).**
For every integer $m\ge3$ and every $R_0>0$, the nonempty level set

$$
\mathcal F_{m,R_0}=\{c\in(0,\infty)^{3m}:R(c)=R_0\}
$$

has

$$
\max_{c\in\mathcal F_{m,R_0}}\lambda_2(L(c))=\frac{B_m}{R_0}.
\tag{4.1}
$$

All its labelled maximizers are (3.2) with the unique scale
$t=B_m/R_0$. There is one such assignment when $m=3$ and exactly three
when $m>3$. In particular, for $K_{3,3}$ every optimizing edge has
conductance $9/R_0$ and the optimum is $27/R_0$.

*Proof.* At every point of the level set, Theorem 3.1 implies
$\lambda_2R_0\le B_m$. Choose $t=B_m/R_0>0$ in (3.2).
All conductances are finite and strictly positive, and Theorem 3.1 gives
$R=B_m/t=R_0$ and $\lambda_2=t$. Hence the level set is nonempty and
the finite bound in (4.1) is attained inside the strictly positive domain.
If any feasible conductance attains that bound, then its product is $B_m$,
so the necessity part of Theorem 3.1 places it on exactly one of the stated
rays, with their coincident description understood at $m=3$. The identity
$R=B_m/t$ fixes its scale. Finally $B_3=3\cdot6+9=27$, and
$t/3=9/R_0$. No compactification or allowance of zero conductances enters
this existence or classification argument. ∎

## 追加锚（本行以下为增补区）

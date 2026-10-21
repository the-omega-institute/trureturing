# FIB atomic recursive holographic boundary geometry VII: spectral and native boundary dimensions

This continuation preserves the prior theory-only results after the latest
VI continuation used the 147--156 section range for a separate application.
The statements below keep their declared comparison operators, source metrics,
and task scopes.

## 157. Quantitative robustness of the normalized bound state

The strict gap in Theorem 55.4 also has a perturbative meaning. This
section keeps the common rooted carrier, counting measure, inherited seams
and normalization of §§55.1--55.5 fixed; §138 supplies the later native-lift
ledger. A perturbation below is only a
bounded real multiplication operator on that carrier; it is not a new
physical field, a change of source history, or a claim about a spatial
dimension.

For a bounded real sequence $w=(w(p))_{p\in\mathcal P}$, write

$$
W_w f(p)=w(p)f(p),
\qquad
\delta_w=\|W_w\|=\sup_{p\in\mathcal P}|w(p)|,
\qquad
\mathsf H_w=\mathsf H+W_w.
\tag{157.1}
$$

Let

$$
m_w=\inf_{\|f\|=1}\langle f,\mathsf H_wf\rangle.
\tag{157.2}
$$

The finite restriction on an actual domain $D_j(t)$ is obtained by
compressing both $\mathsf H$ and the same multiplication operator $W_w$;
write its quadratic form as

$$
\mathcal E_{D_j,w}(f)=\mathcal E_{D_j}(f)+\langle I_{D_j}f,W_wI_{D_j}f\rangle
$$

and denote its normalized minimum by $m_{j,w}(t)$. No stage-dependent
renormalization of $w$ is made.

**Theorem 157.1 (uniform bounded-potential robustness).** Let

$$
\Delta=\epsilon_*-m>0,
\qquad
0\le\delta_w<\frac{\Delta}{2},
\tag{157.3}
$$

where $m$ and $\epsilon_*=a(3-2\sqrt2)$ are the common infimum and escape
edge of §§55.3--55.4. Then

1. $m_w<\epsilon_*-\delta_w$ and the normalized infimum $m_w$ is attained;
2. every normalized $\mathsf H_w$-minimizing sequence has a strongly
   convergent subsequence in $\ell^2(\mathcal P)$, and every cluster point is
   a normalized ground state;
3. for every fixed original source $t$, $m_{j,w}(t)\downarrow m_w$ as the
   actual whole-$\rho$ domains exhaust the common carrier; if $f_j$ is any
   normalized finite state satisfying
   $\mathcal E_{D_j,w}(f_j)-m_{j,w}(t)\to0$, their zero extensions are
   strongly precompact and their cluster points are common normalized ground
   states.

For any sequence of original sources and accepted indices $(t_n,j_n)$ whose
contained ball radii tend to infinity, the corresponding minimum values
converge to $m_w$ and normalized near-minimizers have the same strong
precompactness conclusion, with the same fixed $w$ and common embedding; no
monotonicity is asserted for this varying sequence.

**Proof.** The bounded perturbation gives the two elementary Rayleigh
inequalities

$$
m-\delta_w\le m_w\le m+\delta_w.
\tag{157.4}
$$

The second inequality follows by evaluating $\mathsf H_w$ on a normalized
near-minimizer of $\mathsf H$; the first is the analogous lower estimate.
For a normalized sequence $f_n\rightharpoonup f$, put
$r_n=f_n-f$ and $\alpha=\|f\|^2$. The compactness of $M_\phi$ and the
boundedness of $W_w$ make all mixed terms tend to zero. The kinetic gap in
(55.10), together with $W_w\ge-\delta_wI$, therefore gives

$$
\liminf_n\langle f_n,\mathsf H_wf_n\rangle
\ge
\langle f,\mathsf H_wf\rangle
+(\epsilon_*-\delta_w)(1-\alpha).
\tag{157.5}
$$

Since $\langle f,\mathsf H_wf\rangle\ge m_w\alpha$, a minimizing sequence
and (157.4) imply

$$
m_w
\ge m_w\alpha+(\epsilon_*-\delta_w)(1-\alpha),
\qquad
\epsilon_*-\delta_w-m_w
\ge\Delta-2\delta_w>0.
\tag{157.6}
$$

Consequently $\alpha=1$. Weak convergence is then strong convergence, and
the limit attains $m_w$. The same calculation applies to every normalized
near-minimizer, proving the second assertion.

For the finite restrictions, zero extension identifies each finite Rayleigh
quotient with the common quadratic form on its support. Nested exhaustion
gives $m_{j,w}(t)\ge m_w$ and monotonicity. A finite-support approximation to
any common unit trial gives the reverse limiting inequality, so
$m_{j,w}(t)\downarrow m_w$. Finite near-minimizers are consequently common
near-minimizers, and (157.5)--(157.6) gives strong precompactness. The varying
source statement uses exactly the same contained-ball argument as (55.13),
with no change to the common embedding. $\square$

The radius in (157.3) is a certified worst-case margin, not an optimal
radius for each particular $w$. It is nevertheless a new distinction from
finite negativity: the quantity that protects normalization is the distance
from the infinite minimum to the escape edge, and a perturbation consumes at
most two copies of its operator-norm budget, one in the trial value and one
in the escaping lower bound.

The zero-margin boundary is already realized inside the same carrier. In the
weak-coupling range of (55.18b), $m=\epsilon_*$ and the radial strings there
are weakly null normalized near-minimizers. Thus no positive uniform radius
depending only on $\epsilon_*-m$ can be asserted at equality; at $w=0$ itself
there need not be a normalized ground state. This is a sharp boundary for
the *gap-based certificate*. It does not claim that every individual
perturbation at equality destroys every possible threshold state, nor that
the sufficient radius is necessary for a fixed perturbation.

The result is a stability statement for the declared occurrence operator.
It does not turn bounded multiplication into a native FIB action, does not
identify $\epsilon_*-m$ with a physical noise budget, and does not establish
an operation-, metric-, field- or clock-preserving bridge to Euclidean space.
In particular it supplies no dimension-selection theorem; it records how a
strict escape gap can be spent while retaining a normalized boundary state.

## 157.99 追加锚（本行以下为增补区）
## 158. Native coherent Markov lifts do not select a global heat-trace dimension

**Definition 158.1 (first births and the common birth Hilbert space).**
Fix one finite source $u\in\mathcal T$ of Definition 127.1 and its uncapped
accepted history. Put

$$
b_e=|\mathcal P_e|,\qquad |B_e|=2b_e,\qquad
\eta(u)=\min\{e\ge0:b_e>0\}.
\tag{158.1}
$$

Here $B_e$ is born in the step $e\to e+1$, rather than already being present
at epoch $e$. Every finite source has at least one terminal leaf, so
$\eta(u)=0$ if it has a beta leaf and $\eta(u)=1$ otherwise. The latter
initial step is an accepted empty birth. A beta always has a beta left
child, so $b_e>0$ at every $e\ge\eta(u)$; in particular there are infinitely
many nonempty birth blocks. This also follows from Proposition 128.3.
Its $h(u)$ additionally requires an existing branch: $\eta(\beta)=0$ and
$h(\beta)=1$, whereas $\eta(\alpha)=1$ and $h(\alpha)=2$. Thus the
first-birth offset below is $e-\eta(u)$, without dropping either singleton's
first birth or any accepted empty epoch.

Start with $G_0=I$ and $Q_0=-L_0$. Fix

$$
r>1,\qquad C>\max_{p\in V_0}s_0(p),\qquad
s_0(p)=-Q_0(p,p),\qquad C>0.
\tag{158.2}
$$

At every nonempty birth choose the parameters of Proposition 127.2 to be

$$
q_e=0,\qquad \lambda_e=C r^{e-\eta(u)},\qquad
K_e=\lambda_e I_{2b_e},\qquad
G_{e+1}=W_e^{-\mathsf T}
 \operatorname{diag}(G_e,\lambda_e^{-1}I_{2b_e})W_e^{-1}.
\tag{158.3}
$$

At an empty birth retain $G_{e+1}=G_e$, $Q_{e+1}=Q_e$ and the identity
embedding. The original $V_e,E_e,L_e,T_e$ and the initial norm are fixed;
the compatible successor norms are allowed to depend on $r$. The same
comparison parameter $t$ is used at every step, without an epoch-dependent
change of clock.

For each such lift write $S_e=G_e^{1/2}$,
$H_e=S_e^{-1}L_eS_e^{-1}$ and $V_e^{\rm iso}=S_{e+1}T_eS_e^{-1}$.
These $V_e^{\rm iso}$ are the normalized isometric embeddings called $V$
in Definition 135.1; they are not the occurrence sets $V_e$.
The common abstract birth space is

$$
\mathscr H_u=\mathbb C^{V_0}\mathbin{\oplus}
 \bigoplus_{e\ge\eta(u)}\mathbb C^{B_e}.
\tag{158.4}
$$

The finite initial summand includes all accepted empty steps before the
first birth. Identifications with the normalized finite spaces use the
orthogonal birth charts of Proposition 135.3. The dimensions and labels of
(158.4) are independent of $r$, although those identifications depend on
the chosen norms.

**Theorem 158.2 (a fixed beta source realizes every positive logarithmic heat dimension).**
For $u=\beta$, every $r>1$ and every $C>0$, (158.3) gives a conservative
Markov generator at every finite epoch, with exact form preservation, norm
preservation and same-clock intertwining as in (128.2). On
$\mathscr H_\beta$ their normalized inductive limit is the nonnegative
self-adjoint operator

$$
\begin{aligned}
H_r&=0_{\mathbb C}\mathbin{\oplus}
       \bigoplus_{e\ge0}C r^e I_{2F_{e+1}},\\
\operatorname{Dom}(H_r)
 &=\left\{(z_{\rm init},(z_e)_{e\ge0})\in\mathscr H_\beta:
       \sum_{e\ge0}(C r^e)^2\|z_e\|^2<\infty\right\},
\end{aligned}
\tag{158.5}
$$

where $z_{\rm init}$ is the initial scalar. This operator has compact
resolvent and a single zero
mode. With positive eigenvalues counted with multiplicity, put
$N_r^+(\Lambda)=\operatorname{Tr}\mathbf1_{(0,\Lambda]}(H_r)$. Then

$$
N_r^+(\Lambda)=
\begin{cases}
0,&0\le\Lambda<C,\\
2(F_{m+3}-1),&\Lambda\ge C,\quad
 m=\lfloor\log_r(\Lambda/C)\rfloor,
\end{cases}
\tag{158.6}
$$

and, writing $\varphi=(1+\sqrt5)/2$ and
$\gamma_r=\log\varphi/\log r$,

$$
\begin{aligned}
\operatorname{Tr}(e^{-tH_r})
 &=1+2\sum_{e\ge0}F_{e+1}e^{-tCr^e}<\infty\qquad(t>0),\\
\lim_{\Lambda\to\infty}
 \frac{\log N_r^+(\Lambda)}{\log\Lambda}
 &=\lim_{t\downarrow0}
 \frac{\log\operatorname{Tr}(e^{-tH_r})}{\log(1/t)}
 =\gamma_r.
\end{aligned}
\tag{158.7}
$$

Define $d_{\rm heat}=2\gamma_r$ for this global logarithmic Hilbert
heat-trace convention. For each prescribed real $d>0$, the choice
$r=\varphi^{2/d}$ gives $d_{\rm heat}=d$. In particular $d=3$ is attained
at $r=\varphi^{2/3}$, and is not selected by finite coherence and Markov
positivity.

**Proof.** First consider the finite construction for any source in
Definition 158.1. The initial generator is Markov. Formula (128.3) leaves
every old row, hence every old exit rate, unchanged. A child born at step
$j\to j+1$ has exit rate $\lambda_j$. Consequently, at a nonempty step
$e\to e+1$, an old parent's exit is either an initial exit rate or a
$\lambda_j$ with $j<e$. The strict growth in (158.3) and (158.2) imply

$$
\kappa_c:=\lambda_e-s_e(\operatorname{par}_e(c))>0,
\qquad
s_e(\operatorname{par}_e(c))+\kappa_c=\lambda_e.
\tag{158.8}
$$

Thus $K_e$ is exactly an allowed diagonal choice in Proposition 128.2,
not an arbitrary SPD block whose Markov signs were left unchecked.
Corollary 127.3 gives its actual generator, and Proposition 128.2 proves
nonnegative off-diagonal entries and zero row sums. Proposition 127.2 and
Theorem 128.1 give the inherited SPD metric and all four identities in
(128.2). Empty births have their identity extensions. This induction
constructs compatible prefixes of every finite length, without a future
choice changing any earlier metric or rate.

Proposition 135.3 now identifies the successor operator, unitarily and with
its old isometric copy, with $H_e\oplus\lambda_e I_{2b_e}$. Iterating these
identifications yields (158.4) and the diagonal direct-sum operator
$H_{\rm initial}\oplus\bigoplus_e\lambda_e I_{2b_e}$, where
$H_{\rm initial}=L_0$. The algebraic sum of the finite spaces is a core:
truncation converges both in norm and in the graph norm specified by
$\sum_e\lambda_e^2\|z_e\|^2$. Coordinatewise adjoints give exactly this
domain, so the operator is self-adjoint. Each block is finite-dimensional
and $\lambda_e\to\infty$. The resolvent $(H_r+I)^{-1}$ is therefore a norm
limit of finite-rank truncations, since its tail norm is at most
$\sup_{e\ge E}(1+\lambda_e)^{-1}\to0$. This proves compact resolvent.

For beta, the initial space has one vertex and zero form. The terminal
counts obey $a_{e+1}=b_e$, $b_{e+1}=a_e+b_e$, with $(a_0,b_0)=(0,1)$.
Hence $b_e=F_{e+1}$ for $F_0=0,F_1=1$, and (158.5) follows. Births at
$e=0,\ldots,m$ are precisely the blocks with eigenvalue at most $\Lambda$
when $m$ is as in (158.6). The finite identity
$\sum_{e=0}^mF_{e+1}=F_{m+3}-1$ proves the exact count, including equality
at $\Lambda=Cr^m$. There are no positive initial eigenvalues.

The Fibonacci formula gives $F_{m+3}-1\asymp\varphi^m$ for $m\ge0$.
Since $r^m\le\Lambda/C<r^{m+1}$ and
$\varphi^m=(r^m)^{\gamma_r}$, there are constants $a_-,a_+>0$, independent
of $\Lambda$, such that

$$
a_-(\Lambda/C)^{\gamma_r}
 \le N_r^+(\Lambda)
 \le a_+(\Lambda/C)^{\gamma_r}\qquad(\Lambda\ge C).
\tag{158.9}
$$

Taking logarithms proves the counting limit. Put
$Z_r^+(t)=\operatorname{Tr}(e^{-tH_r})-1$. The elementary identity
$e^{-t\lambda}=t\int_\lambda^\infty e^{-tx}\,dx$, summed over positive
eigenvalues with nonnegative integrands, gives

$$
Z_r^+(t)=t\int_0^\infty e^{-tx}N_r^+(x)\,dx.
\tag{158.10}
$$

This same intermediate identity is used for the different fixed operator
in [*FIB atomic biased boundary spectral counting*, Theorem 3.1](FIB_ATOM_BIASED_BOUNDARY_SPECTRAL_COUNTING.md).
Here (158.9) gives, for $0<t\le C^{-1}$,

$$
\frac{a_-}{\mathrm e}(Ct)^{-\gamma_r}
 \le \mathrm e^{-1}N_r^+(1/t)
 \le Z_r^+(t)
 \le a_+(Ct)^{-\gamma_r}
        \int_0^\infty e^{-x}x^{\gamma_r}\,dx.
\tag{158.11}
$$

The lower estimate counts the eigenvalues at most $1/t$; the upper
estimate substitutes (158.9) in (158.10), with the count zero below $C$.
The last integral is finite because $\gamma_r>0$. The same upper bound
also proves finiteness for every $t>0$. Taking logarithms in (158.11), and
then including the single zero mode, proves (158.7). Substitution of
$r=\varphi^{2/d}$ proves the claimed range. These bounds assert a
logarithmic exponent, without an exact Weyl coefficient or a limit of a
logarithmic derivative of the trace. $\square$

**Proposition 158.3 (separate full-source birth-count variant).**
For every fixed finite $u\in\mathcal T$, let $a(u),b(u)$ be its original
alpha- and beta-leaf counts. In the construction (158.2)--(158.4),

$$
b_e=a(u)F_e+b(u)F_{e+1},\qquad
H_{u,r}=L_0\mathbin{\oplus}
 \bigoplus_{e\ge\eta(u)}Cr^{e-\eta(u)}I_{2b_e}.
\tag{158.12}
$$

Its domain is $\sum_{e\ge\eta(u)}(Cr^{e-\eta(u)})^2\|z_e\|^2<\infty$
inside $\mathscr H_u$, with no additional restriction on the finite initial
component. It is self-adjoint with compact resolvent. For $\Lambda\ge C$,

$$
\begin{aligned}
N_{u,r}^+(\Lambda)
 &=N_{\rm initial}^+(\Lambda)
   +2\sum_{e=\eta(u)}^{\eta(u)+m}b_e,
 &m&=\lfloor\log_r(\Lambda/C)\rfloor,\\
\operatorname{Tr}(e^{-tH_{u,r}})
 &=\operatorname{Tr}(e^{-tL_0})
   +2\sum_{e\ge\eta(u)}b_e e^{-tCr^{e-\eta(u)}}.
\end{aligned}
\tag{158.13}
$$

Here $N_{\rm initial}^+(\Lambda)$ counts the positive eigenvalues of $L_0$
up to and including $\Lambda$, and the heat identity is for $t>0$.
Below $C$ only the initial positive count remains. The two logarithmic limits
displayed in (158.7) equal $\log\varphi/\log r$ for this fixed $u$ as well.

**Proof.** The terminal recurrence in the preceding proof gives the first
formula of (158.12), including $e=0$. It is also the birth-count identity
of IV, Theorem 112.4, now with the full source convention of Definition
127.1. The construction and direct-sum argument in Theorem 158.2 already
apply to these sources, proving the operator, domain and compactness
claims. Since $a(u)+b(u)>0$, the leading Fibonacci coefficient is positive:
$b_{\eta(u)+j}\asymp_u\varphi^j$ as $j\to\infty$. The cumulative sum
therefore has this same order. Counting blocks proves (158.13), and the
two-sided power and integral bounds of (158.9)--(158.11) apply with
source-dependent constants. The finite initial count and finite initial
heat trace do not change either logarithmic limit. All constants refer to
one fixed source; no uniformity over unbounded initial source sizes is
needed. $\square$

**Proposition 158.4 (constant-rate and uniformly bounded-exit boundaries).**
For the same sources, replacing $r>1$ by $r=1$ in (158.3), with $C$ as in
(158.2), still gives coherent conservative finite Markov generators, but

$$
H_{u,1}=L_0\mathbin{\oplus}\bigoplus_{e\ge\eta(u)}C I_{2b_e},
\qquad
\operatorname{Tr}\!\left(e^{-tH_{u,1}}
              \mathbf1_{(0,\infty)}(H_{u,1})\right)=\infty
\quad(t>0).
\tag{158.14}
$$

More generally, suppose a coherent family of finite lifts with the
normalized isometric embeddings of §135 has conservative Markov $Q_e$ and
a uniform exit bound $-Q_e(p,p)\le M<\infty$ over all its epochs and
vertices. If its Hilbert inductive limit is infinite-dimensional, the
compatible normalized operator extends to a bounded nonnegative
self-adjoint operator with spectrum in $[0,2M]$. Its full heat trace is
infinite at every positive time.

**Proof.** For $r=1$ every inherited exit is at most $C$, and
$K_e=C I_{2b_e}\succ0$. The actual-coordinate formula (128.3) has child
exit $C$ and child-to-parent rate $C-s_e(p)\ge0$, with the other entries
as in (128.4). Some of these parent rates are zero: this boundary uses
the displayed sign calculation, rather than asserting the strict
$\kappa_c>0$ hypothesis of Proposition 128.2. Coherence still follows
from Proposition 127.2 and Theorem 128.1. Proposition 135.3 gives
(158.14). Infinitely many positive modes contribute the same positive
number $e^{-tC}$ to that trace.

For the general comparison, each row of $-Q_e$ has diagonal $s_e(p)$ and
sum of absolute off-diagonal entries $s_e(p)\le M$. Gershgorin's bound
puts every real eigenvalue in $[0,2M]$. The eigenvalues are real and
nonnegative because $-Q_e$ is similar to the symmetric nonnegative $H_e$.
Thus $0\le H_e\le2MI$ in each normalized Hilbert space. Exact intertwining
makes these operators consistent on their dense isometric union, where
they have the same norm bound. Their extension is bounded self-adjoint
and satisfies $0\le H\le2MI$. Functional calculus gives
$e^{-tH}\ge e^{-2Mt}I$, whose trace is infinite in infinite dimension.
This comparison needs the uniform bound and compatible Hilbert structure;
finite Markov conservation alone does not impose either a heat-trace
exponent or trace finiteness. $\square$

**Definition 158.5 (scope of nonselection and the missing realization bridge).**
Here $d_{\rm heat}$ is twice a global logarithmic Hilbert heat-trace
exponent for the declared comparison operator. It is not a volume-growth
dimension, walk dimension, pointwise return exponent, spatial or manifold
dimension, or an identification of $t$ with physical time. The finite
Markov property refers to $Q_e$ in actual occurrence coordinates; an SPD
state metric need not be a diagonal measure, and its principal-root
normalization is not by itself a spatial heat-kernel realization.

The nonselection quantifier is already one fixed source $u=\beta$, the
same accepted substitutions, original unit-edge forms, parent-copy maps,
initial norm and comparison clock, with different allowed successor norms.
It does not hold a complete prescribed norm family fixed while varying its
spectrum. The parameter $r$ chooses external compatible metrics; it is not
a native executable control. In particular the theorem supplies no rule
making a native history choose $r=\varphi^{2/3}$. The freedom established
here concerns spectral realization, not removal of the information-escape
conditions of §129 or a physical consequence of the stability result in
§157. Deriving physical $d=3$ would additionally require a specified
metric, measure and locality/transport correspondence, a relation between
its heat law and physical observations, and a criterion selecting the
allowed norm or rate law. Such correspondences are extra hypotheses to be
proved for a proposed realization; they are not consequences of the birth
count.

The fixed biased boundary form in
[*FIB atomic biased boundary spectral counting*, Definitions 1.1 and 4.1,
Theorem 3.1](FIB_ATOM_BIASED_BOUNDARY_SPECTRAL_COUNTING.md) has its own
logarithmic exponent one, with its declared boundary measure and clock.
That conclusion is retained: no unitary, form, measure or clock
identification between that boundary operator and this family is assumed.
Hierarchical pure-point spectra have classical precedents, for example
Bendikov--Grigor'yan--Pittet--Woess,
[*Isotropic Markov semigroups on ultra-metric spaces*, §3.2,
Theorem 3.8](https://arxiv.org/html/1304.6271v3). That theorem supplies
context for hierarchical eigenfunction decompositions, not a native FIB
realization bridge. The repo-derived content here is the explicit
simultaneous Markov/coherence construction on these actual source births
and its range of global exponents; no originality or priority claim about
hierarchical spectral freedom is included.

## 158.99 追加锚（本行以下为增补区）

## 159. Native boundary dimension, scale bridges, and task-level escape

The spectral freedom in §158 does not by itself select a geometric
dimension. The original infinite source boundary gives a sharper negative
test: its native cylinder scale has dimension one. A three-dimensional
carrier therefore requires a changed metric, extra coordinates, or a
transport bridge; replacing \(M\) by an equivalent measure alone does not
change this Hausdorff dimension.

### 159.1 The native cylinder ultrametric

Let

$$
\Omega=\{L,R\}^{\mathbb N}
$$

be the complete binary boundary. For a finite word \(p\), put

$$
s(p)=\#_L(p)+2\#_R(p),
\qquad
\delta(p)=\varphi^{-s(p)},
$$

where \(\varphi^2=\varphi+1\). If \(\omega\ne\eta\), let

$$
\omega\wedge\eta
$$

be their longest common prefix and define

$$
\boxed{
d_\varphi(\omega,\eta)=\delta(\omega\wedge\eta),
\qquad d_\varphi(\omega,\omega)=0.
}
\tag{159.1}
$$

Let \(M\) be the cylinder measure determined by

$$
\boxed{M([p])=\delta(p).}
\tag{159.2}
$$

This is consistent because

$$
\delta(pL)+\delta(pR)
=\delta(p)(\varphi^{-1}+\varphi^{-2})
=\delta(p).
$$

**Proposition 159.1 (native one-dimensional regularity).** The function
\(d_\varphi\) is an ultrametric. Every cylinder is a closed ball whose
diameter and \(M\)-mass are both \(\delta(p)\). Moreover, for every
\(\omega\in\Omega\) and \(0<r\le1\),

$$
\boxed{
\varphi^{-2}r\le M(B_{d_\varphi}(\omega,r))\le r.
}
\tag{159.3}
$$

Consequently \(M\) is \(1\)-Ahlfors regular and

$$
\boxed{\dim_H(\Omega,d_\varphi)=1.}
\tag{159.4}
$$

**Proof.** Two longest common prefixes are nested, so among three points
the two smaller common-prefix scales are bounded by the largest one. This
is the ultrametric inequality. A ball is the cylinder at the first prefix
whose scale is at most its radius. Passing from a prefix to either child
multiplies its scale by \(\varphi^{-1}\) or \(\varphi^{-2}\), which gives
(159.3) from (159.2). The standard cylinder cover and the ball lower bound
give the upper and lower Hausdorff estimates at exponent one. \(\square\)

For every finite source \(u\), the measure \(\nu_u\) of Definition 113.3
has a positive finite density on finitely many terminal cylinders. Hence
there are constants \(0<c_u\le C_u<\infty\) such that

$$
c_uM(A)\le \nu_u(A)\le C_uM(A)
$$

for every Borel set \(A\subseteq\Omega\). Thus each \(\nu_u\) has the
same Hausdorff dimension one in the native metric, although its constants
depend on the finite source.

### 159.2 Native scale cannot supply a three-dimensional carrier

**Proposition 159.2 (Lipschitz dimension obstruction).** Let \(Y\) contain
a compact set \(K\) of Hausdorff dimension three; in particular this holds
for a compact ball in a \(3\)-Ahlfors regular local carrier. There is no
Lipschitz map

$$
F:(\Omega,d_\varphi)\longrightarrow Y
$$

whose image contains \(K\). In particular, no uniformly bi-Lipschitz
identification of the native boundary with a three-dimensional carrier
exists.

**Proof.** Lipschitz maps do not increase Hausdorff dimension, so

$$
\dim_H F(\Omega)\le\dim_H\Omega=1.
$$

The compactness of \(\Omega\) makes \(F(\Omega)\) compact and therefore
closed. It cannot contain \(K\) of dimension three. A bi-Lipschitz map is
Lipschitz, so the stronger assertion follows. \(\square\)

This is a statement about retaining the native cylinder scale. It does not
exclude a non-Lipschitz coding, a hidden transverse coordinate, or a new
transport metric.

### 159.3 Snowflaking is a formal dimension change, not a native selection

For \(0<\alpha<1\), set

$$
d_{\varphi,\alpha}=d_\varphi^\alpha.
$$

The topology and cylinder \(\sigma\)-algebra are unchanged, while (159.3)
becomes

$$
\varphi^{-2}r^{1/\alpha}\le
M(B_{d_{\varphi,\alpha}}(\omega,r))
\le r^{1/\alpha}.
$$

Therefore

$$
\boxed{\dim_H(\Omega,d_{\varphi,\alpha})=\alpha^{-1}.}
\tag{159.5}
$$

Taking \(\alpha=1/3\) gives a formally three-dimensional Ahlfors scale on
the same set. It is an extra choice of metric; neither the source grammar,
the substitution \(\rho\), nor the native cylinder measure selects it.
Thus this is an independent scale bridge, not a native dimension theorem
and not a change to the heat-trace statement of §158.

### 159.4 Applying the source phase loss to future tasks

Applying Theorem 113.5 to a scale-sensitive task gives

$$
\nu_\alpha=\nu_\beta=M,
\qquad
W(\alpha)=1,
\qquad
W(\beta)=\varphi.
$$

Consequently the target \(F(u)=W(u)\), or the full future scale response

$$
F_n(u)=W(\rho^n u)=\varphi^nW(u),
$$

does not factor through the \(\nu\)-only observation. The pair
\((\alpha,\beta)\) is an explicit escape pair:

$$
\nu_\alpha=\nu_\beta,
\qquad
F_n(\alpha)\ne F_n(\beta)
\quad(n\ge0).
\tag{159.6}
$$

The quotient still supports the restricted action \(\nu\mapsto\nu\), since
\(\nu_{\rho u}=\nu_u\). What fails is action closure for tasks that retain
the acquired scale, INITIAL identity, or any legality condition depending
on that scale. The pair \((\nu,W)\) is the boundary datum supplied by
Theorem 113.5 that restores this phase on the attained finite-source image.

### 159.5 Scope

Sections 159.1--159.4 are exact statements for the full binary boundary,
the native Fibonacci cylinder weights, and the finite-source measures of
Definition 113.3. They do not prove a physical three-dimensional
realization, do not solve the strict four-source \(J\)-\(M\) joint-lift
problem, and do not establish the open quantitative gap in §11.11 of the
strict-real incidence continuation. They also do not contradict §158:
§158 varies compatible successor metrics for a fixed comparison operator,
whereas this section identifies the native metric and the task information
that a scale-free quotient omits. The Lipschitz dimension obstruction and
the snowflake calculation have not been formalized in Lean.

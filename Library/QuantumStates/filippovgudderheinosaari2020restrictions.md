---
bibkey: filippovgudderheinosaari2020restrictions
authors: S. N. Filippov, S. Gudder, T. Heinosaari and L. Leppäjärvi
year: 2020
title: Operational Restrictions in General Probabilistic Theories
doi: 10.1007/s10701-020-00352-6
url: https://arxiv.org/abs/1912.08538v1
claim: Convex effect subalgebras are interval intersections with real linear subspaces; meter simulation closure is a separate operational requirement.
strata_touched: []
license: citation-only
triage: anchor
---

# Original probability images and the complete comparison interface

This is a literature application to the original preparation, test and process
interface of the current [Theorem 81.8, equation (81.14)](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md#81-对角几何的单个内在投影与完整量子候选),
retaining the exact equivalent [equation (80.14)](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_V.md#80-全框架缺陷的内在上包络与共同原映射修复)
correspondence. The simpler current entrance uses one fixed source-projection
contraction and the unit-fixed mass witness on the same reconstructed models.
The probability-span representation and convex-effect-subalgebra classification
are existing mathematics. The application below supplies their parameter
correspondence, a tetrahedron obstruction to recovering menus from the specified
comparison table, and the descent conditions needed to retain original processes.
The classification, projection/moment and mass results are reused directly.
It is paper mathematics, without a new general theorem, novelty claim or Lean
kernel certification.

## Verified locator

- S. N. Filippov, S. Gudder, T. Heinosaari and L. Leppäjärvi,
  *Operational Restrictions in General Probabilistic Theories*,
  [DOI 10.1007/s10701-020-00352-6](https://doi.org/10.1007/s10701-020-00352-6),
  [arXiv:1912.08538v1](https://arxiv.org/abs/1912.08538v1), Theorem 3,
  pp. 14–15: convex effect subalgebras are intersections with linear subspaces
  containing the unit. Section 2.2, equation (6), defines finite random selection
  and classical post-processing of meters; §§4.4–5 distinguish this simulation
  closure from closure under every bounded effect sum.
- Alexander Wilce, *Symmetry and Composition in Probabilistic Theories*,
  [arXiv:0910.1527v2](https://arxiv.org/abs/0910.1527v2), §2, pp. 3–4:
  the span of the designated probability weights, its generated cone, and
  original outcome evaluations give an abstract state space with designated
  observables. An arbitrary outcome evaluation is not the unit functional.
- Martin Plávala, *General probabilistic theories: An introduction*,
  [arXiv:2103.07469v2](https://arxiv.org/abs/2103.07469v2), Theorem 3.19
  and Proposition 3.20: normalized evaluation representation and its dimension
  shift; §3.7 retains the no-restriction hypothesis separately.
- John Harding and Alex Wilce, *Order-unit spaces and probabilistic models*,
  [arXiv:2603.05682v2](https://arxiv.org/abs/2603.05682v2), §2,
  Examples 2.2(3)–(4) and Remark 2.3(1): original evaluation functionals,
  affine maps and distinct outcomes with equal effect images.
- Peter Janotta and Raymond Lal, *Generalized Probabilistic Theories Without
  the No-Restriction Hypothesis*,
  [arXiv:1302.2632v1](https://arxiv.org/abs/1302.2632v1),
  [DOI 10.1103/PhysRevA.87.052131](https://doi.org/10.1103/PhysRevA.87.052131):
  state and effect restrictions must be distinguished. That DOI belongs to
  arXiv:1302.2632.

## 1. The carrier of the original image

For each $X=A,D,E$, let $\Sigma_X$ be the nonempty set of original
preparation labels and $\mathcal T_X$ the original binary-test labels, with
original probabilities $\pi_X(e,\sigma)\in[0,1]$. Retain their raw menus,
devices, events, records and source/reference labels as additional data.
A supplied unit test $\mathbf1_X$ satisfies
$\pi_X(\mathbf1_X,\sigma)=1$ for every $\sigma$.
Define the **original image**, without taking any completion, by

$$
k_\sigma(e)=\pi_X(e,\sigma),\qquad
K_X=\{k_\sigma:\sigma\in\Sigma_X\}\subseteq\mathbb R^{\mathcal T_X}.
\tag{1}
$$

Require this image itself to be closed under every finite real probability
mixture, compact in the pointwise topology, and of finite affine dimension
$d_X$. These are explicit model conditions on realized probability tables.
The prescribed raw mixing operations must give those tables. A convex hull,
closure or dual construction cannot supply a missing preparation or test.
Probability-equivalent labels map to the same point but remain raw labels;
the construction does not identify their histories or future behaviors.
Retain every original menu as an indexed family of raw outcome occurrences,
with its device, event and source bindings and each occurrence's test image.
Equal images never merge occurrences or records; a new list of effects
summing to the unit is not thereby an original menu.

Suppress $X$ temporarily. The canonical objects are

$$
V=\operatorname{span}_{\mathbb R}K,\qquad
C=\{\lambda k:\lambda\ge0,\ k\in K\},\qquad
u(v)=v(\mathbf1),\qquad
\widehat e(v)=v(e),\qquad
\mathcal E=\{\widehat e:e\in\mathcal T\}.
\tag{2}
$$

Only the supplied unit coordinate defines $u$. General test coordinates have
their given probabilities, which need not be constant, much less constant one.
For $k_*\in K$,

$$
V=\mathbb R k_*\oplus\operatorname{span}(K-k_*),\qquad \dim V=d+1,
\tag{3}
$$

since $u(k_*)=1$ and $u$ vanishes on the difference span. Coordinate
evaluations separate $V$ by its definition as a space of functions. Their span
is therefore $V^*$: otherwise its annihilator in finite-dimensional $V$ would
be nonzero. Select finitely many original coordinates, including $u$, forming
a dual basis. They identify $V$ with $\mathbb R^{d+1}$; every other coordinate
is a linear combination of them. Thus the pointwise topology on $V$ is its
ordinary finite-dimensional topology, and $K$ is compact there.

Real mixture closure makes $C$ convex, and its definition makes it generating.
For nonzero $\lambda k$, $u(\lambda k)=\lambda>0$, so $C$ is pointed.
It is closed: if $\lambda_jk_j\to v$, then $\lambda_j\to u(v)$; a positive
limit gives $v/u(v)\in K$ by compactness, while a zero limit gives $v=0$
by boundedness of $K$. Consequently

$$
C\cap\{u=1\}=K
\tag{4}
$$

is exactly the original normalized image, and $V$ is nonzero.
Every affine $g:K\to\mathbb R$ extends uniquely to a linear functional on
$V$. To check well-definedness, any relation $\sum_i a_i k_i=0$ has
$\sum_i a_i=0$ by $u$. Splitting its positive and negative coefficients and
normalizing their common total gives equality of two original convex mixtures;
affinity gives $\sum_i a_i g(k_i)=0$. This proves the extension and hence

$$
[0,u]_{C^*}\ \cong\ \operatorname{Aff}(K,[0,1]),\qquad
\widehat e(k_\sigma)=\pi(e,\sigma),\qquad
\mathcal E\subseteq[0,u]_{C^*}.
\tag{5}
$$

These are the finite-coordinate application details of the cited standard
representation, not a claim of full original effect availability. If $K$ is a
singleton, $V$ has dimension one and tests may still have any constant value
in $[0,1]$. Compact finite-dimensional convexity gives finite decompositions
over $P=\operatorname{ext}K$ even when $P$ is not closed; no pure point need
be exposed. Such decompositions do not provide a physical pure-state lottery.

## 2. Original bounded doubling and full effects

Assume original tests contain $0,\mathbf1$, admit real probability mixing,
and have original complements, all with their stated probability tables.
Bounded doubling means precisely

$$
\forall e\in\mathcal T:\quad
\bigl[\forall\sigma\in\Sigma,\ \pi(e,\sigma)\le\tfrac12\bigr]
\ \Longrightarrow\
\bigl[\exists b\in\mathcal T\ \forall\sigma\in\Sigma,
\ \pi(b,\sigma)=2\pi(e,\sigma)\bigr].
\tag{6}
$$

There is one original $b$ for **all** original preparations. In images this
is $f\in\mathcal E,\ 2f\le u\Rightarrow2f\in\mathcal E$.
It is equivalent, in finitely many algebraic steps, to

$$
f,g\in\mathcal E,\quad f+g\le u\quad\Longrightarrow\quad
f+g\in\mathcal E,
\tag{7}
$$

by mixing $f,g$ equally and doubling; conversely set $g=f$.
Together with complements and scaling by mixing with zero, (7) makes
$\mathcal E$ a convex effect subalgebra. The ambient interval generates
$V^*$: a linear functional is bounded on compact $K$, and an appropriate
multiple of $u$ shifts and scales it into $[0,u]$. Filippov et al., Theorem 3,
therefore applies with ambient space $V^*$, cone $C^*$ and subspace
$W=\operatorname{span}_{\mathbb R}\mathcal E$.

Here is the exact finite application, avoiding a menu-closure assumption.
For $h\in W\cap[0,u]$, write $h=\sum_jc_j f_j$, $f_j\in\mathcal E$,
and choose an integer $N\ge\max(1,\sum_j|c_j|)$. Original mixing with zero gives

$$
a=N^{-1}\sum_jc_j^+f_j\in\mathcal E,\qquad
b=N^{-1}\sum_jc_j^-f_j\in\mathcal E,\qquad a-b=h/N.
$$

Since $0\le b\le a\le u$, the bounded sum $(u-a)+b=u-h/N$ is available;
its complement is $h/N$. Repeated bounded addition gives $kh/N$ for
$k=1,\ldots,N$, always below $u$. Thus
$\mathcal E=W\cap[0,u]$. The original coordinate evaluations already span
$V^*$ by §1, so $W=V^*$. We have proved the finite equivalence

$$
\text{original bounded doubling}\quad\Longleftrightarrow\quad(7)
\quad\Longleftrightarrow\quad\mathcal E=[0,u]_{C^*}.
\tag{8}
$$

The reverse implication is immediate. No topological closure of the test
menu, limiting operation or new label is used. This expresses the original
no-restriction availability premise; reciprocal comparisons do not imply it.
Even availability of every binary effect supplies neither all joint meters
nor an instrument or update map for each effect.

## 3. Two tetrahedron menus with the same specified T

Let the original preparations be all points $x$ of the tetrahedron
$\Delta_4=\{x_i\ge0:\sum_i x_i=1\}$. An effect is its four vertex values
$a\in[0,1]^4$, with probability $a\cdot x$. With $u=(1,1,1,1)$ and
coordinate effects $e_i$, consider the original effect images

$$
\mathcal E_{\rm small}=\operatorname{conv}\{0,u,e_i,u-e_i:1\le i\le4\},
\qquad \mathcal E_{\rm full}=[0,1]^4.
\tag{9}
$$

Both are compact, convex, complement-closed and separating. Their preparation
probability images satisfy §1 and have affine dimension three. For every
pure vertex $p_i$ and **every original mixed target** $x\in\Delta_4$,

$$
T^{\mathcal E}_{p_i}(x)
=\min\{a\cdot x:a\in\mathcal E,\ a_i=1\}=x_i
\tag{10}
$$

in both menus: each confirmer has nonnegative coordinates and $a_i=1$,
giving the lower bound $x_i$, and the common effect $e_i$ attains it.
This covers every pure reference, including zero target coordinates and
arbitrary mixed targets; the resulting pure reciprocity and fixed-half tables
agree. It is not equality for arbitrary mixed references. For instance,
confirmation of $r=(p_1+p_2)/2$ forces $a_1=a_2=1$. In the small menu any
convex combination with these two coordinates one uses only
$u,u-e_3,u-e_4$, so $a_3+a_4\ge1$, with equality attained. At the mixed
target $(p_3+p_4)/2$ its minimum is therefore $1/2$, whereas the full menu's
effect $e_1+e_2$ gives minimum zero.

The bounded sum $h=e_1+e_2\le u$ is absent from the small menu.
Indeed $H(a)=a_1+a_2-a_3-a_4$ is at most one on every generator in (9),
and therefore on its convex hull, but $H(h)=2$. Both summands are original
tests, so (7) fails. Equivalently, the original mixed test $h/2$ cannot be
doubled. These menus test only sufficiency of the specified pure-reference
$T$ table, not sufficiency of either complete (80.14) or (81.14) candidate.

There are explicit original meter realizations. In the small realization
start with four labelled binary meters $(e_i,u-e_i)$ and allow exactly finite
random choice and stochastic classical output post-processing, as in
Filippov et al., equation (6). The binary event images are exactly

$$
\sum_i\lambda_i[\alpha_i e_i+\beta_i(u-e_i)],\qquad
\lambda_i\ge0,\quad\sum_i\lambda_i=1,\quad
0\le\alpha_i,\beta_i\le1.
\tag{11}
$$

For fixed $i$ the bracket is the convex hull of $0,u,e_i,u-e_i$;
mixing over $i$ proves equality with $\mathcal E_{\rm small}$ in both
directions. Flattening successive random choices and stochastic matrices
proves simulation closure. In the full realization supply the labelled
four-outcome meter $(e_1,e_2,e_3,e_4)$: a binary post-processing has arbitrary
acceptance coefficients in $[0,1]^4$, so gives exactly the full image.
The four binary meters cannot simulate this four-outcome meter, since its
coarse-graining of outcomes $1,2$ would give the excluded $h$.
This simulation boundary concerns random selection and classical
post-processing only. Neither realization supplies sequential, nondisturbing
or adaptive instrument implementations by its effect table alone.

## 4. Descent of the supplied original processes

The following are entrance conditions, not consequences of bare probabilities.
An original unnormalized output is supplied with its mass $m\ge0$ and, for
$m>0$, an original normalized preparation label $\sigma$; its image is
$w=m k_\sigma$. At zero mass its image is zero, while its event, failure and
record labels remain. A weighted preparation here is a mathematical encoding
of supplied mass data, not a newly callable source.

For the original specified join and readback, write their output images on
normalized inputs as

$$
w_L(\delta,\alpha)=m_L(\delta,\alpha)k_{\ell(\delta,\alpha)}\in C_E,
\qquad
w_p(\epsilon)=m_p(\epsilon)k_{r(\epsilon)}\in C_D.
\tag{12}
$$

Zero outputs use the preceding convention. Require preservation of **all
finite real relations** in each input slot: for arbitrary real coefficients,

$$
\begin{aligned}
\sum_i c_i k_{\delta_i}=0&\Rightarrow
  \sum_i c_i w_L(\delta_i,\alpha)=0 &&(\text{every original }\alpha),\\
\sum_j b_j k_{\alpha_j}=0&\Rightarrow
  \sum_j b_j w_L(\delta,\alpha_j)=0 &&(\text{every original }\delta),\\
\sum_i c_i k_{\epsilon_i}=0&\Rightarrow
  \sum_i c_i w_p(\epsilon_i)=0.
\end{aligned}
\tag{13}
$$

These include descent through duplicate preparation labels. In particular,
every prescribed real mixture must satisfy, in each input slot, the
**mass-weighted** identity $w(\operatorname{mix}_i\lambda_i\sigma_i)=\sum_i\lambda_i w(\sigma_i)$,
not affinity after renormalizing its output.
When raw weighted inputs are supplied, require the same images to scale as
$w_p(a\epsilon)=a w_p(\epsilon)$ and
$w_L(a\delta,b\alpha)=ab w_L(\delta,\alpha)$ for $a,b\ge0$,
with zero and unequal masses included. Conversely, duplicate-label descent
and these real mixture identities imply (13) on normalized inputs: apply
the unit to a finite relation, split positive/negative coefficients with
equal total, and use the two equal convex mixtures. Thus rational mixtures
alone, or equality of normalized conditional output probabilities, is
insufficient; the omitted masses affect linearity.

Relations (13) give unique maps, explicitly

$$
\begin{aligned}
L\left(\sum_i c_i k_{\delta_i},\sum_j b_j k_{\alpha_j}\right)
 &=\sum_{i,j}c_i b_j w_L(\delta_i,\alpha_j),\\
p\left(\sum_i c_i k_{\epsilon_i}\right)&=\sum_i c_i w_p(\epsilon_i).
\end{aligned}
\tag{14}
$$

Changing either expansion changes the right side by zero by (13), proving
well-definedness, real bilinearity/linearity and uniqueness since the images
span. Supplied positive output masses imply positivity on $C_D\times C_A$
and $C_E$, respectively, by homogeneity and (4). Crucially, $K_D,K_E$ are
the entire original joint images; this tests every positive joint direction,
including entangled ones after the geometry bridge, not just products.

Every other advertised carrier-valued original process, including a supplied
reference extension, must obey the corresponding mass-weighted descent and
real mixture laws on its **own original input image**. For correlated
reference inputs this is the original joint image, not a product of local
marginals. Keep the same event, branch and reference on its original product
extension law, and require its stated positivity on the full original joint
cone. The original sufficient-reference and source conditions remain extra
contracts. Present isolated-test equality alone proves neither these
contextual laws nor equal future behavior. Raw devices and records stay
distinct even when their current effect images agree; an extension may not
be fabricated by identifying those devices. If these contracts fail, this
relational entrance does not certify the proposed original process model.

## 5. The current (81.14) entrance and its exact (80.14) correspondence

First specify $\mathsf R_{80.14}$ on the supplied original labelled data;
the equivalent current $\mathsf R_{81.14}$ below changes only its zero and
mass interfaces, preserving every other condition.
Use §§1–2 separately in $A,D,E$, impose (6) in each, and require §4 for the
same supplied original $L,p$ and every supplied process/reference consumer.
On the resulting full effect interval define, only for pure first endpoint,

$$
T^X_\xi(x)=\min\{f(x):0\le f\le u_X,\ f(\xi)=1\}.
$$

The confirmation face is nonempty and compact: it contains $u$, and
$[0,u]$ is closed and bounded, as evaluation on a finite basis of states
bounds all its coordinates in the dual space.
Require exactly the existing fixed-half law

$$
T^X_\xi\!\left(\frac{\eta+x}{2}\right)
=\frac{T^X_\eta(\xi)+T^X_\xi(x)}2
\quad(\xi,\eta\in\operatorname{ext}K_X,\ x\in K_X),\qquad X=A,D,E.
\tag{15}
$$

Reuse the [fixed-half same-carrier theorem](mullerududec2012selfduality.md#appendix-a-fixed-half-puremixed-entrance-to-s)
without reproving it: (15) is equivalent to full $S$ and to the arbitrary
real-weight mixed-remainder law. Use it **after** (8). Keep the full
[conditional EJA bridge](mullerududec2012selfduality.md#least-confirmation-forces-face-filter-purity)
of Definitions 75.1, 78.1 and 79.1: positive-dual generation, faithful
state/effect pairing, common frames, signed spectrality, face projections,
projectivity, purity of filters, and the attributed Barnum–Müller–Ududec
Theorem 16 classification. Pure reciprocity or self-duality alone does not
replace that bridge. Work in its chosen faithful Jordan coordinates, with
$u_X=\tau_X$, the entire square cones and normalized bases, and
$\langle x,y\rangle_X=\tau_X(x\circ_X y)$. Direct sums, rank-one factors
and Albert alternatives remain allowed at this stage.

All remaining predicates of (80.14) are retained, as follows.

1. Keep the **same original** whole-cone-positive $L:V_D\times V_A\to V_E$
   and $p:V_E\to V_D$, and the supplied original reference whose image is
   $\omega=1_D/\tau_D1_D$. Define internally

   $$
   \begin{aligned}
   K(a)&=pL(\omega,a),& M(a,b)&=pL(K(a),b),&Q(a,b,c)&=L(M(a,b),c),\\
   J(a)&=M(a,1_A),&H_{\rm s}(d)&=L(d,1_A),&B_1&=pH_{\rm s},\\
   U&=M(1_A,1_A),&G&=H_{\rm s}1_D,&F&=P_{U^{-1/2}}M.
   \end{aligned}
   \tag{16}
   $$

   Here $K(a)$ is the source's derived map, distinct from the bases $K_X$;
   $P_v$ is the Jordan quadratic representation. The **same $p$ occurs
   twice** in $M$. Keep both $\operatorname{span}_{\mathbb R}M(V_A,V_A)=V_D$
   and $\operatorname{span}_{\mathbb R}L(V_D,V_A)=V_E$, and full-real
   $Z:B_1M(a,b)=u_A(a)Jb$ for all $a,b\in V_A$. Whole-cone positivity
   includes all joint directions; real spanning does not make a joint cone
   product-generated. As in Definition 80.1, positivity and the two spans
   give $U,G>0$ before any zero condition, so $F$ is defined at this stage.

2. Keep the **complete all-frame zero envelope**, precisely

   $$
   \mathcal D(L,p)=\max_{B\in\mathcal F(A)}\left[
   \|U\|_2^2-\sum_{e\in B}\|Je\|_2^2+
   \|G\|_2^2-\sum_{e,f\in B}\|H_{\rm s}F(e,f)\|_2^2\right]=0,
   \tag{17}
   $$

   where $\mathcal F(A)$ consists of **all complete primitive Jordan frames**
   of the chosen faithful structure, with
   $\|x\|_2^2=\tau_X(x\circ_Xx)$. No selected frame or infimum replaces
   the maximum. Theorem 80.3
   restores both whole-cone zero-preservation relations $D_J,D_H$, hence PRE.

3. Keep the original fixed $t,s\in(0,1)$ and $\mathsf{Mass}_{t,s}$:
   there exists real linear $\Phi:V_A\to V_A$ with
   $\Phi(C_A)\subseteq C_A$, $u_A\Phi=u_A$, and
   $\{f\in V_A^*:f\Phi=f\}=\mathbb R u_A$ over **all real functionals**.
   For the original $m_2=u_DM$, $m_3=u_EQ$, keep both identities

   $$
   \begin{aligned}
   m_2(a,b)&=t\,m_2(\Phi a,b)+(1-t)m_2(a,\Phi b),\\
   m_3(a,b,c)&=st\,m_3(\Phi a,b,c)+s(1-t)m_3(a,\Phi b,c)
     +(1-s)m_3(a,b,\Phi c)
   \end{aligned}
   \tag{18}
   $$

   for all original positive $a,b,c$, including zero and unequal masses.
   These $t,s$ are unrelated to the comparison half. Keep the original
   $\mathrm A_0:u_EL(\omega,1_A/n)=1$, $n=\tau_A1_A$.
   A mathematical $\Phi$ does not supply a physical randomizer or reset.

4. Interpret original qualified-state H13 only after (17) has restored PRE,
   exactly as in Definition 80.2. In each active ordered block $(i,k)$ with
   both endpoint ranks at least two, use the original block projection
   $x=\pi_{ik}\rho$ and
   $\alpha_{ik}=F(-,c_k)|_{A_i}$, $\beta_{ik}=F(c_i,-)|_{A_k}$, with
   $c_i,c_k$ the original factor units. The **same original** total-trace-one
   state $\rho$ must have a strictly negative direction in at least one of
   $\alpha_{ik}\alpha_{ik}^*x-x$ and $\beta_{ik}\beta_{ik}^*x-x$ on every
   active block. Adjoints use the original canonical traces and the
   unnormalized units. Inactive blocks are arbitrary positive components,
   including zero; with no active blocks the qualification is all of $K_D$.
   No purity or fixed Schmidt spectrum is required. For that same qualified
   original $\rho$, require its **entire output** $I^{\rm raw}\rho$ positive,
   where $I^{\rm raw}=\widetilde T_{\rm raw}\widetilde M^{-1}$ and
   $T_{\rm raw}(a,c)=L(Ja,c)$. The inverse is used at its justified PRE stage.
   Neither a trace test, blockwise replacement state nor output-dependent
   choice of qualification suffices.

**Correspondence.** On these admissible original labelled models, forgetting
only mathematical witnesses, the canonical representation gives

$$
\mathsf R_{80.14}\quad\Longleftrightarrow\quad
\left[\mathrm{PRE}_0^{\rm mix}+\mathcal D=0+
\mathsf{Mass}_{t,s}+\mathrm A_0+\mathrm H13\right]
\quad\Longleftrightarrow\quad\mathrm{PRE}+C_{\rm joint}+\mathrm{C13}.
\tag{19}
$$

The middle expression is **exactly (80.14)**, with the same supplied maps,
reference and decorations. Here $C_{\rm joint}$ is the original joint
calibration $u_EL(1_D,1_A)+u_D(p1_E)\le2n^3$ on PRE, and
$\mathrm{C13}$ is $I^{\rm raw}(C_D)\subseteq C_E$.

For the forward arrow, §§1–2 give exactly the original full bases and full
effects, §4 gives the same original real maps, and the cited fixed-half
theorem gives full $S$ before the conditional EJA bridge. Conditions
(16)–(18) and H13 are then exactly the retained original predicates.
Apply 80.3, 79.5–79.7 and (80.14) in their original order: zero envelope
restores PRE; both mass laws and the anchor restore joint calibration before
H13; H13 supplies C13. No classification consumer is reproved here.

For the reverse arrow, take an original full carrier satisfying (80.14)
with its original preparations, tests, maps and supplied decorations.
Its evaluation map is

$$
\iota_X(x)(e)=e(x),\qquad
L'(\iota_Dd,\iota_Aa)=\iota_EL(d,a),\qquad
p'(\iota_Ez)=\iota_Dp(z).
\tag{20}
$$

Full effects separate the carrier, so $\iota_X$ is injective and maps onto
the span of its full original base image. It is a cone/base isomorphism and
pullback identifies the full effect intervals. Hence §§1–2 hold and the
original real maps satisfy (13) and all mass-weighted mixture laws, including
zero outputs. The existing fixed-half theorem supplies (15).
Transport the **entire chosen faithful structure**: set
$\iota_Xx\circ'_X\iota_Xy=\iota_X(x\circ_Xy)$,
$1'_X=\iota_X1_X$, $\tau'_X\iota_X=\tau_X$, and transport the trace
inner products, quadratic representations, all complete frames, norms,
adjoints and witnesses. Thus (17), both (18), $\Phi$, the original $t,s$,
anchor and H13 correspond exactly. In particular this is not an arbitrary
cone isomorphism while incompatible geometry is held fixed.
Carry the **same** original $L,p,\omega,\rho$, devices, events, menus,
reference contexts, source labels and records through evaluation. Contextual
extensions are transported on their original joint carriers with the same
product laws; they are not constructed from isolated probabilities.
This proves the first equivalence. The second is the cited (80.14),
including its reverse witness construction. The equivalence is relative to
the declared original descent and process contracts; it does not turn an
undecorated probability table into an original operational model.

**Direct application of the current entrance.** On these very same canonical
carriers, chosen faithful Jordan/trace structures and original $z=(L,p)$,
apply Theorem 81.3 and Proposition 81.4. For each complete primitive frame
$B$, set $\Pi_B=\sum_{e\in B}|e\rangle\langle e|$ and, with
$n=\tau_A1_A$, use precisely the source objects

$$
\begin{aligned}
P_0&=|1_A\rangle\langle1_A|/n,&\mathsf h_A&=P_0\otimes P_0,\\
\mathscr H_A&=\operatorname{span}_{\mathbb R}\{\Pi_B\otimes\Pi_B:B\in\mathcal F(A)\},&
\mathsf P_A&:\operatorname{End}(V_A\otimes_{\mathbb R}V_A)\to\mathscr H_A,\\
v_A&=\mathsf P_A\mathsf h_A,&\mathcal T&=H_{\rm s}\widetilde F,\\
\Gamma_z&=(\|U\|_2^2+\|G\|_2^2)\mathsf h_A
-\tfrac12(J^*J\otimes P_0+P_0\otimes J^*J)-\mathcal T^*\mathcal T.
\end{aligned}
\tag{17a}
$$

Here $\mathsf P_A$ is the fixed Hilbert–Schmidt orthogonal projection,
not a new input or physical operation. Reuse the source's unique invariant
full-support probability $\nu_A$ on the diagonal-projection orbit and its
moments $\mathsf C_A=\int\Pi\,d\nu_A$ and
$\mathsf W_A=\int(\Pi\otimes\Pi)\,d\nu_A$. Proposition 81.4 gives
$v_A\ne0$, $\mathsf W_A=v_A/\|v_A\|_{\rm HS}^2$ and

$$
\mathcal Q(z)=\frac{\langle\Gamma_z,v_A\rangle_{\rm HS}}{\|v_A\|_{\rm HS}^2}
=\|U\|_2^2+\|G\|_2^2-\operatorname{Tr}(J^*J\mathsf C_A)
-\operatorname{Tr}(\mathcal T^*\mathcal T\mathsf W_A),
\qquad
\langle\Gamma_z,v_A\rangle_{\rm HS}=0
\ \Longleftrightarrow\ \mathcal Q=0
\ \Longleftrightarrow\ \mathcal D=0
\ \Longleftrightarrow\ D_J+D_H.
\tag{17b}
$$

The last equivalences are Theorem 81.3 on the complete base already supplied
above. $\mathcal Q$ is distinct from the trilinear map $Q$ in (16), and
$\operatorname{Tr}$ is operator trace, not $\tau_X$. The second moment
retains the **same frame twice**: it cannot in general be replaced by
$\mathsf C_A\otimes\mathsf C_A$. Nor is $\mathsf W_A$ generally a
projection. These formulas apply the existing Haar/projection results;
they neither reprove them nor supply finite experimental readouts.

For the mass interface, take exactly Definition 81.7's fixed mathematical
witness $R_A(a)=u_A(a)1_A/n$. Theorem 81.8 supplies its positivity,
mass preservation and full real fixed-functional space $\mathbb R u_A$.
Replace the existential witness in (18) by the fixed identities

$$
\begin{aligned}
\mathsf E_2:\quad m_2(a,b)&=\tfrac12[m_2(R_Aa,b)+m_2(a,R_Ab)],\\
\mathsf E_3:\quad m_3(a,b,c)&=\tfrac13[m_3(R_Aa,b,c)+m_3(a,R_Ab,c)+m_3(a,b,R_Ac)]
\end{aligned}
\tag{18a}
$$

on all original positive inputs, including zero and unequal masses, with
the same $m_2=u_DM$, $m_3=u_EQ$. These are (18) at
$\Phi=R_A,t=1/2,s=2/3$; no local randomizer or joint extension is supplied.
Keep the same original anchor $\mathrm A_0$. Define $\mathsf R_{81.14}$
by these replacements alone. H13 is exactly clause 4, interpreted only
after (17b) restores PRE, on the **same original** qualified state and its
entire original output. In particular its block units and adjoints are not
renormalized. Applying Theorem 81.8 directly now gives

$$
\boxed{\mathsf R_{81.14}\ \Longleftrightarrow\
\bigl[\mathrm{PRE}_0^{\rm mix}+\langle\Gamma_z,v_A\rangle_{\rm HS}=0
+\mathsf E_2+\mathsf E_3+\mathrm A_0+\mathrm H13\bigr]}
\ \Longleftrightarrow\ \mathrm{PRE}+C_{\rm joint}+\mathrm{C13}
\ \Longleftrightarrow\ \mathsf R_{80.14}.
\tag{19a}
$$

The bracket is exactly (81.14), the current complete entrance. Its forward
direction first restores PRE, then uses both fixed mass laws and the anchor
to calibrate $C_{\rm joint}$ before H13 yields C13. Conversely, the same
original PRE+$C_{\rm joint}$ gives product masses by 79.6–79.7, so the
unit-fixed $R_A$ satisfies (18a); 81.3 and the original direction theorem
supply zero contraction and H13. Thus (19a) and (19) describe the same
actual models after forgetting mathematical witnesses. This does not
identify $R_A$ with a preassigned $\Phi$, or assert that either mass law
follows from comparisons alone.

For the reverse evaluation correspondence, extend the **full faithful
transport** in (20) to the fixed source data as well. Each $\iota_X$ is
an isometry for its transported canonical trace. Write
$\mathscr I=\iota_A\otimes\iota_A$ and
$\operatorname{Ad}_{\mathscr I}(Y)=\mathscr IY\mathscr I^{-1}$; then

$$
\begin{aligned}
\Pi'_B&=\iota_A\Pi_B\iota_A^{-1},&
\mathsf C'_A&=\iota_A\mathsf C_A\iota_A^{-1},&
\mathsf W'_A&=\operatorname{Ad}_{\mathscr I}(\mathsf W_A),\\
\mathsf P'_A&=\operatorname{Ad}_{\mathscr I}\mathsf P_A\operatorname{Ad}_{\mathscr I}^{-1},&
v'_A&=\operatorname{Ad}_{\mathscr I}(v_A),&
\Gamma'_{z'}&=\operatorname{Ad}_{\mathscr I}(\Gamma_z),\\
R'_A\iota_A&=\iota_AR_A,&
\langle\Gamma'_{z'},v'_A\rangle_{\rm HS}&=\langle\Gamma_z,v_A\rangle_{\rm HS}.&&
\end{aligned}
\tag{20a}
$$

The primed orbit and its probability are the corresponding pushforwards;
the induced Hilbert–Schmidt isometry carries $\mathscr H_A$, its orthogonal
projection and $\mathsf h_A$ as displayed. This is the precise parameter
transport of 81.3–81.4, not an arbitrary cone relabelling. The transported
unit and trace keep $n$, $R_A$, both masses and (18a) unchanged, just as
(20) carries $\Phi$ and (18). Throughout, the same actual $L,p$ (with $p$
twice), supplied reference, both spans, full-real $Z$, whole-cone positivity,
anchor, H13 state and all process/source decorations are retained. No
classification, Haar/projection or mass theorem is reproved.

## 6. Quantum correspondence, geometry and remaining conditions

The consumers of Theorem 81.8, §§79.8 and 80.5 retain their complete original premises.
Their correspondence is concise:

| Quantum structure | Retained route and scope |
| --- | --- |
| Density states, full effects, Born pairing | Full effects, (15), the faithful conditional EJA bridge and the original two-interface classification give finite complex Hermitian direct sums, $\Pr(f\mid\rho)=\sum_i\operatorname{Tr}(f_i\rho_i)$, $\sum_i\operatorname{Tr}\rho_i=1$, $0\le f_i\le I_i$. Reciprocity alone does not select the complex field. |
| Specified two- and three-copy tensors and readbacks | Both spans, full-real $Z$, the fixed projection's zero contraction (equivalently the zero envelope), fixed $\mathsf E_2,\mathsf E_3$, original anchor and H13 give the same original tensors and partial traces of (79.17), including scalar sectors and all correlated or entangled directions. |
| CP events, instruments and Lüders updates | The same actual event/branch/record, product extension, sufficient actual reference, full joint positivity, both budgets, complete-menu TP and update contracts remain required. |
| Hamiltonian evolution | Requires the supplied continuous, time-homogeneous reversible $*$-automorphism group in the original physical time, clock and units; static comparisons supply no such group or $\hbar$. |

More explicitly, CP/Kraus requires an original reference block of at least
each input block's dimension and positivity of that same event's extension
on the entire original joint cone. Preserve both original budgets (79.28),

$$
\sum_{a,j}F^a_{ji}\le I_i,\qquad
\sum_{a,j}F^a_{ji}\otimes u_{jk}\le I_i\otimes u_{ik},\qquad
F^a_{ji}=\sum_\ell K_{a,ji,\ell}^\dagger K_{a,ji,\ell},
\tag{21}
$$

and total TP on both sides for the same complete actual menu. Here $u_{ik}$
are the source's original matrix filter weights, distinct from $u_X$;
normalization makes them identities. Common-reset input-row consistency,
sequential composition and actual coarse-graining keep their original
contracts. Outcome probability is the original output mass; condition on
it only when strictly positive, retaining zero-branch records and permissions.
Lüders additionally needs the same CP branch to have sharp effect $P$ and
fix every normalized state certainly accepted by $P$. An effect does not
determine its update. Neither the mathematical $R_A$ in (18a) nor (18) for a
specified $\Phi$ certifies supplied physical reset operations; (18) does not
certify the positive joint extensions of (79.18); 79.9 supplies the original
counterexample. Mathematical existence witnesses create no physical menus.

All original preparation, event, reference, copy and source obligations
remain, including actual correlated joints, zero and unequal masses,
controls, ready/flags, complete records, failure, stopping, destruction,
return, future behavior, full menus, fixed supports and every specified
intermediate cut. The original analyzer acceptance interface and
$B_r$-to-active-ready connection mentioned in §§79.9 and 80.5 are not
constructed here. No additional bracketing, four-copy system, coherent
control, copying or infinite-dimensional consistency is supplied. The
fixed-carrier approximation result 80.5 still requires all its original
boundedness and noncollapse conditions (80.9); repair within C13 requires
80.6's additional whole-cone C13 premise. No noisy H13 bridge follows here.

Geometrically, a preparation is its original probability table and the cone
adds a mass coordinate to that same base. Bounded doubling concerns which
cuts of the base are actually present as tests. The tetrahedron shows that
identical least-confirmation numbers can conceal a missing cut. After full
effects and the fixed-half bridge, (17) measures cross-overlaps of positive
pieces in every complete frame. The current (17b) instead contracts the
same data against the fixed source projection: the existing nonnegative,
full-support average vanishes exactly when every frame has zero overlap.
Its moments preserve the common-frame correlation. The two mass laws use
the unit-fixed $R_A$, followed by the original anchor and same-state H13;
this is the simpler (81.14) entrance to the same complete model class.
Endpoint reciprocity exchanges two
arguments of a comparison; it differs from commuting successive physical
instruments. This reduces externally supplied geometry and expression,
without establishing fewer independent physical assumptions, least axioms,
lower experimental cost or a physical quantum origin.

可以把一个准备看成它面对所有原测试时给出的整张概率表，但原装置、菜单和记录仍然各自保留。只有这些原表本身允许实概率混合、形成有限维紧集合，才能从它们构造出这里的向量空间与带质量的正锥；取闭包不能替我们造出新准备。测试是否齐全还要另问：一个已有测试在所有原准备上的成功率都不超过一半时，是否有同一个原测试把这些数同时加倍？结合原混合与补测试，这恰好表达全效应可用性。四面体的两个菜单说明，纯参照对全部混态的最小确认数完全相同，仍能漏掉一个有界和。接回当前的完整候选 81.14 时，仍保留同一个读回用两次、原参考、两张成、全实零关系与全方向正性；但不必再搜索最坏框架，而把原几何固定的一个源投影与同一原映射导出的量作收缩。已有定理保证它为零恰好等于每套完整框架都零重叠，所以 80.14 的精确对应仍然保留。两条总质量关系现在采用由原单位固定的同一个数学见证，不另选局部变化；再用原锚校准倍率，最后才检查同一原混态的方向条件及其整个原输出。原过程还必须在保留输出质量的情况下尊重混合与等价关系，来源、参考、全菜单、时钟等义务也都保留。比较两端交换后数值相同，不等于两次仪器交换执行次序后状态相同。这使同一模型类的入口更简洁，不据此声称独立物理假设更少，也没有凭概率表生成仪器、来源、时钟或完整的物理量子起源。

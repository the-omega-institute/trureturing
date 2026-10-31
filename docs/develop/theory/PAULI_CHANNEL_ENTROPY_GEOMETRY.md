# Pauli-channel entropy geometry

## 1. Physical domain and shared definitions

**Definition 1.1 (States, channels, and entropy deficit).** Let $C,D$ be
qubits and let $I_2$ be the qubit identity. The Pauli matrices are

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

Write $AB=A\otimes B$ when the tensor factors are unambiguous and $I$
for the identity on the space in question. The source domain consists of
all actual complex Hermitian $4\times4$ matrices $\rho\geq0$ with
$\operatorname{tr}\rho=1$ on $\mathbb C_C^2\otimes\mathbb C_D^2$.
For independently variable $a,b\in[0,1]$, set

$$
\begin{aligned}
K&=XX,\qquad L=ZZ,\qquad \operatorname{Ad}_U(A)=UAU^*,\\
\Psi&=\frac{1+a}{2}\operatorname{id}+\frac{1-a}{2}\operatorname{Ad}_K,
&\Phi&=\frac{1+b}{2}\operatorname{id}+\frac{1-b}{2}\operatorname{Ad}_L,\\
\Gamma&=\Psi\Phi=\Phi\Psi,
&P&=\Phi\rho,\quad Q=\Psi\rho,\quad R=\Gamma\rho.
\end{aligned}
\tag{1.1}
$$

The conjugations commute, although the individual qubit axes differ.
For a density matrix $A$, define $S(A)=-\operatorname{tr}A\log A$, with
natural logarithms and $0\log0=0$, and write $A_E$ for the actual partial
trace to $E=C,D$. Put

$$
\begin{aligned}
\Delta(\rho)&=3S(R)-4S(P)-S(Q)
 +\sum_{E=C,D}\bigl[3S(P_E)+S(Q_E)-2S(R_E)\bigr],\\
F(\rho)&=3S(R)-4S(P)-S(Q),\\
\mathcal F_{\sigma,\tau}
 &=\{\rho\geq0:\operatorname{tr}\rho=1,\ \rho_C=\sigma,\ \rho_D=\tau\}.
\end{aligned}
\tag{1.2}
$$

With $\boldsymbol\sigma=(X,Y,Z)$, every source has the unique expansion

$$
\rho=\frac14\left[I+\sum_i u_i\sigma_i\otimes I
 +\sum_jv_j I\otimes\sigma_j
 +\sum_{i,j=x,y,z}T_{ij}\sigma_i\otimes\sigma_j\right].
\tag{1.3}
$$

All nine correlation coefficients $T_{ij}$ and all six marginal coordinates
$u_i,v_j$ are real; matrix entries need not be real. Positivity is imposed
on the complete complex matrix, with no rank, separability, axis, or
common-bias restriction. The margins are
$\sigma=(I+u\cdot\boldsymbol\sigma)/2$ and
$\tau=(I+v\cdot\boldsymbol\sigma)/2$.
Partial trace of a product Pauli conjugation is the corresponding local
Pauli conjugation. Thus $\Delta-F$ depends only on $(\sigma,\tau,a,b)$;
minimizing $F$ and $\Delta$ on a fixed-margin fiber is equivalent.

**Definition 1.2 (Exact entropy budget).** For $A=P,Q,R$, set
$I_A=S(A_C)+S(A_D)-S(A)$, and put

$$
\begin{aligned}
g&=S(R)-S(P),\qquad h_E=S(R_E)-S(P_E),\qquad h=h_C+h_D,\\
\Delta&=I_P+I_Q+3g-2h.
\end{aligned}
\tag{1.4}
$$

The last identity follows by grouping the terms in (1.2). The universal
assertion under consideration is $\Delta(\rho)\geq0$ on the whole domain
of Definition 1.1; the precise unresolved funding assertion is given in §9.

## 2. Rank-three optimization on full complex fixed-margin fibers

Fix

$$
r=\frac9{10},\quad \beta=\frac1{20},\quad a=b=\frac12,
 \qquad \sigma_\varepsilon=\frac{I+rY+\varepsilon X}{2}.
\tag{2.1}
$$

In the product $Y$ eigenbasis choose phases so that

$$
 Y=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
 X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
 Z=\begin{pmatrix}0&i\\-i&0\end{pmatrix}.
$$

This is a representation change of the actual channel matrices, not a
change of the channel axes. All nine real Pauli correlation coefficients
remain available; in particular tensors involving $Z$ encode imaginary
entries in this representation.

**Theorem 2.1 (Local support rotation and the diagonal restriction cost).**
There is $\varepsilon_0>0$ such that for every
$0<|\varepsilon|<\varepsilon_0$ the entire fiber
$\mathcal F_{\sigma_\varepsilon,\sigma_\varepsilon}$ has a unique
minimizer of $F$, equivalently of $\Delta$, denoted by
$\omega_\varepsilon$. It has rank three and positive
$P,Q,R$. Its complementary positive slack, in the sense

$$
M_{\omega_\varepsilon}=H_C I+I H_D+N_\varepsilon,
 \qquad N_\varepsilon\geq0,\quad
 N_\varepsilon\omega_\varepsilon=0,
\tag{2.2}
$$

is unique and nonzero; neither $N_\varepsilon$ nor
$\omega_\varepsilon$ commutes with either local marginal operator
$\sigma_\varepsilon I$ or $I\sigma_\varepsilon$.
Here $M$ is the trace-one gradient representative defined in
(2.5). The optimal source $C_\varepsilon$ diagonal in the
product marginal eigenbasis satisfies

$$
\Delta(C_\varepsilon)-\Delta(\omega_\varepsilon)
     =\gamma\varepsilon^2+O(\varepsilon^4),\qquad
 \gamma=\frac{D^2}{B+10m}>0.
\tag{2.3}
$$

All constants are specified exactly in (2.9), (2.17), and
(2.21). These properties, including strict loss from the diagonal
restriction, hold on a nonempty open subset of the eight real parameters
$(u,v,a,b)$, where the margins are $(I+u\cdot\boldsymbol\sigma)/2$ and
$(I+v\cdot\boldsymbol\sigma)/2$. This subset contains independently unequal biases.

### 2.1. Relative entropy and the global supporting inequality

Proof of Theorem 2.1. We use finite-dimensional relative-entropy joint
convexity and data processing, in their standard scope; see J. Watrous,
*The Theory of Quantum Information* (2018), DOI 10.1017/9781316848142.
The required mixed-unitary case and matrix derivatives can be obtained
inside this proof as follows.
For states $A$ and $B>0$ write
$D(A\Vert B)=\operatorname{tr} A\log A-\operatorname{tr} A\log B$.

For a mixed-unitary channel $T=\sum p_j\operatorname{Ad}_{U_j}$ and states
$A$, $B>0$,

$$
 D(TA\Vert TB)\leq D(A\Vert B),\qquad
 D(A\Vert B)\geq0,
$$

and the last equality holds exactly when $A=B$.
For $A>0$, a traceless Hermitian $H$, and the quadratic form

$$
 G_A(H)=\operatorname{tr} H\,\mathrm D\log_A[H],
$$

one has $G_{TA}(TH)\leq G_A(H)$, and $G_A$ is positive definite.

For the relative-entropy ingredient, proceed as follows.
For positive $A_i,B_i$, set $A=\sum p_iA_i$, $B=\sum p_iB_i$.
On the Hilbert--Schmidt matrix space let
$\mathscr D_i=L_{B_i}R_{A_i}^{-1}$ and
$\mathscr D=L_BR_A^{-1}$; left and right multiplication commute,
so these are positive operators. Define the isometry into a direct sum by

$$
 (VX)_i=\sqrt{p_i}\,X A^{-1/2}A_i^{1/2}.
$$

Direct multiplication gives $V^*V=I$ and
$V^*(\bigoplus\mathscr D_i)V=\mathscr D$.
For every positive operator $T$ and isometry $V$,

$$
 (V^*TV+sI)^{-1}\leq V^*(T+sI)^{-1}V\quad(s\geq0).
$$

For example this follows from the variational formula for an inverse
quadratic form by restricting its maximizing vector to $\operatorname{ran}V$.
Integrate this inequality using
$-\log t=\int_0^\infty[(t+s)^{-1}-(1+s)^{-1}]\mathrm d s$ to obtain
operator Jensen for $-\log$. Applying it to $A^{1/2}$ and using
$(VA^{1/2})_i=\sqrt{p_i}A_i^{1/2}$ proves

$$
 D(A\Vert B)\leq\sum_i p_iD(A_i\Vert B_i).
$$

Indeed $\log(L_BR_A^{-1})=L_{\log B}-R_{\log A}$, which identifies
the quadratic forms with the displayed relative entropies. Choose
$A_i=U_iAU_i^*$ and $B_i=U_iBU_i^*$ to get mixed-unitary contraction.
For singular $A$, replace it by $(1-\delta)A+\delta I/d$ and pass
to the limit; $B$ and $TB$ are positive and entropy is continuous.

For nonnegativity, diagonalize $A$ and $B$, with eigenvalues
$\lambda_i\geq0$, $\mu_j>0$ and overlap weights $c_{ij}$.
The doubly stochastic weights give

$$
 D(A\Vert B)=\sum_{ij}c_{ij}
 [\lambda_i\log(\lambda_i/\mu_j)-\lambda_i+\mu_j]\geq0.
$$

The scalar summand is zero exactly when $\lambda_i=\mu_j$.
Equality therefore implies that each eigenvector of $A$ belongs to
the eigenspace of $B$ with that same eigenvalue, hence $A=B$.

Using finite-dimensional matrix functional calculus (R. Bhatia,
*Matrix Analysis*, 1997, DOI 10.1007/978-1-4612-0653-8),
differentiating the resolvent formula for $\log$ gives

$$
 \mathrm D\log_A[H]=\int_0^\infty(A+sI)^{-1}H(A+sI)^{-1}\mathrm d s.
$$

In an eigenbasis of $A$,

$$
G_A(H)=\sum_{ij}|H_{ij}|^2\ell(\lambda_i,\lambda_j),\quad
 \ell(x,y)=\begin{cases}(\log x-\log y)/(x-y)&x\ne y,\\1/x&x=y.
 \end{cases}
\tag{2.4}
$$

Every coefficient is positive. Apply contraction to
$D(A+sH\Vert A)=s^2G_A(H)/2+O(s^3)$ for sufficiently small signed
$s$, using trace zero, to prove the metric inequality.

Where $P,Q,R>0$, the entropy objective is real analytic on the real
space of trace-one Hermitian matrices, whether the source is singular
or not. Its trace-one gradient representative is

$$
M_\omega=4\Phi(\log P_\omega)+\Psi(\log Q_\omega)
                  -3\Gamma(\log R_\omega).
\tag{2.5}
$$

The unrestricted gradient is $M_\omega+2I$; scalar identity terms
are local and do not affect any argument. The channels are self-adjoint
for the trace pairing. For every physical source $\rho$, even if its
outputs are singular, direct expansion gives

$$
\begin{aligned}
F(\rho)-F(\omega)-\operatorname{tr} M_\omega(\rho-\omega)
 &=4D(P_\rho\Vert P_\omega)+D(Q_\rho\Vert Q_\omega)
                           -3D(R_\rho\Vert R_\omega)\\
 &\geq D(P_\rho\Vert P_\omega)+D(Q_\rho\Vert Q_\omega)\geq0.
\end{aligned}
\tag{2.6}
$$

All second arguments are positive, so these are finite relative
entropies and mixed-unitary contraction applies without an input-support gap.
If $b>0$, $\Phi$ is an invertible real linear map: its eigenvalues
on the commuting and anticommuting operator subspaces are $1,b$.
Thus the right side is strictly positive for $\rho\ne\omega$.
Consequently a positive-output reference satisfying (2.2)
is the unique global minimizer on its fiber, since its local term pairs
to zero with $\rho-\omega$, and
$\operatorname{tr} N(\rho-\omega)=\operatorname{tr} N\rho\geq0$.

For completeness, the ambient second derivative on trace-zero directions is

$$
F''_\rho[H,H]=4G_P(\Phi H)+G_Q(\Psi H)-3G_R(\Gamma H)
 \geq G_P(\Phi H)+G_Q(\Psi H)>0\quad(H\ne0,b>0).
\tag{2.7}
$$

Here $\Gamma H=\Psi(\Phi H)$, so the first metric contraction alone
pays the three subtracted terms. On segments of positive-output states
this proves convexity. For arbitrary physical endpoints replace both by
their mixtures with $I/4$; the whole regularized segment has positive
outputs. Let the mixing tend to zero and use entropy continuity to prove
convexity of $F$ on the entire physical state set. This also justifies
one-dimensional convexity when a diagonal competitor has singular outputs.

### 2.2. Exact base point and analytic rank-three continuation

Let $v_0=|--\rangle_Y$. At (2.1), set

$$
 \omega_0=\frac14[I+r(YI+IY)+\tfrac45YY]
     =\operatorname{diag}(r,\beta,\beta,0).
$$

Both $K$ and $L$ interchange the double-plus and double-minus
probabilities and interchange the equal middle probabilities. Therefore

$$
P_0=Q_0=\operatorname{diag}(27/40,1/20,1/20,9/40),\quad
 R_0=\operatorname{diag}(9/16,1/20,1/20,27/80).
\tag{2.8}
$$

Write $p_+,p_-,p_0$ and $q_+,q_-,q_0$ for the respective large,
last, and middle values in this equation. The coefficient of $YY$ in
the diagonal logarithm is one fourth the log of the ratio of the product
of its first and last probabilities to the product of its middle ones.
Since the channels fix $YY$, the $YY$ coefficient of $M_0$ is

$$
m=\frac14[5\log(243/4)-3\log(1215/16)]
       =\frac14\log(236196/125)>0.
\tag{2.9}
$$

More explicitly, let

$$
 c_P=\tfrac14\log(p_+p_-p_0^2),\quad
 c_R=\tfrac14\log(q_+q_-q_0^2),\quad g_0=5c_P-3c_R,
$$

$$
 g_1=\tfrac58\log3-\tfrac3{16}\log(5/3).
$$

The logarithms have equal coefficients on $YI,IY$, and the channels
multiply each such coefficient by $1/2$ and $1/4$, respectively.
Thus the exact gradient is

$$
 M_0=g_0I+g_1(YI+IY)+mYY.
$$

As $4v_0v_0^*=I-YI-IY+YY$, it follows that

$$
M_0=(g_0-m)I+(g_1+m)(YI+IY)+4m v_0v_0^*.
\tag{2.10}
$$

The last term is PSD and annihilates $\omega_0$. Equation
(2.6) proves uniqueness over the full complex fiber directly.

We now prove an analytic continuation with no omitted correlation
coordinates. Parametrize all trace-one Hermitian matrices by (1.3).
All fifteen coefficients in (1.3) are real; they parametrize the complete
Hermitian space. Put $z=(T_{ij})_{(i,j)\ne(y,y)}$.
At the base, $\operatorname{adj}\omega_0=r\beta^2v_0v_0^*$, so

$$
\frac{\partial\det\rho}{\partial T_{yy}}\bigg|_0
    =\frac{r\beta^2}{4}>0.
\tag{2.11}
$$

The real analytic implicit function theorem (S. G. Krantz and
H. R. Parks, *The Implicit Function Theorem: History, Theory, and
Applications*, 2002) gives a chart
$T_{yy}=\theta(u,v,z)$ of $\det\rho=0$ on an open neighborhood.
Its other three eigenvalues remain positive; its fourth is zero.
Every point in this chart is therefore an actual rank-three PSD state.
The margins remain positive and all three channel outputs remain positive
after shrinking the neighborhood. This follows from the strictly positive
base eigenvalues, and is valid also for independently perturbed $a,b$.

The constrained Hessian must include the curvature of this chart.
For a rank-three curve $\rho(s)$ through $\omega_0$ with tangent $H$,
choose a unit kernel vector with $\langle v_0,v'_0\rangle=0$.
Differentiating $\rho(s)v(s)=0$ yields

$$
 \langle v_0,Hv_0\rangle=0,\qquad
 v'_0=-\omega_0^+Hv_0,\qquad
 \langle v_0,\rho''(0)v_0\rangle
    =2\langle Hv_0,\omega_0^+Hv_0\rangle,
$$

where $\omega_0^+$ is the inverse on the three-dimensional support
and zero on the kernel. For curves whose margins are affine in $s$,
the local part of (2.10) pairs to zero with $\rho''(0)$.
Consequently their actual second derivative is

$$
\mathcal H(H)=F''_{\omega_0}[H,H]
                  +8m\langle Hv_0,\omega_0^+Hv_0\rangle.
\tag{2.12}
$$

In particular this is positive definite on the eight fixed-margin
tangents $\partial_z\rho$ by (2.7). At the base
$\partial_z\theta=0$, since all these correlation tensors have zero
$v_0$ diagonal entry, so these are eight independent tangents.

Apply analytic IFT to the eight equations
$\partial_z F(\rho(u,v,z);a,b)=0$. Their derivative in $z$ is the
invertible positive Hessian just proved. We obtain a real analytic
$z=z_*(u,v,a,b)$ and hence an analytic rank-three source $\omega(p)$,
where $p=(u,v,a,b)$ varies in a full open subset of $\mathbb R^8$.
To prove that this stationary chart solution is the global optimizer,
let $\Pi(p)$ be its kernel projection. It is analytic, for example by

$$
 \Pi(p)=\frac{\operatorname{adj}\omega(p)}
                    {\operatorname{tr}\operatorname{adj}\omega(p)}.
$$

The fixed-margin tangent space has dimension nine; its rank-three
subspace is the kernel of $H\mapsto\operatorname{tr}\Pi(p)H$ and has dimension
eight. Stationarity implies

$$
M_{\omega(p)}-\lambda(p)\Pi(p)\quad\text{is local}.
\tag{2.13}
$$

This is precisely the orthogonal complement statement for the full
nine-dimensional correlation space in (1.3). An explicit analytic
coefficient is

$$
 \lambda(p)=\frac{\operatorname{tr}(M_{\omega(p)}YY/4)}{\operatorname{tr}(\Pi(p)YY/4)}.
$$

The denominator equals $1/4$ at the base and stays nonzero; the numerator
equals $m$ there. Hence $\lambda(p)\to4m>0$. Shrink the neighborhood
so $\lambda>0$ and $0<a,b<1$. Now
$N(p)=\lambda(p)\Pi(p)$ is an actual complementary PSD slack.
Equation (2.6) proves global optimality and uniqueness against
every physical competitor, with every rank and every complex correlation.
We did not assume those competitors had positive outputs or lay in the
chart. This proves all analytic and global hypotheses needed for the
continuation assertion.

### 2.3. Full tangent and its coefficients

Specialize the analytic optimizer to the signed family
$u=v=(\varepsilon,r,0)$, $a=b=1/2$. Its uniqueness implies covariance
under swap, transpose in the displayed $Y$ representation, and $U=YY$.
Both $K=XX$ and $L=ZZ$ are real in this representation, so transpose
really does intertwine the channels and preserve the entropy objective.
Swap and transpose preserve these margins, while $U$ sends their
$\varepsilon$ to $-\varepsilon$. It follows that

$$
 \omega_{-\varepsilon}=U\omega_\varepsilon U^*.
$$

At first order, the odd tensors under $U$ have exactly one transverse
factor $X$ or $Z$. Transpose removes the single-$Z$ tensors, and swap
equates the remaining two correlation coefficients. The prescribed
margins fix the two local $X$ coefficients. Thus, as a consequence of
uniqueness in the full problem,

$$
\omega_\varepsilon=\omega_0+\varepsilon H(t_*)+O(\varepsilon^2),
 \qquad H(t)=\tfrac14[XI+IX+t(XY+YX)].
\tag{2.14}
$$

No symmetry subspace was imposed during optimization.

For a diagonal matrix with probabilities $(p_+,\beta,\beta,p_-)$,
the only nonzero upper-triangular entries of
$H(x,y)=[x(XI+IX)+y(XY+YX)]/4$ are

$$
 H_{12}=H_{13}=(x+y)/4,\qquad
 H_{24}=H_{34}=(x-y)/4.
$$

Counting also their transposes in (2.4) gives exactly

$$
G_P(H(x,y))=\mathcal G_h(x,y)
 =\tfrac14[(x+y)^2h_++(x-y)^2h_-],
\tag{2.15}
$$

where

$$
 h_+=\tfrac85\log(27/2),\quad h_-=\tfrac{40}7\log(9/2),\qquad
 j_+=\tfrac{80}{41}\log(45/4),\quad
 j_-=\tfrac{80}{23}\log(27/4)
$$

are respectively the divided differences for $(P_0,R_0)$ against $\beta$.
For instance $p_+-\beta=5/8$ and $q_+-\beta=41/80$.
The actual channel actions on this tangent are

$$
 \Phi H(t)=H(1/2,t),\quad \Psi H(t)=H(1,t/2),\quad
 \Gamma H(t)=H(1/2,t/2).
$$

Indeed $\Phi$ multiplies the local $X$ by $b$ and fixes $XY,YX$;
$\Psi$ fixes local $X$ and multiplies these correlations by $a$.
Substitution gives, with a constant $C_0$ independent of $t$,

$$
\begin{aligned}
F''[H(t),H(t)]
 &=4\mathcal G_h(1/2,t)+\mathcal G_h(1,t/2)
                                      -3\mathcal G_j(1/2,t/2)\\
 &=C_0+4At+2Bt^2,
\end{aligned}
\tag{2.16}
$$

where explicitly

$$
A=\tfrac18[\tfrac52(h_+-h_-)-\tfrac34(j_+-j_-)],\qquad
 B=\tfrac18[\tfrac{17}4(h_++h_-)-\tfrac34(j_++j_-)].
\tag{2.17}
$$

Here $C_0=(h_++h_-)/2-3(j_++j_-)/16$.
The coefficient $2B$ is $F''[E,E]$ for $E=(XY+YX)/4$, so
$B>0$ follows independently from (2.7).

Since $H(t)v_0=(1-t)(|+-\rangle+|-+\rangle)/4$ and the two
support eigenvalues concerned are $\beta=1/20$, the curvature term is

$$
 8m\langle H(t)v_0,\omega_0^+H(t)v_0\rangle=20m(1-t)^2.
$$

The true second-derivative polynomial is therefore

$$
J(t)=C_0+4At+2Bt^2+20m(1-t)^2.
\tag{2.18}
$$

Differentiating the chart stationarity equations along the moving
margins says that their first-order tangent minimizes this quadratic
form over the affine space of allowed tangents. Equivalently the
bilinear form associated to (2.12) pairs its tangent to
zero with every fixed-margin tangent. In particular $J'(t_*)=0$.
Since $B+10m>0$, this yields

$$
t_* =\frac{10m-A}{B+10m},\qquad
 J(t)-J(t_*)=2(B+10m)(t-t_*)^2.
\tag{2.19}
$$

This derivation accounts for the analytic PSD constraint, rather than
minimizing the ambient quadratic alone.

### 2.4. Marginal diagonal optimum, logarithmic bound, and cost

Let $R_\varepsilon=\sqrt{r^2+\varepsilon^2}$ and
$n_\varepsilon=(rY+\varepsilon X)/R_\varepsilon$. For
$|\varepsilon|<\sqrt{19}/10$, the margins are positive and have distinct
eigenvalues. All sources diagonal in their product eigenbasis are exactly

$$
\rho_\varepsilon(c)=\tfrac14[I+R_\varepsilon(n_\varepsilon I+In_\varepsilon)
                              +c\,n_\varepsilon n_\varepsilon],
 \qquad 2R_\varepsilon-1\leq c\leq1.
\tag{2.20}
$$

These bounds follow by writing its four probabilities
$(1+2R+c,1-c,1-c,1-2R+c)/4$.
At $(\varepsilon,c)=(0,2r-1)$ the derivative of $F$ in $c$ is
$\operatorname{tr} M_0YY/4=m>0$. The endpoint and its outputs vary analytically,
so this endpoint derivative stays positive for all sufficiently small
signed $\varepsilon$. Convexity on the whole interval, including its
possibly singular-output end, proves that its unique minimum is

$$
 C_\varepsilon=\rho_\varepsilon(2R_\varepsilon-1).
$$

It is analytic, rank three, and has first tangent $H(t_c)$ with

$$
 t_c=\frac{2r-1}{r}=\frac89.
$$

Define

$$
\begin{aligned}
D&=A+\tfrac89B-\tfrac{10}9m\\
  &=\tfrac{113}{90}\log(27/2)+\tfrac{115}{126}\log(9/2)
     -\tfrac{85}{246}\log(45/4)+\tfrac5{138}\log(27/4)
     -\tfrac5{18}\log(236196/125).
\end{aligned}
\tag{2.21}
$$

The identity follows by expanding (2.17), with the five logarithms
kept as separate symbols. The following strict bound holds:

$$
D>\frac{8191}{10332}>0.
\tag{2.22}
$$

Indeed $8/3<e<11/4$: the first inequality follows from the terms through
$1/3!$ and a positive tail, and for the second the terms through $1/4!$
sum to $65/24$, with remaining tail at most
$(1/120)\sum_{k\geq0}6^{-k}=1/100$.
The exact rational comparisons

$$
 (11/4)^5<(27/2)^2,\quad 11/4<9/2,\quad
 (8/3)^3>45/4,\quad 27/4>1,\quad
 (8/3)^8>236196/125
$$

give, respectively,

$$
 \log(27/2)>5/2,\quad\log(9/2)>1,\quad
 \log(45/4)<3,\quad\log(27/4)>0,\quad
 \log(236196/125)<8.
$$

Using the correct signs of all five coefficients in (2.21) yields

$$
 D>\frac{113}{90}\frac52+\frac{115}{126}
                       -\frac{85}{246}3-\frac5{18}8
    =\frac{8191}{10332}.
$$

In particular

$$
t_c-t_* =\frac{D}{B+10m}>0,\qquad
 \gamma=(B+10m)(t_c-t_*)^2=\frac{D^2}{B+10m}>0.
\tag{2.23}
$$

Both rank-three paths have the same affine margins and base point.
Their first derivatives in $F$ are equal by (2.10), since
$\langle v_0,H(t)v_0\rangle=0$. Their actual second derivatives are
$J(t_c)$ and $J(t_*)$, respectively. Taylor expansion and
(2.19) therefore give the coefficient $\gamma$ in (2.3).
To establish its asserted remainder, note that all paths and all their
outputs are real analytic for signed $\varepsilon$ in an open interval
about zero; the output spectra are bounded away from zero on a smaller
closed interval. The conjugation by $U=YY$ relates the two signs for
both $C$ and $\omega$, so both objective values are even analytic
functions. The cubic term and every other odd term vanish. This proves
$O(\varepsilon^4)$, with a finite uniform remainder constant after
shrinking the interval. Since $\Delta-F$ is the same on the fiber, the
claim holds for $\Delta$ as well. In particular the gap is at least
$\gamma\varepsilon^2/2$ for sufficiently small nonzero $\varepsilon$.

### 2.5. An explicit physical comparison source

Fix any real $t$ and put $u_t=(1+t)/4$, $w_t=(1-t)/4$.
For sufficiently small signed $\varepsilon$, let $q=q_t(\varepsilon^2)$
be the small root near zero of

$$
f(q,s)=(r+q)[q(\beta-q)-2w_t^2s]-2u_t^2sq=0,
 \qquad s=\varepsilon^2.
\tag{2.24}
$$

This specifies an unambiguous analytic branch: $f(0,0)=0$ and
$f_q(0,0)=r\beta>0$, so IFT gives the unique root in a neighborhood
of $(q,s)=(0,0)$. It is analytic jointly in $(s,t)$ locally at each
finite $t$, and the construction and estimates can be made uniform
on any fixed compact interval of $t$ by shrinking $|\varepsilon|$.
Implicit differentiation gives

$$
q_t(\varepsilon^2)=\frac{2w_t^2}{\beta}\varepsilon^2
                       +O(\varepsilon^4)
    =\frac52(1-t)^2\varepsilon^2+O(\varepsilon^4).
\tag{2.25}
$$

Define the actual matrix

$$
W_\varepsilon(t)=
 \begin{pmatrix}
 r+q&u_t\varepsilon&u_t\varepsilon&0\\
 u_t\varepsilon&\beta-q&0&w_t\varepsilon\\
 u_t\varepsilon&0&\beta-q&w_t\varepsilon\\
 0&w_t\varepsilon&w_t\varepsilon&q
 \end{pmatrix}.
\tag{2.26}
$$

Positivity follows by a Schur complement.
The antisymmetric middle vector has eigenvalue $\beta-q>0$.
On $\{|++\rangle,(|+-\rangle+|-+\rangle)/\sqrt2,|--\rangle\}$
the block is

$$
 \begin{pmatrix}r+q&\sqrt2u_t\varepsilon&0\\
 \sqrt2u_t\varepsilon&\beta-q&\sqrt2w_t\varepsilon\\
 0&\sqrt2w_t\varepsilon&q\end{pmatrix}.
$$

Its leading $2\times2$ block $A$ is positive for small
$|\varepsilon|$, since at zero it is $\operatorname{diag}(r,\beta)$.
The determinant of the three-dimensional block is
$f(q,\varepsilon^2)=0$. Its Schur complement over $A$ is
therefore exactly zero, explicitly

$$
 q-\frac{2w_t^2\varepsilon^2(r+q)}
                 {(r+q)(\beta-q)-2u_t^2\varepsilon^2}=0.
$$

Thus the three-dimensional block is PSD of rank two and the complete
$W$ is PSD of rank three. This also proves $q\geq0$ on the physical
branch, including $q=0$ when $t=1$. Its trace is
$r+2\beta=1$. Either partial trace has diagonal entries
$(r+\beta,\beta)$ and off-diagonal entry
$(u_t+w_t)\varepsilon=\varepsilon/2$; hence both are exactly
$\sigma_\varepsilon$. Positive outputs follow by continuity from
(2.8). Its tangent is $H(t)$, so (2.12) or
(2.25) gives actual second derivative $J(t)$.

The root depends on $\varepsilon^2$ and
$UW_\varepsilon(t)U^*=W_{-\varepsilon}(t)$. Its objective is therefore
even analytic, with the same signed-domain justification used above.
For $t=t_*$ this proves

$$
\Delta(C_\varepsilon)-\Delta(W_\varepsilon(t_*))
      =\gamma\varepsilon^2+O(\varepsilon^4),\qquad
 0\leq F(W_\varepsilon(t_*))-F(\omega_\varepsilon)=O(\varepsilon^4).
\tag{2.27}
$$

The second inequality follows from global optimality, and its order
from the equal tangent, equal second derivative, and even analyticity.
The explicit comparison source is not asserted to equal the optimizer
at fourth or higher order. In particular any bound $L$ valid on the
whole physical fiber must obey

$$
 L(1/2,1/2,\sigma_\varepsilon,\sigma_\varepsilon)
       \leq\Delta(C_\varepsilon)-\frac\gamma2\varepsilon^2
 \quad(0<|\varepsilon|<\varepsilon_0)
$$

after a further reduction of $\varepsilon_0$.

### 2.6. Kernel rotation, unique slack, and the eight-parameter open set

Choose the analytic unit kernel vector $v_\varepsilon$ with positive
overlap with $v_0$. This is possible by normalizing
$\Pi_\varepsilon v_0$, which is nonzero near zero; the transpose
symmetry also allows it to be real in the displayed basis.
Differentiating its kernel equation gives exactly

$$
v'_0=-5(1-t_*)(|+-\rangle+|-+\rangle).
\tag{2.28}
$$

By differentiating the single-qubit marginal eigenvalue equation, its
negative eigenvector has derivative $-|+\rangle/(2r)=-5|+\rangle/9$.
Thus the double-negative product eigenvector has derivative
$-5(|+-\rangle+|-+\rangle)/9$. Equations (2.23) and
(2.28) show that these rotations differ. To verify the stronger
assertion for each marginal separately, rather than merely their joint
eigenbasis, put $e_2=|+-\rangle$, $e_3=|-+\rangle$, $e_4=|--\rangle$.
Direct differentiation of the commutators gives

$$
\begin{aligned}
\langle e_2,[\Pi_\varepsilon,\sigma_\varepsilon I]e_4\rangle
    &=\tfrac12(8-9t_*)\varepsilon+O(\varepsilon^2),\\
 \langle e_2,[\omega_\varepsilon,\sigma_\varepsilon I]e_4\rangle
    &=\tfrac1{40}(9t_*-8)\varepsilon+O(\varepsilon^2).
\end{aligned}
\tag{2.29}
$$

For the other local marginal replace $e_2$ by $e_3$; swap gives the
same coefficients. Since $8-9t_*=9D/(B+10m)>0$, these entries are
nonzero for all sufficiently small nonzero signed $\varepsilon$.
The same holds for $N_\varepsilon=\lambda_\varepsilon\Pi_\varepsilon$
because $\lambda_\varepsilon>0$.

It remains to justify that another saturated PSD slack cannot avoid
this conclusion. At any rank-three optimizer every PSD matrix $N$
with $N\omega=0$ is a nonnegative multiple of its kernel projection.
If two such matrices satisfy (2.2), their difference is
local and is a scalar multiple of that rank-one projection. A nonzero
local Hermitian operator $A I+I B$ cannot have rank one: its four
eigenvalues are $a_i+b_j$, and any three zero entries in this
$2\times2$ additive array force the fourth zero. Hence the difference
vanishes and the slack is unique. The individual fields still have the
irrelevant scalar gauge $H_C\mapsto H_C+cI$, $H_D\mapsto H_D-cI$.

For clarity we also verify persistence of the diagonal comparison,
not just persistence of noncommutation. In the full parameter
neighborhood of the IFT, let $U_0=\|u\|$, $V_0=\|v\|$ and
$n_u=u\cdot\boldsymbol\sigma/U_0$, $n_v=v\cdot\boldsymbol\sigma/V_0$.
These are analytic because the radii stay positive and less than one.
All marginal-diagonal sources have correlation $c n_u n_v$, with

$$
 U_0+V_0-1\leq c\leq1-|U_0-V_0|.
$$

At the lower endpoint their probabilities are
$((U_0+V_0)/2,(1-V_0)/2,(1-U_0)/2,0)$.
This endpoint source $C(p)$ is analytic and positive-output near the
base; the derivative of $F$ with respect to $c$ is positive there
by continuity from $m>0$. Global convexity again makes it the unique
diagonal optimum for every nearby parameter, independently of $a,b$.
At any fixed sufficiently small $\varepsilon_1\ne0$, the analytic
gap $F(C(p))-F(\omega(p))$ is strictly positive by (2.3),
and the four commutators in (2.29) are nonzero.
Positivity of the gap, positive outputs, positive $\lambda$, and these
nonzero commutators all persist on an open neighborhood of that point
in all eight parameters. The construction already maintains exact
rank three throughout this neighborhood. Taking it inside
$0<a,b<1$ proves the stated independent-bias open set, including points
with $a\ne b$, and allows all six marginal coordinates to vary.

### 2.7. Sharp and conservative fiber certificates

The noncommutation in Theorem 2.1 concerns a saturated complementary PSD
slack at the true optimum. A conservative local certificate can instead
use $N=0$ and the scalar local field $\lambda_{\min}(M_\omega)I$:
$M_\omega\geq\lambda_{\min}(M_\omega)I$. The supporting inequality
(2.6) then gives a valid fiber lower bound. Saturation requires
equality at the optimizer; the unique noncommuting slack prevents a
saturated marginal-diagonal slack in the family above. A marginal-diagonal
restricted optimization value is an upper bound on the full fiber minimum,
with the strict loss (2.3), and is not by itself a lower certificate.
This completes the proof of Theorem 2.1.

## 3. All-domain support-aware BKM covariance funding

**Definition 3.1 (Supported path and covariance).** For $0\leq t\leq1$, define

$$
A_t=\frac{1+t}{2}P+\frac{1-t}{2}KPK,
 \qquad H=\frac{P-KPK}{2}.
\tag{3.1}
$$

Then $A_1=P$, $A_a=R$, and $A_t'=H$.  For $t<1$,

$$
 \operatorname{supp} A_t=\operatorname{supp}(P+KPK)=:{\cal S},
$$

and $A_t$ is positive definite on ${\cal S}$; $H$ is supported on
${\cal S}$.  The endpoint $t=1$ may be singular. Every BKM quantity below is used
pointwise only for $0\leq t<1$, on the fixed support $\mathcal S$.
An integral written with upper endpoint $1$ means its improper limit from
below, and any singular-support endpoint statement means that support
limit. No finite pointwise BKM value at $t=1$ is asserted.

For a density matrix $A$ that is positive on its support, define

$$
 \Omega_A(B)=\int_0^1A^sBA^{1-s}\,ds,
 \qquad
 \mathcal K_A(B,C)=\operatorname{Re}\operatorname{tr}\bigl(B^\circ\Omega_A(C^\circ)\bigr),
$$

where $B^\circ=B-\operatorname{tr}(AB)I$ and the identity is understood on the
support.  In an eigenbasis of $A$,

$$
 \Omega_A(B)_{ij}=L(\lambda_i,\lambda_j)B_{ij},\qquad
 L(x,y)=\begin{cases}
 (x-y)/(\log x-\log y),&x,y>0,\ x\ne y,\\
 x,&x=y>0,\\
 0,&xy=0.
 \end{cases}
$$

Let

$$
 G_A(D)=\operatorname{tr} D\,\mathrm D\log_A[D]
$$

for supported Hermitian trace-zero $D$.  The logarithmic-mean covariance and its inverse metric are standard
BKM constructions; see D. Petz, *Covariance and Fisher information in
quantum mechanics*, arXiv:quant-ph/0106125. The inverse relation between
$\Omega_A$ and $\mathrm D\log_A$ gives, within the covariance argument,
the variational identity

$$
G_A(D)=\sup_{B=B^*}\{2\operatorname{tr}(DB)-\mathcal K_A(B,B)\}.
\tag{3.2}
$$

At a singular ambient state all expressions in this identity are taken on
its support.  If a linear combination of observables has zero centered
$\mathcal K_A$ norm, it is scalar on the support and hence pairs to zero with
any supported trace-zero $D$.  Thus every expectation-derivative vector
belongs to the range of the corresponding covariance Gram matrix, which
justifies Moore--Penrose inverses below.

Write the six local observables as

$$
 (O_1,\ldots,O_6)=(XI,YI,ZI,IX,IY,IZ),
$$

and set

$$
V_t=[\mathcal K_{A_t}(O_i,O_j)]_{i,j=1}^6
 =\begin{pmatrix}V_C&B_t\\ B_t^{\mathsf T}&V_D\end{pmatrix},
 \qquad d_t=\binom{p'(t)}{q'(t)},
\tag{3.3}
$$

where $p(t),q(t)$ are the Bloch vectors of $A_{t,C},A_{t,D}$.
For any unit vectors $n_0,m_0\in\mathbb R^3$, let

$$
 W=(n_0\cdot\boldsymbol\sigma)\otimes(m_0\cdot\boldsymbol\sigma),
\quad z_t=(\mathcal K_{A_t}(O_i,W))_{i=1}^6,
\quad v_t=\mathcal K_{A_t}(W,W),\quad e_t=\operatorname{tr}(HW).
$$

Define the support-aware residual

$$
\mathcal R_t=\begin{cases}
 \displaystyle\frac{(e_t-z_t^{\mathsf T}V_t^+d_t)^2}
 {v_t-z_t^{\mathsf T}V_t^+z_t},&v_t-z_t^{\mathsf T}V_t^+z_t>0,\\[3mm]
 0,&v_t-z_t^{\mathsf T}V_t^+z_t=0.
 \end{cases}
\tag{3.4}
$$

The second case uses both the PSD Gram matrix and the actual augmented
tangent expectation vector. If

$$
 \widehat V_t=\begin{pmatrix}V_t&z_t\\z_t^{\mathsf T}&v_t\end{pmatrix},
 \qquad \widehat d_t=\binom{d_t}{e_t},
$$

then $\widehat d_t\in\operatorname{ran}\widehat V_t$ by the zero-norm
pairing argument above applied to all seven observables. PSD alone does
not imply the required residual pairing is zero. When the Schur
complement vanishes, the coefficient vector
$(-V_t^+z_t,1)$ is in $\ker\widehat V_t$; its pairing with
$\widehat d_t$ vanishes. Thus $e_t-z_t^{\mathsf T}V_t^+d_t=0$.

**Proposition 3.2 (Augmented Schur-residual bound).**
For every $0\leq t<1$,

$$
G_{A_t}(H)\geq d_t^{\mathsf T}V_t^+d_t+\mathcal R_t.
\tag{3.5}
$$

Its use at the entropy endpoint is solely through the improper
integrals and support limits specified in Definition 3.1.

Proof.
The Gram matrix

$$
 \begin{pmatrix}V_t&z_t\\z_t^{\mathsf T}&v_t\end{pmatrix}
$$

is positive semidefinite.  Orthogonally project the centered $W$ onto
the span of the six centered local observables.  The residual has squared
norm $v_t-z_t^{\mathsf T}V_t^+z_t$ and score pairing
$e_t-z_t^{\mathsf T}V_t^+d_t$.  Applying (3.2) to the
local span and then to this orthogonal residual proves (3.5).
The range statements for both $V_t$ and $\widehat V_t$ handle
singular local Gram matrices and the zero-Schur case.

For a qubit with Bloch vector $p=rn$, define its centered qubit BKM
matrix in the Pauli basis by

$$
\mathcal Q_p=\frac r{\operatorname{atanh}r}(I-nn^{\mathsf T})
 +(1-r^2)nn^{\mathsf T},
\tag{3.6}
$$

with continuous values $\mathcal Q_0=I$ and $\mathcal Q_p=0$ for $r=1$.  Actual
partial trace is a CPTP map. Using standard CPTP relative-entropy
data processing (Watrous, *The Theory of Quantum Information*), and
differentiating it at a
state and a supported trace-zero tangent gives

$$
G_{A_{t,C}}(D_C)\leq G_{A_t}(D),
 \qquad G_{A_{t,D}}(D_D)\leq G_{A_t}(D).
\tag{3.7}
$$

Using (3.2) in the dual direction yields

$$
V_C\leq\mathcal Q_{p(t)},\qquad V_D\leq\mathcal Q_{q(t)}.
\tag{3.8}
$$

No faithfulness is needed: take the supported limit if a marginal is
singular.  Positivity of $V_t$ and (3.8) imply, for all
$x,y$,

$$
 |x^{\mathsf T}B_ty|^2
 \leq(x^{\mathsf T}\mathcal Q_{p(t)}x)(y^{\mathsf T}\mathcal Q_{q(t)}y).
$$

Consequently the normalized full cross operator

$$
\kappa_t=\left\|(\mathcal Q_{p(t)}^+)^{1/2}B_t
 (\mathcal Q_{q(t)}^+)^{1/2}\right\|_{\mathrm{op}}
\tag{3.9}
$$

obeys $0\leq\kappa_t\leq1$, with the range inclusions supplied by the
same inequality.  In particular,

$$
 V_t\leq(1+\kappa_t)\operatorname{diag}(\mathcal Q_{p(t)},\mathcal Q_{q(t)}).
$$

The variational formula, applied to this order rather than by blindly
inverting matrices, gives

$$
d_t^{\mathsf T}V_t^+d_t
 \geq\frac{s_t}{1+\kappa_t},
 \qquad
 s_t=p'(t)^{\mathsf T}\mathcal Q_{p(t)}^+p'(t)
 +q'(t)^{\mathsf T}\mathcal Q_{q(t)}^+q'(t).
\tag{3.10}
$$

If a marginal is pure at an interior point, the convex path forces its
derivative to be zero, so no undefined inverse is being used.

Since $KA_tK=A_{-t}$ after extending the path to negative $t$, entropy
is even and $S'(A_t)|_{t=0}=0$.  Two integrations of
$S''(A_t)=-G_{A_t}(H)$ give

$$
S(R)-S(P)=\int_0^1w_a(t)G_{A_t}(H)\,dt,
 \qquad
 w_a(t)=\begin{cases}1-a,&0\leq t\leq a,\\1-t,&a<t\leq1.
 \end{cases}
\tag{3.11}
$$

The same calculation for both partial traces gives

$$
h=\int_0^1w_a(t)s_t\,dt.
\tag{3.12}
$$

For a singular $P$, first perform both integrations with an upper endpoint
$T<1$, with weights $w_{a,T}(t)=T-a$ for $0\leq t\leq a$ and
$w_{a,T}(t)=T-t$ for $a<t\leq T$ (when $a<1$ and $T>a$).
These nonnegative weights increase to $w_a$ as $T\uparrow1$.
Monotone convergence of the nonnegative curvature integrals and entropy
continuity give the stated improper identities. If $a=1$, both entropy
gains and both weighted integrals are zero. In particular the endpoint
argument assigns no finite pointwise value to $G_{A_1}(H)$ or $s_1$.  Substitution of
(3.5), (3.11), and (3.12)
into (1.4) proves the main all-domain estimate.

**Theorem 3.3 (All-domain covariance funding).**
For every complex PSD trace-one $\rho$ and every $a,b\in[0,1]$,

$$
\boxed{\Delta\ge I_P+I_Q+
 \int_0^1w_a(t)\bigl[3d_t^{\mathsf T}V_t^+d_t+3\mathcal R_t-2s_t\bigr]dt.}
\tag{3.13}
$$

Moreover,

$$
\boxed{d_t^{\mathsf T}V_t^+d_t\ge\frac{s_t}{1+\kappa_t}},
\tag{3.14}
$$

and hence

$$
\boxed{\Delta\ge I_P+I_Q+\int_0^1w_a(t)
 \left[\frac{1-2\kappa_t}{1+\kappa_t}s_t+3\mathcal R_t\right]dt.}
\tag{3.15}
$$

In particular, if $\kappa_t\leq1/2$ for $w_a(t)s_t\,dt$-almost every
$t$, then $\Delta\ge I_P+I_Q\geq0$.

Proof.
Equation (3.13) is exactly the substitution described above;
(3.14) is (3.10); and (3.15) follows by inserting
(3.14).  Mutual information is relative entropy to a product
state, so $I_P,I_Q\geq0$.  All endpoint statements are the improper integral or support limits of
Definition 3.1, preserving all stated quantifiers. The nonnegative
Schur bound is bounded by the integrable global curvature; moreover
$0\leq s_t\leq2G_{A_t}(H)$ by metric DPI, so the signed integrals
in these estimates are well defined.

## 4. Entropy-compatible PSD correlation funding

**Definition 4.1 (Affine correlation reference and PSD witnesses).**
The channel multipliers in (1.3) are

$$
 \ell=(b,b,1),\qquad k=(1,a,a),
$$

and, with rows and columns ordered $x,y,z$,

$$
(\ell_{ij})=\begin{pmatrix}1&1&b\\1&1&b\\b&b&1\end{pmatrix},\qquad
 (k_{ij})=\begin{pmatrix}1&a&a\\a&1&1\\a&1&1\end{pmatrix}.
\tag{4.1}
$$

Let $w_{ij}=\ell_{ij}^2+k_{ij}^2$ and
$\mathcal J=\{(i,j):w_{ij}>0\}$.  For the actual source margins
$u,v$, define an affine Hermitian trace-one matrix $\rho_0$ by the same
margins and by

$$
T^0_{ij}=\frac{\ell_{ij}\ell_i\ell_j+k_{ij}k_i k_j}{w_{ij}}u_iv_j
 \quad((i,j)\in\mathcal J),
 \qquad T^0_{ij}=0\quad((i,j)\notin\mathcal J).
\tag{4.2}
$$

This is an affine Hermitian reference with the actual physical margins;
it need not itself be positive.  Define the product output references

$$
 \pi_P=P_C\otimes P_D,\qquad \pi_Q=Q_C\otimes Q_D,
$$

and

$$
 E_P=\Phi\rho_0-\pi_P,\qquad E_Q=\Psi\rho_0-\pi_Q.
$$

The two cancellation identities are

$$
\Phi E_P+\Psi E_Q=0,
 \qquad
 v_0:=\|E_P\|_2^2+\|E_Q\|_2^2
 =\frac14\sum_{(i,j)\in\mathcal J}
 \frac{c_{ij}^2}{w_{ij}}(u_iv_j)^2,
\tag{4.3}
$$

where

$$
 c_{ij}=k_{ij}\ell_i\ell_j-\ell_{ij}k_i k_j.
$$

Indeed, the two output residual coefficients are respectively
$-k_{ij}c_{ij}u_iv_j/w_{ij}$ and
$\ell_{ij}c_{ij}u_iv_j/w_{ij}$, and Pauli orthogonality proves both
claims.  This uses all nine correlation coordinates; only coordinates
invisible to both channels are omitted.

Let $N\geq0$ be any Hermitian witness whose correlation coefficients
$n_{ij}=\operatorname{tr}[N(\sigma_i\otimes\sigma_j)]/4$ vanish outside $\mathcal J$.
Put

$$
\mu=\operatorname{tr}(N\rho_0),\qquad q_N=\sum_{(i,j)\in\mathcal J}\frac{n_{ij}^2}{w_{ij}},
\tag{4.4}
$$

and

$$
 W_P=\sum_{(i,j)\in\mathcal J}\frac{\ell_{ij}n_{ij}}{w_{ij}}
 \sigma_i\otimes\sigma_j,\qquad
 W_Q=\sum_{(i,j)\in\mathcal J}\frac{k_{ij}n_{ij}}{w_{ij}}
 \sigma_i\otimes\sigma_j.
$$

Every bipartite state is supported on the tensor product of its two
marginal supports: if a marginal kernel vector had a nonzero block, the
positive expectation of the corresponding projection would be nonzero.
Thus $P$ is supported in $\pi_P$ and $Q$ in $\pi_Q$, including singular
margins.

For a product reference $\pi$ with support projection $\Pi$, define

$$
\Lambda_\pi(X)=\log\operatorname{tr}_{\Pi}\exp(\log(\pi|_\Pi)+\Pi X\Pi)-\operatorname{tr}(\pi X).
\tag{4.5}
$$

The finite-dimensional Gibbs variational formula on the support
(see Watrous, *The Theory of Quantum Information*) says

$$
D(A\Vert\pi)\geq\operatorname{tr}[X(A-\pi)]-\Lambda_\pi(X)
\tag{4.6}
$$

for every density matrix $A$ supported in $\Pi$.
The definitions in (4.3) and self-adjointness of the Pauli
channels give, for $\delta\rho=\rho-\rho_0$,

$$
\operatorname{tr}[2E_P(P-\pi_P)+2E_Q(Q-\pi_Q)]=2v_0.
\tag{4.7}
$$

$$
\begin{aligned}
\operatorname{tr}[W_P(P-\pi_P)+W_Q(Q-\pi_Q)]
 &=\sum_{(i,j)\in\mathcal J}n_{ij}(T_{ij}-T^0_{ij})\\
 &=\operatorname{tr}[N(\rho-\rho_0)]\geq-\mu.
\end{aligned}
\tag{4.8}
$$

**Theorem 4.2 (Entropy-compatible witness bound).** For every source
and independent biases of Definition 1.1 and every witness $N$ of
Definition 4.1, applying (4.6) to $P$ and $Q$ with
$X_P=2E_P+\theta W_P$, $X_Q=2E_Q+\theta W_Q$ proves

$$
\boxed{I_P+I_Q\geq2v_0-\theta\mu
 -\Lambda_{\pi_P}(X_P)-\Lambda_{\pi_Q}(X_Q)}
\tag{4.9}
$$

for every $\theta\geq0$.

In the proof, retain the support compression when references are
singular. Define the strict remainder with the full Hilbert–Schmidt norm,

$$
\delta_\pi(X)=\frac14\|X\|_2^2-\Lambda_\pi(X).
\tag{4.10}
$$

For every Hermitian $X$, this remainder is nonnegative, and it is
strictly positive if $X\ne0$. To prove the claim, let $Y=\Pi X\Pi$,
let $r_\Pi=\operatorname{rank}\Pi$, and choose the support trace-average

$$
 c=\frac{\operatorname{tr}_{\Pi}(Y)}{r_\Pi},\qquad Y_0=Y-c\Pi.
$$

This $c$ minimizes $\|Y-c\Pi\|_2$, since

$$
 \|Y-c'\Pi\|_2^2
 =\|Y-c\Pi\|_2^2+r_\Pi(c'-c)^2.
$$

The functional $\Lambda_\pi$ is invariant under adding a scalar on the
support. On that support, quantum Pinsker in trace-zero Hilbert–Schmidt
form gives $D(A\Vert\pi)\geq\|A-\pi\|_2^2$. One can obtain this
standard Pinsker consequence (see Watrous, *The Theory of Quantum
Information*) by measuring the positive spectral projection of $A-\pi$,
applying binary DPI, and using the binary second derivative
$1/[p(1-p)]\geq4$, together with
$\|A-\pi\|_1^2\geq2\|A-\pi\|_2^2$. When $A\ne\pi$, the binary
curvature gives a strict inequality: equality of curvature can occur
only at the isolated value $p=1/2$, not on a nonconstant segment.
The Gibbs supremum is attained at the density matrix

$$
 A_X=\frac{\exp(\log(\pi|_\Pi)+Y)}{Z},\qquad
 Z=\operatorname{tr}_{\Pi}\exp(\log(\pi|_\Pi)+Y).
$$

Consequently, writing $D_X=A_X-\pi$ on the support and completing the
square at this actual optimizer gives

$$
 \begin{aligned}
 \Lambda_\pi(X)
 &=\operatorname{tr}(Y_0D_X)-D(A_X\Vert\pi)\\
 &\leq\operatorname{tr}(Y_0D_X)-\|D_X\|_2^2\\
 &=\frac14\|Y_0\|_2^2-\|D_X-Y_0/2\|_2^2
 \leq\frac14\|Y_0\|_2^2
 \leq\frac14\|X\|_2^2.
 \end{aligned}
$$

If the support compression $Y$ is nonscalar, then $A_X\ne\pi$:
otherwise taking the unique Hermitian logarithm would give
$Y=(\log Z)\Pi$. The Pinsker step at the attained optimizer is then
strict. If $Y$ is scalar, $\Lambda_\pi(X)=0$, so every nonzero $X$
again has $\delta_\pi(X)>0$. Separately, if $X$ has a nonzero component
outside its support compression, orthogonality gives
$\|Y_0\|_2\leq\|Y\|_2<\|X\|_2$, making the final norm comparison
strict as well. These cases include rank-one reference supports and
nonzero scalar compressions; no full-rank ambient reference is required.

Pauli orthogonality and (4.3) yield

$$
\frac14\bigl(\|X_P\|_2^2+\|X_Q\|_2^2\bigr)=v_0+\theta^2q_N,
\tag{4.11}
$$

(the cross terms vanish).  If $q_N>0$, choose
$\theta_0=[-\mu]_+/(2q_N)$; if $q_N=0$, take $\theta_0=0$.
When $q_N=0$, $\mu=\operatorname{tr}(N\rho)\geq0$ because the witness has no
correlation component and $\rho$ and $\rho_0$ have equal margins.
Combining (4.9), (4.10), and (4.11) gives

$$
\boxed{
 I_P+I_Q\geq \mathcal C_N:=v_0+\frac{[-\mu]_+^2}{4q_N}
 +\delta_{\pi_P}(X_P)+\delta_{\pi_Q}(X_Q),}
\tag{4.12}
$$

Here $X_P,X_Q$ in (4.12) are evaluated at $\theta=\theta_0$, and the
quotient is omitted when $q_N=0$. This support-aware entropy witness
retains the compression in
(4.5), while the full norm in (4.10) is
valid because compression is Hilbert–Schmidt contractive. This proves
Theorem 4.2, including singular product references.

## 5. Combined funding and the positive-overlap obstruction

**Theorem 5.1 (Combined bounds and necessary negative-deficit funding).**
For every source and independent biases of Definition 1.1, and for
every allowed $N$ and product observable $W$, combining
(3.13) with (4.12) gives

$$
\boxed{\Delta\geq\mathcal C_N+
 \int_0^1w_a(t)[3d_t^{\mathsf T}V_t^+d_t+3\mathcal R_t-2s_t]dt.}
\tag{5.1}
$$

Using (3.14) also gives

$$
\boxed{\Delta\geq\mathcal C_N+
 \int_0^1w_a(t)\left[\frac{1-2\kappa_t}{1+\kappa_t}s_t+3\mathcal R_t\right]dt.}
\tag{5.2}
$$

Let $E_+=\{t\in[0,1):\kappa_t>1/2\}$ and
$E_-=[0,1)\setminus E_+$.  Any hypothetical physical state with
$\Delta<0$ must satisfy, simultaneously for every allowed witness $N$
and every chosen $W$,

$$
\boxed{
 \int_{E_+}w_a(t)\frac{2\kappa_t-1}{1+\kappa_t}s_t\,dt
 >\mathcal C_N+3\int_0^1w_a(t)\mathcal R_t\,dt
 +\int_{E_-}w_a(t)\frac{1-2\kappa_t}{1+\kappa_t}s_t\,dt.}
\tag{5.3}
$$

Thus a negative state would need enough full local BKM overlap on
$E_+$ to pay both the entropy-compatibility budget and the residual
correlation cost. The condition applies to the actual physical
source with its jointly constrained correlations.

## 6. Product-Z covariance and the full transverse cross block

**Proposition 6.1 (Exact product-Z curvature decomposition).** Let

$$
 \rho=\sigma_r\otimes\sigma_r,\qquad
 \sigma_r=(I+rZ)/2,\qquad 0<r<1.
$$

For every $b$, $P=\rho$, and the path is

$$
A_t=\frac14[I+rt(ZI+IZ)+r^2ZZ].
\tag{6.1}
$$

In the $Z$ product basis, labelled by $\sigma,\tau\in\{\pm1\}$,

$$
 \lambda_{\sigma\tau}(t)=\frac14[1+rt(\sigma+\tau)+r^2\sigma\tau].
$$

For $0\leq t<1$, all four eigenvalues are positive.
The following calculations prove the exact decomposition. The
active local-$Z$ covariance block
and tangent are

$$
V_{ZZ}(t)=\begin{pmatrix}1-r^2t^2&r^2(1-t^2)\\
r^2(1-t^2)&1-r^2t^2\end{pmatrix},
 \qquad d_{ZZ}=(r,r)^{\mathsf T}.
\tag{6.2}
$$

A longitudinal calculation alone would not establish the full operator
norm in (3.9).  The transverse block is obtained as follows.
For a diagonal $A_t$, the matrix-element formula is

$$
 \mathcal K_{A_t}(B,C)=\operatorname{Re}\sum_{\alpha,\beta}
 L(\lambda_\alpha,\lambda_\beta)B_{\alpha\beta}C_{\beta\alpha}
$$

for centered observables (the centering does not change off-diagonal
terms).  A local Pauli on $C$ with label $x$ or $y$ flips only $\sigma$;
a local Pauli on $D$ with label $x$ or $y$ flips only $\tau$; a $z$
label makes no flip.  The two matrix elements in the displayed sum
can share an ordered pair only when both labels are $z$.  Therefore the
entire $3\times3$ cross block, including every transverse entry, is

$$
B_t=\begin{pmatrix}0&0&0\\0&0&0\\0&0&r^2(1-t^2)\end{pmatrix}.
\tag{6.3}
$$

The same transition argument shows that the active $Z$ coordinates have
no covariance with the transverse coordinates and that $ZZ$ has no
covariance with a transverse local Pauli.  Since both marginals have
Bloch vector $rtZ$,

$$
 \mathcal Q_{p(t)}=\mathcal Q_{q(t)}
 =\operatorname{diag}\left(\frac{rt}{\operatorname{atanh}(rt)},
 \frac{rt}{\operatorname{atanh}(rt)},1-r^2t^2\right).
$$

Equation (6.3) and this full diagonal marginal metric prove
the exact operator norm of the full normalized cross block:

$$
\boxed{\kappa_t=\frac{r^2(1-t^2)}{1-r^2t^2}.}
\tag{6.4}
$$

Choose $W=ZZ$.  The only nonzero entries of $z_t$ are the two $Z$
entries, and direct classical covariance gives

$$
z_t=rt(1-r^2)(1,1)^{\mathsf T},\qquad
 v_t=1-r^4,\qquad e_t=0.
\tag{6.5}
$$

Put

$$
 D_t=1+r^2-2r^2t^2,\qquad
 E_t=(1+r^2)^2-4r^2t^2.
$$

The active block in (6.2) has eigenvalue $D_t$ on $(1,1)$,
so

$$
d_t^{\mathsf T}V_t^+d_t=\frac{2r^2}{D_t},
 \qquad
 \frac{s_t}{1+\kappa_t}=\frac{2r^2}{D_t}.
\tag{6.6}
$$

The Schur denominator is $(1-r^2)E_t/D_t$, while the residual score
pairing is $-2r^2t(1-r^2)/D_t$.  Consequently

$$
\mathcal R_t=\frac{4r^4t^2(1-r^2)}{D_tE_t}.
\tag{6.7}
$$

Finally direct diagonal differentiation gives

$$
G_{A_t}(H)=\frac{2r^2(1+r^2)}{E_t}
 =d_t^{\mathsf T}V_t^+d_t+\mathcal R_t.
\tag{6.8}
$$

Thus the Schur residual exactly recovers the curvature omitted by the
scalar product-of-margins enclosure on this whole family. The
complete transverse block (6.3) determines the full
$\kappa_t$; decoupling of the tangent and $W$ alone is insufficient.

## 7. Strict entropy-witness calibration on an entire fiber

**Proposition 7.1 (Strict full-fiber calibration).** Take

$$
 a=b=\frac12,\qquad u=v=(0,7/10,0),\qquad
 N=|--\rangle_Y\langle--|.
$$

Here $T^0_{yy}=c_0=49/400$,

$$
 d=2(7/10)-1-c_0=111/400,\qquad
 v_0=0,\qquad \mu=-d/4,\qquad q_N=1/32,\qquad
 \theta_0=4d.
$$

The two references coincide and commute with $YY$, and

$$
 W_P=W_Q=\frac18YY,\qquad
 \Lambda_\pi(xYY)=\log(\cosh x+c_0\sinh x)-c_0x.
$$

Its first derivative vanishes at zero and its second derivative is a
variance of a $\{\pm1\}$-valued variable, hence is at most one.  With
$x=\theta_0/8=d/2$, equation (4.9) gives

$$
I_P+I_Q\geq\frac34d^2.
\tag{7.1}
$$

For comparison, the two local entropy gains are equal to

$$
 h_0=\int_{7/40}^{7/20}\operatorname{atanh}x\,dx,
 \qquad \frac{147}{3200}\leq h_0\leq\frac{49}{936},
$$

using $x\leq\operatorname{atanh}x\leq x/(1-x^2)$.  For the actual classical–quantum $K$-record state

$$
 \Omega_{UCD}=\frac{1+a}{2}|0\rangle\langle0|\otimes P
 +\frac{1-a}{2}|1\rangle\langle1|\otimes KPK,
$$

unitary invariance of the conditional entropies gives
$I(U:CD)=g$ and $I(U:E)=h_E$. The conditional-information chain rule
and data processing therefore give
$I(U:D\mid C)+I(U:C\mid D)=2g-h_C-h_D\geq0$.
Here $h_C=h_D=h_0$, so $2g-2h_0\geq0$ and
$3g-4h_0\geq-h_0$.  Thus the elementary quadratic-plus-PSD estimate
alone has the upper estimate
$d^2/2-h_0\leq d^2/2-147/3200=-2379/320000<0$, while

$$
 \Delta\geq\frac34d^2-\frac{49}{936}
 =\frac{404671}{74880000}>0
$$

for every physical state with these margins.  This is an analytic
fiber statement; no commutativity of an arbitrary source is assumed.

## 8. A finite algebraic covariance form

**Proposition 8.1 (Symmetrized finite algebraic bound).** The same
variational construction gives a lower bound without logarithmic
means. For the centered symmetrized covariance of the six
local Pauli observables, direct Pauli multiplication gives

$$
V_t^{\rm sym}=\begin{pmatrix}
 I-p p^{\mathsf T}&T-pq^{\mathsf T}\\
 T^{\mathsf T}-qp^{\mathsf T}&I-qq^{\mathsf T}
 \end{pmatrix},
\tag{8.1}
$$

where $p,q,T$ are the Pauli data of $A_t$.  For
$W=(n_0\cdot\boldsymbol\sigma)\otimes(m_0\cdot\boldsymbol\sigma)$ and
$c=n_0^{\mathsf T}Tm_0$,

$$
z^{\rm sym}=\binom{(m_0\cdot q)n_0-cp}{(n_0\cdot p)m_0-cq},
 \qquad v^{\rm sym}=1-c^2,
 \qquad e=n_0^{\mathsf T}T'm_0.
\tag{8.2}
$$

The logarithmic-mean inequality $L(x,y)\leq(x+y)/2$ gives
$\mathcal K_A\leq\mathcal K_A^{\rm sym}$ on centered observables.  Therefore the
variational and Schur arguments remain valid with $V^{\rm sym}$ and
its residual, yielding a finite matrix-algebra lower bound which still
contains every one of the nine $T_{ij}$. The threshold
$\kappa_t\leq1/2$ of Theorem 3.3 is not asserted
for this weaker symmetrized form.

## 9. The universal funding assertion and exact pinching accounting

**Open assertion 9.1 (Universal sign and positive-overlap funding).**
For every actual complex PSD trace-one $\rho$ and independent
$a,b\in[0,1]$, is $\Delta(\rho)\geq0$? A sufficient unresolved
funding assertion for the bounds above is that, for every such source,
one can choose an allowed PSD witness $N$ and product observable $W$
so that

$$
 \int_{E_+}w_a(t)\frac{2\kappa_t-1}{1+\kappa_t}s_t\,dt
 \leq\mathcal C_N+3\int_0^1w_a(t)\mathcal R_t\,dt
 +\int_{E_-}w_a(t)\frac{1-2\kappa_t}{1+\kappa_t}s_t\,dt.
$$

No universal choice with this property is supplied by Theorems 3.3,
4.2, and 5.1; nor do they supply a nonnegative local-field certificate
for every pair of margins and independent biases. Failure of one of
these lower certificates does not imply $\Delta<0$. The local family
in Theorem 2.1 establishes a sharp diagonal restriction cost and support
rotation, not a negative physical state or a universal sign theorem.

**Proposition 9.2 (Exact pinching accounting).** Let
$T_X(B)=(B+XBX)/2$, $\Pi=T_{X,C}T_{X,D}$, put
$k(A)=S(\Pi A)-S(A)$, and write
$c_E(A)=S(T_{X}A_E)-S(A_E)$ and
$d_A=I_A-I_{\Pi A}=k(A)-c_C(A)-c_D(A)$.  The chain rule and CPTP
data processing give the exact identity

$$
 \Delta=J_Q+J_R+A_L+2d_P+C_U-f_C-f_D,
$$

where $J_A=I_{\Pi A}$, $A_L=k(Q)-k(R)\geq0$,
$C_U=I(U:D\mid C)+I(U:C\mid D)\geq0$ is the classical $K$-record
conditional-information sum,
and $f_E=c_E(Q)-c_E(R)\geq0$. Here the record $U$ is the actual
state $\Omega_{UCD}$ defined in the
proof of Proposition 7.1, with the current source and bias $a$.
To verify the identity, $\Pi P=\Pi R$ and its marginal versions imply

$$
 J_P=J_R,\qquad k(P)-k(R)=g,\qquad
 \sum_E[c_E(P)-c_E(R)]=h,\qquad d_P-d_R=g-h.
$$

Also $C_U=2g-h$ by the record chain rule, while
$A_L-f_C-f_D=d_Q-d_R$. Substitute $I_P=J_R+d_P$ and
$I_Q=J_Q+d_Q$ into (1.4) to obtain exactly the displayed pinching
identity. Local data processing gives $d_P\geq0$, and $J_Q,J_R\geq0$.
For the remaining signs, $k(A)=D(A\Vert\Pi A)$ and
$c_E(A)=D(A_E\Vert T_XA_E)$. The map $\Phi$ and its marginal channels
commute with the respective pinchings and send $Q$ to $R$; relative-entropy
data processing gives $A_L\geq0$ and $f_E\geq0$, with singular cases
interpreted on their supports. Thus the identity leaves precisely the
local penalty $f_C+f_D$ to be funded. The signed BKM overlap integral
provides the alternative unresolved funding expression in Assertion 9.1.

## 追加锚（本行以下为增补区）


## 10. Obstructions to the auxiliary funding assertions

**Proposition 10.1 (Correction to the sufficient assertion in 9.1).**
The existential PSD-witness and product-observable funding assertion in
Assertion 9.1 is false. The statements calling that sufficient assertion
unresolved in §1, Assertion 9.1, and the last sentence of Proposition 9.2
are superseded by this proposition. The original question
$\Delta(\rho)\geq0$ on the domain of Definition 1.1 remains open;
Theorems 3.3, 4.2, and 5.1 remain valid lower bounds.

More precisely, let $|\pm\rangle_Y$ be the two $Y$ eigenvectors and take

$$
\rho=\frac34|++\rangle_Y\langle++|
 +\frac14|--\rangle_Y\langle--|
 =\frac14[I+\tfrac12(YI+IY)+YY],\qquad
 a=\frac12,\quad b=\frac14.
\tag{10.1}
$$

At this complex, nonreal rank-two state, both combined right sides in
Theorem 5.1 are at most $-87/16384$ for every allowed $N$ and every
product observable $W$. Adding any family of joint score observables,
or allowing any $\theta\geq0$ in the endpoint bound (4.9), does not
remove this obstruction. At the same state,

$$
\Delta=2\mathsf h(1/8)+\mathsf h(1/4)-\mathsf h(1/16)
 \geq\frac32\log2>0,
\quad
\mathsf h(x)=-\frac{1+x}{2}\log\frac{1+x}{2}
            -\frac{1-x}{2}\log\frac{1-x}{2}.
\tag{10.2}
$$

Proof.
Put $A(s)=[I+s(YI+IY)+YY]/4$. Both channels preserve
$\mathcal S=\operatorname{span}\{|++\rangle_Y,|--\rangle_Y\}$, and

$$
P=A(1/8),\qquad Q=A(1/4),\qquad R=A(1/16).
$$

The nonzero eigenvalues of $A(s)$, and the eigenvalues of each of its
margins, are $(1\pm s)/2$. In particular the source spectrum is
$(3/4,1/4,0,0)$, and $S(A(s))=I_{A(s)}=\mathsf h(s)$.

Write $m=1/8$. The supported path is $A_t=A(mt)$, and $H$ has
entries $(m/2,-m/2)$ on $\mathcal S$. The compressions of $XI,ZI,IX,IZ$
vanish, while $YI$ and $IY$ both compress to
$\operatorname{diag}(1,-1)$. With $c_t=1-m^2t^2$, the active local
Gram block and derivative vector are

$$
V_{YY,t}=c_t\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
 d_{YY}=(m,m)^{\mathsf T},\qquad
 B_t=\operatorname{diag}(0,c_t,0).
$$

Each marginal BKM matrix has longitudinal entry $c_t$, so the full
normalized cross operator (3.9) has just one nonzero singular value,
equal to $1$. Thus $\kappa_t=1$. Direct differentiation on $\mathcal S$
gives

$$
\begin{aligned}
\mathrm D\log_{A_t}[H]
 &=\frac m{c_t}(YI-mt I_{\mathcal S}),\\
G_{A_t}(H)&=\frac{m^2}{c_t}=d_t^{\mathsf T}V_t^+d_t,
& s_t&=\frac{2m^2}{c_t}.
\end{aligned}
\tag{10.3}
$$

The full optimal score already lies in the centered local span.
Consequently the score pairing of every orthogonal additional observable
is zero. Every Schur score residual is zero, even after adding any family
of observables. Both covariance integrands in Theorem 5.1 are therefore
$-G_{A_t}(H)$.

For the source margins $u_y=v_y=1/2$, (4.2) gives

$$
T^0_{yy}=\frac{a^2+b^2}{2}\left(\frac12\right)^2=\frac5{128},\qquad
\rho_0=\frac14[I+\tfrac12(YI+IY)+\tfrac5{128}YY].
$$

The four eigenvalues of this reference are
$(261,123,123,5)/512$. Hence $\rho_0>0$, and
$\mu=\operatorname{tr}(N\rho_0)\geq0$ for every allowed PSD witness.
The prescribed $\theta_0$ is zero for all of them. Moreover,

$$
E_P=\frac3{512}YY,\qquad E_Q=-\frac3{512}YY,\qquad
 v_0=\frac9{32768}.
$$

For the supported Gibbs state
$\omega_\pi(X)=\exp(\log(\pi|_\Pi)+\Pi X\Pi)/Z_\pi(X)$,
direct subtraction of logarithms yields
$\Lambda_\pi(X)=D(\pi\Vert\omega_\pi(X))\geq0$.
Thus (4.9) is at most $2v_0$ for every $\theta\geq0$, and in particular

$$
\mathcal C_N=2v_0-\Lambda_{\pi_P}(2E_P)
                    -\Lambda_{\pi_Q}(2E_Q)\leq2v_0.
$$

The path identity (3.12) and
$\mathsf h'(x)=-\operatorname{atanh}x$ give

$$
g=\mathsf h(1/16)-\mathsf h(1/8)
 =\int_{1/16}^{1/8}\operatorname{atanh}x\,dx
 \geq\int_{1/16}^{1/8}x\,dx=\frac3{512}.
$$

Both combined right sides are consequently at most

$$
2v_0-g\leq\frac9{16384}-\frac3{512}=-\frac{87}{16384}<0.
\tag{10.4}
$$

This disproves the universal sufficient funding assertion in 9.1,
with its witness and observable choices quantified before the bound.
Since the two marginal entropy gains both equal $g$, (1.4) gives
(10.2). Concavity gives $\mathsf h(x)\geq(1-x)\log2$ for
$0\leq x\leq1$, and $\mathsf h(x)\leq\log2$, proving its strict sign.

**Definition 10.2 (Actual-correlation budget).** For a two-qubit state
$A$, let $p,q,T$ be its actual Pauli data, and choose unit vectors $n,m$
in the directions of its marginal Bloch vectors; use the $Z$ direction
when a vector is zero. Put

$$
r=|p|,\quad s=|q|,\quad c=n^{\mathsf T}Tm,\qquad
w_{uv}=\frac{1+ur+vs+uvc}{4},\quad u,v\in\{-1,1\}.
\tag{10.5}
$$

These are the probabilities of the product spectral pinching
$\bar A=\mathscr D_A(A)$ in the actual marginal eigenbases. Define

$$
\begin{aligned}
M(A)&=S(A_C)+S(A_D),\\
J_A&=M(A)+\sum_{u,v}w_{uv}\log w_{uv},\\
\mathsf V(A)&=J_A+\frac{\|T\|_F^2-c^2}{4},\qquad
 \mathcal B_{\rm vis}=\mathsf V(P)+\mathsf V(Q).
\end{aligned}
\tag{10.6}
$$

The usual zero conventions apply to the probabilities.

**Proposition 10.3 (Validity and limits of the visible lower bound).**
For every complex two-qubit state, including singular states,

$$
I_A=J_A+D(A\Vert\bar A)\geq\mathsf V(A)\geq0,
\qquad
\mathsf V(A)=0\ \Longleftrightarrow\ A=A_C\otimes A_D.
\tag{10.7}
$$

For any measurable score lower estimate $0\leq\gamma_t\leq G_{A_t}(H)$,

$$
\Delta\geq\mathcal L_{\rm vis}(\gamma):=
 \mathcal B_{\rm vis}+\int_0^1 w_a(t)(3\gamma_t-2s_t)\,dt.
\tag{10.8}
$$

This lower bound need not be nonnegative, even when $\gamma_t$ is the
full BKM curvature, as Proposition 10.4 shows.

Proof.
The pinching preserves both margins. A zero diagonal entry of
$\bar A$ forces the corresponding row and column of $A$ to vanish by
positivity. Hence
$\operatorname{supp}A\subseteq\operatorname{supp}\bar A
\subseteq\operatorname{supp}(A_C\otimes A_D)$.
The logarithms of the latter two matrices are diagonal on their
supports, so tracing them against $A$ or $\bar A$ gives the same result.
Subtracting relative entropies gives
$I_A=J_A+D(A\Vert\bar A)$.

The standard CPTP relative-entropy data-processing and Pinsker bounds
(Watrous, *The Theory of Quantum Information*) imply
$D(B\Vert C)\geq\|B-C\|_2^2$ for density matrices with the necessary
support inclusion. Indeed, measurement of the positive spectral
projection of $B-C$ gives $D(B\Vert C)\geq2t^2$, where $t$ is the
positive trace of $B-C$. Its positive and negative parts each have
trace $t$, so $\|B-C\|_2^2\leq2t^2$.
Pauli orthogonality now gives

$$
\|A-\bar A\|_2^2=\frac{\|T\|_F^2-c^2}{4}.
$$

This proves (10.7). If equality $\mathsf V(A)=0$ holds, the residual
vanishes, so $A=\bar A$, and $J_A=0$ forces this classical state to be
the product of its margins. The converse is direct. Finally insert
$I_P+I_Q\geq\mathcal B_{\rm vis}$ and
$g\geq\int w_a\gamma_t$, $h=\int w_a s_t$ into (1.4).
The weighted curvature identity bounds $\int w_a\gamma_t$ by the
finite number $g$, so all displayed weighted integrals are defined.
All endpoint identities retain the supported interpretation of §3.

**Proposition 10.4 (Full-rank obstruction to visible funding).**
In the computational basis of Definition 1.1, take

$$
v=(-1+3i,-2,12,2+6i)^{\mathsf T},\qquad
\rho=\frac{999}{1000}\frac{vv^*}{198}+\frac{I_4}{4000},\qquad
 a=\frac14,\quad b=\frac{15}{16}.
\tag{10.9}
$$

This is a nonreal positive definite trace-one state with unequal valid
biases. With $g,h$ from Definition 1.2, set
$U=\mathcal B_{\rm vis}+3g-2h$. Then

$$
-\frac{24077097}{10^9}\leq U\leq-\frac{24077096}{10^9}
 <-\frac{24}{1000},\qquad
\frac{307125175}{10^9}\leq\Delta\leq\frac{307125176}{10^9}.
\tag{10.10}
$$

Consequently $\mathcal L_{\rm vis}(\gamma)<0$ for every score estimate
in Proposition 10.3. In particular the universal visible funding
assertion

$$
\int_0^1w_a(t)(2s_t-3\gamma_t)\,dt\leq\mathcal B_{\rm vis}
\tag{10.11}
$$

is false for the local score augmented by the maximum of the nine
separate Pauli Schur residuals from (3.4), for any genuine larger score
projection, and even for the full score $\gamma_t=G_{A_t}(H)$.

Proof.
First $v^*v=10+4+144+40=198$, so the spectrum of $\rho$ is
$(3997,1,1,1)/4000$. Every path state is at least $I_4/4000$:
all channels and all path points are convex mixtures of unitary
conjugations of $\rho$. There are therefore no singular endpoint
logarithms at this example. The exact output matrices are

$$
P=\frac{31\rho+L\rho L}{32},\qquad
Q=\frac{5\rho+3K\rho K}{8},\qquad
R=\frac{5P+3KPK}{8}.
\tag{10.12}
$$

Here is rational spectral and Pauli data sufficient to evaluate every
entropy in (10.10). Write $\chi_A(z)=\det(zI_4-A)$. Direct determinant
expansion gives

$$
\begin{aligned}
\chi_P(z)&=(z-1/4000)^2
 \left(z^2-\frac{1999}{2000}z+\frac{357173771}{15488000000}\right),\\
\chi_Q(z)&=(z-1/4000)^2
 \left(z^2-\frac{1999}{2000}z+\frac{1801478203}{7744000000}\right),\\
\chi_R(z)&=z^4-z^3+\frac{120448480659}{495616000000}z^2
 -\frac{24478666840733}{5451776000000000}z
 +\frac{15925486527909364633}{982540877824000000000000}.
\end{aligned}
\tag{10.13}
$$

The following disjoint rational intervals contain the complete spectra;
nonpoint intervals have width at most $10^{-12}$ and contain one simple
root. The point intervals have the displayed multiplicity two.

| State | Multiplicity | Lower endpoint | Upper endpoint |
| --- | --- | --- | --- |
| $P$ | $2$ | $1/4000$ | $1/4000$ |
| $P$ | $1$ | $7175/303619$ | $139854/5918095$ |
| $P$ | $1$ | $2378851/2437676$ | $710683/728257$ |
| $Q$ | $2$ | $1/4000$ | $1/4000$ |
| $Q$ | $1$ | $749898/2032783$ | $618007/1675260$ |
| $Q$ | $1$ | $1312300/2081041$ | $1582561/2509620$ |
| $R$ | $1$ | $9167/1883940$ | $6979/1434277$ |
| $R$ | $1$ | $24887/1670423$ | $27389/1838358$ |
| $R$ | $1$ | $591191/1636990$ | $547279/1515399$ |
| $R$ | $1$ | $224159/362078$ | $3418942/5522525$ |

For a direct rational root count, divide (10.13) into squarefree factors
and apply the Sturm recurrence $f_0=f$, $f_1=f'$, and
$f_{j+1}=-\operatorname{rem}(f_{j-1},f_j)$. At each nonpoint interval
the variation count at its lower endpoint exceeds that at its upper
endpoint by one; neither endpoint is a root. The point $1/4000$ is
checked by substitution and has multiplicity two for $P,Q$.
The total multiplicity is four in every case, so no eigenvalue is
omitted. All endpoints lie in $(0,1)$.

For the marginal and pinching entropies put
$\nu_A=p^{\mathsf T}Tq$ and
$\eta_A=(\|T\|_F^2-\nu_A^2/(r^2s^2))/4$.
The traces $p_i=\operatorname{tr}(A\sigma_iI)$,
$q_j=\operatorname{tr}(AI\sigma_j)$ and
$T_{ij}=\operatorname{tr}(A\sigma_i\sigma_j)$ in the fixed Pauli
convention give the following rational invariants.

| $A$ | $r^2$ | $s^2$ | $\nu_A$ | $\eta_A$ |
| --- | --- | --- | --- | --- |
| $P$ | $4669659/4840000$ | $141408117/154880000$ | $139910018931/154880000000$ | $61560834894981/33684719552000000$ |
| $Q$ | $1342989/15488000$ | $9819837/77440000$ | $278623360737/4259200000000$ | $2797470550456389/21023266000000000$ |
| $R$ | $3166497/38720000$ | $563919849/4956160000$ | $1615816365201/27258880000000$ | $19009662585939117/157560786944000000$ |

In particular $0<r,s<1$, $c=\nu_A/(rs)$, and every $w_{uv}>0$.
The latter also follows from $A\geq I_4/4000$ by taking its expectation
in each pinching basis vector. Thus

$$
M(A)=\mathsf h(r)+\mathsf h(s),\qquad
\mathsf V(A)=M(A)+\sum_{u,v}w_{uv}\log w_{uv}+\eta_A.
\tag{10.14}
$$

The numerical bounds in (10.10) follow by the following finite rational
inequalities. For rational $x\geq0$, take
$k=\lfloor\sqrt{10^{28}x}\rfloor$; then
$k/10^{14}\leq\sqrt x<(k+1)/10^{14}$, as verified by squaring.
For a positive rational logarithm argument write $x=2^j y$,
$1\leq y\leq2$, and $z=(y-1)/(y+1)$. The positive atanh series has

$$
\begin{aligned}
L(y)&=2\sum_{k=0}^{23}\frac{z^{2k+1}}{2k+1},\\
L(y)&\leq\log y\leq L(y)+\frac{2z^{49}}{49(1-z^2)}.
\end{aligned}
\tag{10.15}
$$

Indeed, replacing every omitted denominator by $49$ bounds the tail
by the displayed geometric sum. Apply the same bounds to $\log2$ and
use $\log x=\log y+j\log2$, reversing the endpoints when $j<0$.
For an interval, monotonicity of the logarithm supplies its bounds from
the two endpoints. Use four-corner rational interval multiplication
for $-x\log x$, reciprocal bounds only for intervals excluding zero,
and sum over each spectral root with its multiplicity.

Substituting these bounds into (10.6), (10.12)--(10.14), and
$\Delta=M(P)-S(P)+M(Q)-S(Q)+3g-2h$ yields, with outward rounding
to multiples of $10^{-9}$, precisely (10.10). Every input and tail
bound is rational; no floating point sign inference is needed.

Finally, $w_a(t)\geq0$ and (3.12) give

$$
\mathcal L_{\rm vis}(\gamma)
 \leq\mathcal B_{\rm vis}+\int_0^1w_a(t)(3G_{A_t}(H)-2s_t)\,dt
 =\mathcal B_{\rm vis}+3g-2h=U<0.
\tag{10.16}
$$

Each of the nine separate local-plus-Schur projections satisfies
$\gamma_t\leq G_{A_t}(H)$ by (3.5); their maximum satisfies the same
bound. Any enlarged orthogonal score projection also has squared norm
at most the full score norm. This proves the asserted scope of failure.
The independent positive bound for $\Delta$ in (10.10) proves that this
state does not refute the original entropy inequality.

**Open assertion 10.5 (Original universal sign).** For every actual
complex PSD trace-one $\rho$ and independent $a,b\in[0,1]$, does
$\Delta(\rho)\geq0$ hold? This is the open part of Assertion 9.1.
Its witness-funding sufficient assertion is disproved by Proposition
10.1; the visible-budget sufficient assertion (10.11) is disproved by
Proposition 10.4. The actual-correlation bound (10.7), the supported BKM
identities, the earlier lower bounds, and Proposition 9.2's exact
pinching accounting remain valid. A sufficient argument retaining the
visible endpoint budget cannot be repaired solely by adding path score
observables, even all of them; it must use more endpoint information or
a different combined inequality.
## 追加锚（本行以下为增补区）

## 11. A spectral region retaining the exact endpoint budget

**Definition 11.1 (Spectral data and the exact budget).** Let $\rho$ be any complex positive semidefinite trace-one matrix on two
qubits $C,D$. Write $K=X\otimes X$, $L=Z\otimes Z$ and, independently for
$a,b\in[0,1]$,
$$
 \Psi_a(A)=\frac{1+a}{2}A+\frac{1-a}{2}KAK,
 \qquad
 \Phi_b(A)=\frac{1+b}{2}A+\frac{1-b}{2}LAL.
$$
Set $P=\Phi_b\rho$, $Q=\Psi_a\rho$, $R=\Psi_a P$,
$S(A)=-\operatorname{tr} A\log A$ with natural logarithms and $0\log0=0$, and
$$
 I_A=S(A_C)+S(A_D)-S(A),\qquad
 g=S(R)-S(P),\quad h=\sum_{E=C,D}[S(R_E)-S(P_E)].
$$
The original deficit is
$$
 \Delta=3S(R)-4S(P)-S(Q)
 +\sum_{E=C,D}[3S(P_E)+S(Q_E)-2S(R_E)]
 =I_P+I_Q+3g-2h.
$$

**Theorem 11.2 (A comparison retaining all endpoint information).**
Put $M=\lambda_{\max}(P)$. If the two actual marginal Bloch lengths
$r_C,r_D$ are less than one and
$$
 f(r)=\begin{cases}\operatorname{atanh}(r)/r&r>0,\\1&r=0,\end{cases}
 \qquad f_*=\max\{f(r_C),f(r_D)\},
$$
then
$$
 h\leq4Mf_*g,\qquad
 \Delta\geq I_P+I_Q+(3-8Mf_*)g.
$$
In particular, for the entire original source and bias domain,
$$
 M\leq\frac7{20}
 \quad\Longrightarrow\quad
 \boxed{\Delta\geq I_P+I_Q+\frac1{45}g\geq0.}
\tag{11.1}
$$
Consequently every negative original deficit, if one exists, has
$\lambda_{\max}(\Phi_b\rho)>7/20$.

Proof.
We first establish the relative-entropy estimate needed below, using the
standard finite-dimensional logarithmic functional calculus (Bhatia,
*Matrix Analysis*). If $A,B$ are density matrices and $A,B\preceq MI$ for $M>0$, then
$$
 D(A\Vert B)\geq\frac{\|A-B\|_2^2}{2M}.
$$
Here relative entropy is extended by $+\infty$ if the support condition
fails, and $\|H\|_2^2=\operatorname{tr} H^*H$.

First suppose $A,B$ are positive definite. On the segment
$A_t=B+t(A-B)\preceq MI$, put $H=A-B$ and
$F(A)=\operatorname{tr}(A\log A)$. The derivative of the logarithm gives
$$
 F''(A_t)[H,H]=\int_0^\infty
 \operatorname{tr}\bigl(H(A_t+sI)^{-1}H(A_t+sI)^{-1}\bigr)\,ds.
$$
In an orthonormal eigenbasis of $A_t$, the integrand is
$\sum_{ij}|H_{ij}|^2/[(\lambda_i+s)(\lambda_j+s)]$ and hence is at
least $\|H\|_2^2/(M+s)^2$. It follows that
$F''(A_t)[H,H]\geq\|H\|_2^2/M$. Integrating with weight $1-t$ and
using $\operatorname{tr} H=0$ identifies the Bregman remainder with $D(A\Vert B)$
and proves the bound.
For singular matrices with support inclusion, restrict to
$\operatorname{supp}B$ (which contains $\operatorname{supp}A$) and use
$(1-\varepsilon)A+\varepsilon B$ to approach $A$. This segment is still
bounded above by $MI$, is positive definite on that support, and its
relative entropy to $B$ converges by finite-dimensional spectral
continuity. Without support inclusion the asserted extended inequality
is immediate.

We now prove the comparison for the actual channels.
If $a=1$, then $R=P$ and $g=h=0$, so the claims follow directly.
For the moment assume $a<1$ and $\rho$ positive definite. Define
$$
 T=\frac{P-KPK}{2},\qquad w=\frac{1+a}{2}.
$$
Both mixing weights are positive, and $R=wP+(1-w)KPK$. The exact
relative-entropy mixing identity is
$$
 g=wD(P\Vert R)+(1-w)D(KPK\Vert R).
$$
Since $P,KPK,R\preceq MI$, the relative-entropy estimate above,
$P-R=(1-a)T$, and $KPK-R=-(1+a)T$ give
$$
 g\geq\frac{w(1-a)^2+(1-w)(1+a)^2}{2M}\|T\|_2^2
 =\frac{1-a^2}{2M}\|T\|_2^2.
\tag{11.2}
$$

Write the actual marginal as
$$
 P_E=\frac{I+x_EX+y_EY+z_EZ}{2},\qquad
 r_E^2=x_E^2+y_E^2+z_E^2,\qquad u_E=y_E^2+z_E^2.
$$
The reduced channel gives
$R_E=(I+x_EX+a y_EY+a z_EZ)/2$. For binary entropy
$\mathsf h(r)=-\sum_{\pm}(1\pm r)\log((1\pm r)/2)/2$, differentiation
uses $\mathsf h'(r)=-\operatorname{atanh}r$. Thus
$$
 h_E=\int_a^1 t u_E f\!\left(\sqrt{x_E^2+t^2u_E}\right)dt
 \leq\frac{1-a^2}{2}\,u_E f(r_E).
$$
The estimate follows because $f$ increases on $[0,1)$, as is also
immediate from its positive series $\sum_{n\geq0}r^{2n}/(2n+1)$.

To compare the two local tangents with the actual global tangent, put
$T_E=\operatorname{tr}_{E^c}T=(y_EY+z_EZ)/2$. Then
$$
 T=\frac12T_C\otimes I+\frac12I\otimes T_D+T_0,
 \qquad \operatorname{tr}_C T_0=\operatorname{tr}_D T_0=0.
$$
The three terms are Hilbert--Schmidt orthogonal: the marginal tangents
are traceless, and the two partial traces of $T_0$ vanish. Therefore
$$
 \|T\|_2^2\geq\tfrac12(\|T_C\|_2^2+\|T_D\|_2^2)
 =\frac{u_C+u_D}{4}.
\tag{11.3}
$$
Adding the two marginal estimates and applying (11.2) and
(11.3) yields
$$
 h\leq\frac{1-a^2}{2}f_*(u_C+u_D)
 \leq2(1-a^2)f_*\|T\|_2^2\leq4Mf_*g.
$$
No division by $g$ or by $1-a^2$ is used. Inserting this inequality into
the exact original deficit proves the first comparison.

Now suppose $M\leq7/20$. Positivity of partial trace applied to
$P\preceq MI_4$ gives $P_E\preceq2MI_2$. Consequently
$$
 \frac{1+r_E}{2}\leq2M,\qquad 0\leq r_E\leq4M-1\leq\frac25.
$$
For $0\leq r\leq2/5$, the same positive series gives the rational bound
$$
 f(r)=1+\sum_{n\geq1}\frac{r^{2n}}{2n+1}
 \leq1+\frac{r^2}{3(1-r^2)}\leq\frac{67}{63}.
$$
It follows that
$$
 h\leq4\cdot\frac7{20}\cdot\frac{67}{63}\,g
 =\frac{67}{45}g,
$$
and
$$
 \Delta\geq I_P+I_Q+\left(3-\frac{134}{45}\right)g
 =I_P+I_Q+\frac1{45}g.
$$
The endpoint mutual informations are nonnegative by their exact
relative-entropy expression, and $g\geq0$ by its mixing identity.

Finally for arbitrary singular $\rho$ use
$\rho_\varepsilon=(1-\varepsilon)\rho+\varepsilon I_4/4$.
Both channels preserve the maximally mixed state, and
$$
 M_\varepsilon=(1-\varepsilon)M+\varepsilon/4.
$$
Thus $M\leq7/20$ implies $M_\varepsilon\leq7/20$. Entropy continuity
proves (11.1) in the limit. More generally if $r_C,r_D<1$, the
regularized marginal lengths converge to them, $M_\varepsilon\to M$,
and continuity of $f$ on $[0,1)$ gives the two comparison inequalities
by the same limit. This includes singular and nonreal inputs without
replacing either endpoint mutual information by a lower truncation.
$\square$


## 12. Two classical controls and further exact-deficit regions

**Definition 12.1 (The actual two-control extension).** Keep the whole
source and independent bias domain of Definition 1.1. For $E=C,D$, write
$\bar E$ for the other qubit, and put

$$
 k=S(R)-S(Q),\qquad
 \ell_E=S(R_E)-S(Q_E),\qquad \ell=\ell_C+\ell_D.
\tag{12.1}
$$

Let $U,V$ be independent classical bits with probabilities

$$
 \pi_u=\frac{1+(-1)^u a}{2},\qquad
 \eta_v=\frac{1+(-1)^v b}{2},\qquad u,v\in\{0,1\}.
$$

Their controlled-Pauli state is the density matrix

$$
 \Omega_{UVCD}=\sum_{u,v}\pi_u\eta_v
 |u,v\rangle\langle u,v|\otimes K^uL^v\rho L^vK^u.
\tag{12.2}
$$

Zero-probability summands are omitted. For subsystems of this state,
use $I(A:B)=S(A)+S(B)-S(AB)$ and

$$
 I(A:B\mid F)=S(AF)+S(BF)-S(F)-S(ABF).
$$

All entropies use natural logarithms and the convention of Definition
1.1. In particular they are finite for singular states. Define
$H_2(t)=-t\log t-(1-t)\log(1-t)$ with its continuous endpoint values.

**Theorem 12.2 (An exact two-control deficit identity).** For either
$E=C,D$ and every source and bias pair of Definition 1.1,

$$
\begin{aligned}
 \Delta={}&2I_P-\ell_E
 +I(U:C\mid D)_\Omega+I(U:D\mid C)_\Omega
 +I(V:E\mid\bar E)_\Omega.
\end{aligned}
\tag{12.3}
$$

Consequently

$$
 \Delta\geq2I_P-\min\{\ell_C,\ell_D\}.
\tag{12.4}
$$

Proof.
The probabilities in (12.2) are nonnegative and sum to one, and each
quantum branch is a unitary conjugate of $\rho$. Since $KL=LK$, the
$CD$ marginal of $\Omega$ is exactly $R$. Conditioning on $U=u$ gives
$K^uPK^u$; conditioning on $V=v$ gives $L^vQL^v$. These are product
unitary conjugations, so the entropy of each joint conditional state,
and of each of its one-qubit margins, is independent of the control
value. The classical-quantum entropy formula

$$
 S\left(\sum_j p_j|j\rangle\langle j|\otimes A_j\right)
 =H(p)+\sum_jp_jS(A_j)
$$

follows by diagonalizing each block. Applying it to these actual
marginal states gives

$$
\begin{aligned}
 I(U:CD)_\Omega&=g,& I(U:E)_\Omega&=h_E,\\
 I(V:CD)_\Omega&=k,& I(V:E)_\Omega&=\ell_E.
\end{aligned}
\tag{12.5}
$$

The mutual-information chain rule therefore yields

$$
\begin{aligned}
 I(U:C\mid D)_\Omega&=g-h_D,&
 I(U:D\mid C)_\Omega&=g-h_C,\\
 I(V:E\mid\bar E)_\Omega&=k-\ell_{\bar E}.
\end{aligned}
\tag{12.6}
$$

These conditional mutual informations are nonnegative by strong
subadditivity (Lieb and Ruskai, *Proof of the strong subadditivity of
quantum-mechanical entropy*, 1973; also Watrous, *The Theory of Quantum
Information*).

The complete endpoint mutual informations obey the exact balances

$$
 I_R-I_P=h-g,\qquad I_R-I_Q=\ell-k.
$$

Thus $I_Q=I_P+h-g-\ell+k$. Substitution into the unchanged original
budget (1.4), followed by (12.6), gives

$$
\begin{aligned}
 \Delta
 &=2I_P+2g-h+k-\ell\\
 &=2I_P-\ell_E+(g-h_D)+(g-h_C)+(k-\ell_{\bar E}),
\end{aligned}
$$

which is (12.3). No endpoint mutual information was discarded in this
identity. Applying strong subadditivity gives
$\Delta\geq2I_P-\ell_E$ for both choices of $E$; their larger lower
bound is (12.4).

**Corollary 12.3 (Control-entropy, endpoint, and fixed-margin regions).**
On the full domain of Definition 1.1,

$$
\begin{aligned}
 \Delta&\geq2I_P-H_2\!\left(\frac{1-b}{2}\right),\\
 \Delta&\geq2I_P-
 \min\left\{H_2\!\left(\frac{1-b}{2}\right),
             \log2-\max_{E=C,D}S(Q_E)\right\}.
\end{aligned}
\tag{12.7}
$$

In particular either of the two conditions

$$
 I_P\geq\frac12H_2\!\left(\frac{1-b}{2}\right),
 \qquad
 2I_P+\max_{E=C,D}S(Q_E)\geq\log2
\tag{12.8}
$$

implies $\Delta\geq0$. The condition $I_P\geq\tfrac12\log2$
is sufficient uniformly in both biases, including when
$\lambda_{\max}(P)>7/20$.
If $[Q_E,Z]=0$ for at least one $E$, then

$$
 \Delta\geq2I_P.
\tag{12.9}
$$

This conclusion holds whenever a source marginal commutes with $Z$,
without any joint-state commutation condition. At each such point with
$I_P>0$, the strict sign $\Delta>0$ holds on a neighborhood relative
to the original physical state and bias domain.

Proof.
The standard classical-control entropy bound gives

$$
 0\leq\ell_E=I(V:E)_\Omega\leq H(V)
 =H_2\!\left(\frac{1-b}{2}\right).
$$

Here the upper bound is the entropy-of-mixture inequality
$S(\sum_jp_jA_j)\leq H(p)+\sum_jp_jS(A_j)$, equivalently the
classical-quantum Holevo bound (Watrous, *The Theory of Quantum
Information*). Also each $R_E$ is a qubit density matrix, whence

$$
 \ell_E=S(R_E)-S(Q_E)\leq\log2-S(Q_E).
$$

Therefore

$$
 \min_E\ell_E\leq
 \min\left\{H(V),\log2-\max_E S(Q_E)\right\}.
$$

Combine this with (12.4) to obtain (12.7)--(12.8), and use
$H_2(t)\leq\log2$ for the bias-uniform sufficient condition.

If $[Q_E,Z]=0$, the local $Z$-mixture fixes $Q_E$, so $R_E=Q_E$ and
$\ell_E=0$. Equation (12.3) proves (12.9). If instead the source
margin commutes with $Z$, its local $X$ conjugate still commutes with
$Z$, since $XZX=-Z$; consequently their mixture $Q_E$ also commutes
with $Z$. Finally the function $2I_P-\ell_E$ is continuous in the
state and biases. At a fixed-margin point with $I_P>0$ it equals
$2I_P>0$, and hence stays positive on a relative open neighborhood.
Theorem 12.2 gives the asserted strict sign there, even if the base
point is singular or lies at a bias endpoint.

**Proposition 12.4 (Endpoints and the residual domain).** Theorem 12.2
and Corollary 12.3 include every singular source and all independent
$a,b\in[0,1]$. At $b=1$, one has $\Delta\geq2I_P$ for every source.
At $a=1$, one has $\Delta=I_P+I_Q\geq0$.
Every negative original deficit, if one exists, must satisfy
simultaneously

$$
\begin{gathered}
 \lambda_{\max}(P)>\frac7{20},\qquad a<1,\quad b<1,\\
 2I_P<\ell_C,\qquad 2I_P<\ell_D,\\
 2I_P<\min\left\{
 H_2\!\left(\frac{1-b}{2}\right),
 \log2-\max_{E=C,D}S(Q_E)\right\}.
\end{gathered}
\tag{12.10}
$$

Proof.
The state (12.2), its block entropy formula, the entropy balances and
strong subadditivity use no inverse or logarithm of a positive definite
matrix. The zero-eigenvalue convention and omission of zero-probability
branches apply directly, so no support regularization or rank assumption
is required. If $b=1$, $V$ is constant and $\ell_C=\ell_D=k=0$;
(12.3) proves the first endpoint assertion. If $a=1$, $R=P$ and
$g=h=0$, so the original exact budget gives the second.
For a negative $\Delta$, Theorem 11.2 excludes
$\lambda_{\max}(P)\leq7/20$, the endpoint assertions exclude $a=1$
and $b=1$, and (12.4) implies both strict inequalities involving
$\ell_E$. The upper bounds for $\min_E\ell_E$ in Corollary 12.3 give
the last line of (12.10).

**Open assertion 12.5 (The unchanged original sign question).** For
every actual complex PSD trace-one two-qubit $\rho$ and independent
$a,b\in[0,1]$, does

$$
 \Delta(\rho)=I_P+I_Q+3g-2h\geq0
$$

hold? The sign on the residual domain (12.10) is not established by the
preceding sufficient regions. Open assertion 10.5 therefore remains the
original unrestricted question, with neither an added source restriction
nor a replacement endpoint budget.

## 追加锚（本行以下为增补区）


## 13. A pure-boundary neighborhood inside the remaining region

Use the states, channels and exact deficit of Definitions 1.1--1.2 and
the second-channel gains $\ell_E$ of Definition 12.1.
Write $I(A)=I_A$. Entropy uses natural logarithms and $0\log0=0$;
write $H_2(t)=-t\log t-(1-t)\log(1-t)$ with continuous endpoint values.

**Theorem 13.1 (A uniform positive neighborhood in the residual domain).**
There is $\theta_0\in(0,1/2)$ such that the following holds uniformly
for independent $a\in[11/12,23/24]$, $b\in[1/4,3/4]$, arbitrary
$\phi_C,\phi_D\in\mathbb R$, and $0<\theta<\theta_0$.
Define
$$
 u_{\theta,\phi}=\cos(\theta/2)|0\rangle+
 e^{i\phi}\sin(\theta/2)|1\rangle,\quad
 \tau=|u_{\theta,\phi_C}u_{\theta,\phi_D}\rangle
       \langle u_{\theta,\phi_C}u_{\theta,\phi_D}|.
$$
Every physical density operator with $\tfrac12\|\rho-\tau\|_1\leq\theta^3$
satisfies
$$
 \Delta(\rho;a,b)\geq\frac7{32}\theta^2\log(1/\theta^2)>0,
$$
and simultaneously
$$
 \lambda_{\max}(P)>7/20,\qquad 2I(P)<\ell_C,\qquad 2I(P)<\ell_D.
$$
Thus these states are outside both previously proved sufficient
regions. The threshold is existential; no numerical cutoff is asserted.

Proof.
Write $c=1-b^2$, $\Lambda=\log(1/\theta^2)$,
$e(t)=H_2((1+t)/2)$, $f(t)=\operatorname{atanh}(t)/t$.
Every $O$-bound below is uniform over the compact bias rectangle and
the two phase circles. These bounds follow from Taylor expansion of
the displayed analytic matrix entries; the spectral estimates below
avoid differentiating entropy at a zero eigenvalue.
First let $\rho=\tau$.

The nonzero spectrum of $P$ is $1-\alpha,\alpha$, with
$$
 \alpha=\frac{1-\sqrt{b^2+c\cos^4\theta}}2
        =\frac c2\theta^2+O(\theta^4).
$$
Both $P_E$ have spectrum $1-\beta,\beta$, with
$$
 \beta=\frac{1-\sqrt{1-c\sin^2\theta}}2
       =\frac c4\theta^2+O(\theta^4).
$$
The constants multiplying $\theta^2$ stay strictly positive, since
$c\in[7/16,15/16]$. Using
$H_2(x)=x\log(1/x)+x+O(x^2)$ gives uniformly
$$
 I(P)=2H_2(\beta)-H_2(\alpha)
 =\frac{c\log2}{2}\theta^2+O(\theta^4\Lambda).
\tag{13.1}
$$
In particular the $\theta^2\Lambda$ terms cancel in this mutual
information.

The pure-state overlap with $K$ is
$\sin^2\theta\cos\phi_C\cos\phi_D$. Hence
$$
 S(Q)=e\left(\sqrt{a^2+(1-a^2)\sin^4\theta
                   \cos^2\phi_C\cos^2\phi_D}\right)
      =e(a)+O(\theta^4).
\tag{13.2}
$$
The marginal Bloch vectors directly give
$S(Q_E)=e(a)+O(\theta^2)$ and
$S(R_E)=e(a)+O(\theta^2)$.

We now compute the small spectrum of $R$. Order the even and odd
$L$-parity sectors as $(|00\rangle,|11\rangle)\oplus(|01\rangle,|10\rangle)$.
Set
$$
 v=\frac12(e^{i\phi_D},e^{i\phi_C})^{\mathsf T},\quad
 J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
 \pi_\pm=(1\pm a)/2,\quad A_0=\operatorname{diag}(\pi_+,\pi_-),
$$
$$
 F=\begin{pmatrix}\pi_+v^{\dagger}\\\pi_-(Jv)^{\dagger}\end{pmatrix},\qquad
 B_0=\pi_+vv^{\dagger}+\pi_-Jvv^{\dagger}J.
$$
The four transformed source vectors give, in operator norm,
$$
 R=\begin{pmatrix}
 A_0+O(\theta^2)&b\theta F+O(\theta^3)\\
 b\theta F^{\dagger}+O(\theta^3)&\theta^2B_0+O(\theta^4)
 \end{pmatrix}.
\tag{13.3}
$$
We have $A_0\succeq I/48$ uniformly and
$$
 F^{\dagger}A_0^{-1}F=B_0,\qquad \operatorname{tr} B_0=\|v\|^2=1/2.
$$
Let
$$
 G=\begin{pmatrix}0&-bA_0^{-1}F\\bF^{\dagger}A_0^{-1}&0\end{pmatrix}.
$$
This anti-Hermitian matrix has uniformly bounded norm. Taylor
expansion of the unitary conjugation $e^{-\theta G}Re^{\theta G}$
cancels the order-$\theta$ off-diagonal block. Its lower block is
$$
 \theta^2(B_0-b^2F^{\dagger}A_0^{-1}F)+O(\theta^3)
 =c\theta^2B_0+O(\theta^3),
$$
its upper block is $A_0+O(\theta^2)$, and its off-diagonal block is
$O(\theta^3)$. Weyl's eigenvalue bound, applied to the resulting
block-diagonal comparison, shows that the two large eigenvalues are
$\pi_\pm+O(\theta^2)$ and the two small ones obey
$$
 \lambda_3+\lambda_4=\frac c2\theta^2+O(\theta^3),\qquad
 0\leq\lambda_j\leq C\theta^2.
$$
The large eigenvalues are uniformly bounded away from zero, so their
entropy contribution is $e(a)+O(\theta^2)$. For the small ones, use
$$
 -\sum_{j=3,4}\lambda_j\log\lambda_j
 =\Lambda\sum_{j=3,4}\lambda_j
 -\theta^2\sum_{j=3,4}\frac{\lambda_j}{\theta^2}
                  \log\frac{\lambda_j}{\theta^2}.
$$
The second sum is uniformly bounded by continuity of $x\log x$ on
$[0,C]$, including zero. Also $\theta^3\Lambda=O(\theta^2)$.
Thus, without a lower bound on either small eigenvalue,
$$
 S(R)=e(a)+\frac c2\theta^2\Lambda+O(\theta^2).
\tag{13.4}
$$

Equations (13.1)--(13.4) give
$$
 I(P)=O(\theta^2),\quad I(Q)=e(a)+O(\theta^2),\quad
 g=e(a)+O(\theta^2),\quad
 h=2e(a)-\frac c2\theta^2\Lambda+O(\theta^2).
$$
Substitution into the unchanged original deficit yields
$$
 \Delta(\tau;a,b)=c\theta^2\Lambda+O(\theta^2).
\tag{13.5}
$$
Both endpoint mutual informations have been retained.

To verify that this region is new, the marginal radii satisfy
$$
 r_{Q,E}^2=a^2+(1-a^2)\sin^2\theta\cos^2\phi_E,
$$
$$
 r_{Q,E}^2-r_{R,E}^2
 =c\sin^2\theta(\cos^2\phi_E+a^2\sin^2\phi_E).
$$
Since $e'(r)=-\operatorname{atanh}r$ and $a$ stays away from both zero
and one, Taylor expansion is uniform and gives
$$
 \ell_E=\frac c2\theta^2 f(a)
            (\cos^2\phi_E+a^2\sin^2\phi_E)+O(\theta^4).
$$
Moreover
$$
 f(a)(\cos^2\phi_E+a^2\sin^2\phi_E)
 \geq a\operatorname{atanh}a
 \geq\frac{11}{24}\log23>2\log2.
$$
The last strict inequality follows from $23^{11}>2^{48}$, for example
by multiplying $(23^3)^3>2^{39}$ and $23^2>2^9$.
Combining with (13.1) proves a uniform positive order-$\theta^2$
gap $\ell_E-2I(P)>0$ for small $\theta$. Also
$\lambda_{\max}(P)=1-\alpha\to1$ uniformly.

Finally let $t=\tfrac12\|\rho-\tau\|_1\leq\theta^3$.
We use a self-contained finite-dimensional entropy-continuity estimate.
For density matrices $A,B$ at half trace distance $t>0$, the positive
and negative parts of $A-B$ give density matrices $\gamma_+,\gamma_-$
with $A-B=t(\gamma_+-\gamma_-)$. Thus
$$
 W=\frac{A+t\gamma_-}{1+t}=\frac{B+t\gamma_+}{1+t}
$$
is a common density matrix. Entropy concavity for one mixture and
the entropy-of-mixture upper bound for the other, as used in Corollary
12.3, give
$$
 |S(A)-S(B)|\leq B_d(t):=
 t\log d+(1+t)H_2\!\left(\frac{t}{1+t}\right).
$$
Indeed, subtracting the two mixture bounds gives
$S(A)-S(B)\leq t[S(\gamma_+)-S(\gamma_-)]+(1+t)H_2(t/(1+t))$,
and exchanging $A,B$ gives the reverse bound; both auxiliary entropies
lie in $[0,\log d]$. Set $B_d(0)=0$.
The identity
$$
 (1+t)H_2\!\left(\frac{t}{1+t}\right)
 =(1+t)\log(1+t)-t\log t
$$
shows that $B_d$ is increasing and $B_d(t)=O(t\log(1/t))$ as
$t\downarrow0$. This proof includes singular $A,B$.

Channels and partial traces contract trace distance. Therefore every
four-dimensional output entropy changes by at most $B_4(t)$ and every
one-qubit marginal entropy by at most $B_2(t)$. The absolute entropy
coefficients of $\Delta$ sum to eight in dimension four and twelve in
dimension two, so
$$
 |\Delta(\rho)-\Delta(\tau)|\leq8B_4(t)+12B_2(t)
 =O(\theta^3\Lambda)=o(\theta^2).
$$
Likewise
$$
 \begin{aligned}
 |I(P_\rho)-I(P_\tau)|&\leq B_4(t)+2B_2(t),\\
 |\ell_{E,\rho}-\ell_{E,\tau}|&\leq2B_2(t).
 \end{aligned}
$$
In particular the change in $\ell_E-2I(P)$ is at most
$2B_4(t)+6B_2(t)=o(\theta^2)$. Thus the uniform positive gaps of
order $\theta^2$ persist on the entire physical trace-distance ball.
The spectral maximum changes by at most
$2t$, preserving $\lambda_{\max}(P)>7/20$.
Since $c\geq7/16$, the uniform remainder in (13.5) and the
continuity error are at most $(7/32)\theta^2\Lambda$ after reducing
$\theta_0>0$. This proves all assertions simultaneously.

**Proposition 13.2 (Faithful, nonreal entangled inputs in the neighborhood).**
For every sufficiently small $\theta>0$ and every bias pair in Theorem
13.1, the neighborhood with $\phi_C=\phi_D=0$ contains a faithful,
nonreal state with negative partial transpose.

Proof.
Take
both phases zero, let $v_\theta$ be a real unit vector orthogonal to
$u_{\theta,0}$, and put $\varepsilon=\theta^3/4$,
$$
 \chi_\theta=\sqrt{1-\varepsilon^2}\,u_{\theta,0}\otimes u_{\theta,0}
       +i\varepsilon v_\theta\otimes v_\theta,\qquad
 \rho_\theta=(1-\varepsilon^2)|\chi_\theta\rangle\langle\chi_\theta|
                    +\varepsilon^2 I_4/4.
$$
Its trace distance from $\tau$ is at most
$\varepsilon+\varepsilon^2<\theta^3$. It is faithful. In the local real
Schmidt bases its partial transpose has eigenvalue
$$
 \varepsilon^2/4-\varepsilon(1-\varepsilon^2)^{3/2}<0
$$
for small $\theta$, so it is entangled; its imaginary cross term is
nonzero. The theorem therefore includes faithful entangled and
nonreal inputs, without asserting uniformity as $a\to1$ or $b\to1$.

The threshold $\theta_0$ is existential. Uniformity as $a\to1$ or
$b\to1$ is not asserted. The original unrestricted sign question in
Open assertion 12.5 remains unresolved outside the proved regions.

## 追加锚（本行以下为增补区）


## 14. A global pure-state source-moment criterion

Use the original complex states, independent biases, channels and exact
entropy budget of Definitions 1.1--1.2. Write $I(A)=I_A$ and retain
$\ell_E=S(R_E)-S(Q_E)$ from Definition 12.1. All logarithms are natural.

**Definition 14.1 (Pure-source moments).** For a unit vector
$|\psi\rangle\in\mathbb C^2\otimes\mathbb C^2$ and
$\rho=|\psi\rangle\langle\psi|$, put
$$
 x_C=\langle\psi|XI|\psi\rangle,\qquad
 x_D=\langle\psi|IX|\psi\rangle,\qquad
 \kappa=\langle\psi|XX|\psi\rangle,
$$
$$
 \tau_\psi=4\det\rho_C=4\det\rho_D,\qquad
 d_\psi=\max\{\max\{x_C^2,x_D^2\}-\kappa^2,0\}.
$$
These moments are real, and $0\leq\tau_\psi\leq1$.

**Theorem 14.2 (A source-moment sufficient condition).** For every
complex pure source and every independent $a,b\in[0,1]$,
$$
 (1-a^2)d_\psi\leq a^2\tau_\psi
 \quad\Longrightarrow\quad
 \Delta(\rho;a,b)\geq I(P)\geq0.
\tag{14.1}
$$

Proof.
First consider an arbitrary source, and set
$\pi_u=(1+(-1)^u a)/2$. The binary ensemble
$\{\pi_u,K^u\rho K^u\}_{u=0,1}$ has average $Q$ and Holevo
information $S(Q)-S(\rho)$. The global commutation $KL=LK$ gives
$$
 \Phi_b(K^u\rho K^u)=K^uPK^u.
$$
The resulting ensemble has average $R$ and Holevo information
$g=S(R)-S(P)$. Its actual partial trace to $E=C,D$ is the ensemble
$\{\pi_u,X^uP_EX^u\}_{u=0,1}$, whose Holevo information is $h_E$.
The standard finite-dimensional CPTP relative-entropy data-processing
inequality (Watrous, *The Theory of Quantum Information*), applied to
these ensembles, therefore gives
$$
 0\leq h_E\leq g\leq S(Q)-S(\rho).
\tag{14.2}
$$
This includes singular states and zero weights. Every positive-weight
ensemble member $A_u$ is supported on its average $\overline A$, since
$\overline A\succeq\pi_uA_u$. Thus all positive-weight terms in
$\chi=\sum_u\pi_uD(A_u\Vert\overline A)$ are finite; zero-weight terms
are omitted. In particular, the unchanged original deficit obeys the
general bound
$$
 \Delta\geq I(P)+I(Q)-g
 \geq I(P)+I(Q)-S(Q)+S(\rho).
$$
Hence $I(Q)+S(\rho)\geq S(Q)$ is sufficient for $\Delta\geq I(P)$
for arbitrary sources. We now derive a concrete sufficient condition
for pure sources from their actual spectra.

Write $e(t)=H_2((1+t)/2)$ for $0\leq t\leq1$; it is decreasing.
For pure $\rho$, the two possibly nonzero eigenvalues of $Q$ are
$(1\pm s)/2$, where
$$
 s^2=a^2+(1-a^2)\kappa^2.
\tag{14.3}
$$
Indeed, the $2\times2$ Gram matrix of
$\sqrt{\pi_0}|\psi\rangle,\sqrt{\pi_1}K|\psi\rangle$ has trace one
and determinant $(1-a^2)(1-\kappa^2)/4$. This also proves (14.3) in
rank-one degeneracies, and $S(Q)=e(s)$.

The two source margins have equal squared Bloch radius
$1-\tau_\psi$. If the Bloch vector on $E$ is $(x_E,y_E,z_E)$, its
actual image $Q_E$ has vector $(x_E,ay_E,az_E)$. Its squared radius is
$$
 s_E^2=a^2(1-\tau_\psi)+(1-a^2)x_E^2.
$$
Consequently
$$
 s^2-s_E^2=a^2\tau_\psi+(1-a^2)(\kappa^2-x_E^2).
\tag{14.4}
$$
The hypothesis of (14.1) makes (14.4) nonnegative for both margins.
The monotonicity of $e$ gives
$$
 S(Q_C)\geq S(Q),\qquad S(Q_D)\geq S(Q).
\tag{14.5}
$$
For this pure source, (14.2) reads $0\leq h_E\leq g\leq S(Q)$.
Retaining both full endpoint mutual informations, expand exactly:
$$
 \begin{aligned}
 \Delta={}&I(P)+[S(Q_C)-S(Q)]+[S(Q_D)-S(Q)]\\
          &+[S(Q)-g]+2(g-h_C)+2(g-h_D).
 \end{aligned}
\tag{14.6}
$$
The three middle entropy terms sum to $I(Q)-g$, and the final two
terms sum to $4g-2h$. Thus (14.6) is precisely the original
$I(P)+I(Q)+3g-2h$, with unchanged coefficients. Every term after
$I(P)$ is nonnegative by (14.2) and (14.5); subadditivity gives
$I(P)\geq0$.

No division by $1-a^2$, a spectral value or $\tau_\psi$ has been
used. At $a=1$, $g=h_E=S(Q)=0$. At $a=0$, the hypothesis becomes
$d_\psi=0$. Both $b=0,1$, arbitrary complex amplitudes and all zero
spectra are included.

**Corollary 14.3 (All biases and an entanglement-dependent interval).**
Every pure source satisfying
$$
 \max\{|x_C|,|x_D|\}\leq|\kappa|
\tag{14.7}
$$
satisfies $\Delta\geq I(P)\geq0$ for all independent $a,b\in[0,1]$.
For every entangled pure source, $\tau_\psi>0$, the same conclusion
holds for every $b\in[0,1]$ whenever
$$
 a\geq\sqrt{\frac{d_\psi}{\tau_\psi+d_\psi}}.
$$
The lower endpoint is zero when $d_\psi=0$.

Proof.
Condition (14.7) is exactly $d_\psi=0$. For $\tau_\psi>0$, rearranging
$(1-a^2)d_\psi\leq a^2\tau_\psi$ gives the displayed interval.
Apply Theorem 14.2.

**Proposition 14.4 (An all-bias family through the full entanglement range).**
Let $|u\rangle,|v\rangle$ be unit qubit vectors with
$\langle u|X|u\rangle=\langle v|X|v\rangle=0$. For every
$0\leq\lambda\leq1$ and $\chi\in\mathbb R$, the source
$$
 |\psi\rangle=\sqrt\lambda\,|u\rangle|v\rangle
       +e^{i\chi}\sqrt{1-\lambda}\,X|u\rangle X|v\rangle
$$
satisfies (14.7), hence the original inequality for all independent
biases.

Proof.
Each local pair $u,Xu$ and $v,Xv$ is orthonormal. Both margins are
mixtures of these pairs, and each constituent has zero $X$
expectation. Thus $x_C=x_D=0$ and $d_\psi=0$. Their eigenvalues
are $\lambda,1-\lambda$, so $\tau_\psi=4\lambda(1-\lambda)$ covers
$[0,1]$. The relative phase and both local angles on the $YZ$ circle
are unrestricted.

**Proposition 14.5 (A strict residual intersection, open among pure sources).**
The region of Theorem 14.2 contains an open set of complex entangled
pure sources and independent biases inside the residual region
(12.10), with biases outside the interval of Theorem 13.1.

Proof.
Start with the exact product source $|\psi_0\rangle=|uv\rangle$, where
$$
 |u\rangle=\frac{5|0\rangle+i|1\rangle}{\sqrt{26}},\qquad
 |v\rangle=\frac{7|0\rangle+i|1\rangle}{\sqrt{50}},\qquad
 a_0=\frac{999}{1000},\qquad b_0=0.
$$
Here $x_C=x_D=\kappa=0$, while $z_C=12/13$ and $z_D=24/25$.
Thus (14.7) applies. The binary mixture defining $P$ has smaller
nonzero eigenvalue $(1-z_Cz_D)/2=37/650$, so
$$
 M=\lambda_{\max}(P)=\frac{613}{650}>\frac7{20}.
$$
The source marginal vectors have unit length, whereas the $b_0=0$
channel retains only their $Z$ coordinate. The smaller eigenvalues
of $P_C,P_D$ are $1/26,1/50$; those of $Q_C,Q_D$ are $1/2000$;
those of $R_C,R_D$ are $253/6500,64/3125$. Therefore
$$
 \begin{aligned}
 I(P)&=H_2(1/26)+H_2(1/50)-H_2(37/650),\\
 \ell_C&=H_2(253/6500)-H_2(1/2000),\\
 \ell_D&=H_2(64/3125)-H_2(1/2000).
 \end{aligned}
\tag{14.8}
$$
The following strict rational intervals make the comparison exact.
In the last two columns every integer is divided by $10^6$:

| $q$ | lower bound for $H_2(q)$ | upper bound for $H_2(q)$ |
| --- | ---: | ---: |
| $1/26$ | $163023$ | $163024$ |
| $1/50$ | $98039$ | $98040$ |
| $37/650$ | $218415$ | $218416$ |
| $253/6500$ | $164506$ | $164507$ |
| $64/3125$ | $99901$ | $99902$ |
| $1/2000$ | $4300$ | $4301$ |

Here is a reconstruction using only rational arithmetic. For any
positive rational logarithm argument $x$, choose an integer $k$ so
that $y=2^kx\in[1,2]$, and use $\log x=\log y-k\log2$.
For $t=(y-1)/(y+1)\in[0,1/3]$, set
$$
 L(y)=2\sum_{j=0}^{15}\frac{t^{2j+1}}{2j+1},\qquad
 U(y)=L(y)+\frac{2t^{33}}{33(1-t^2)}.
$$
Expanding $\log y=2\operatorname{atanh}t$ gives
$L(y)\leq\log y\leq U(y)$: the positive tail is bounded by the
geometric sum with every denominator replaced by $33$. Bound
$\log2$ by the same formulas at $y=2$, reversing interval endpoints
when multiplying by a negative number. Apply these intervals to
$-q\log q-(1-q)\log(1-q)$ and round outward to denominator $10^6$;
cross-multiplication yields the six rows above.

Equation (14.8) consequently gives
$$
 \frac{42646}{10^6}<I(P)<\frac{42649}{10^6},\qquad
 \ell_C>\frac{160205}{10^6},\qquad
 \ell_D>\frac{95600}{10^6}.
$$
In particular $2I(P)<\ell_C,\ell_D$, and the original deficit obeys
$\Delta\geq I(P)>42/1000$.

To obtain an open entangled intersection, put
$$
 |\psi_\varepsilon\rangle
 =\sqrt{1-\varepsilon^2}\,|\psi_0\rangle
      +\varepsilon K|\psi_0\rangle.
$$
For $0<\varepsilon<1$, the local pairs are orthonormal, so these
sources are entangled and
$$
 x_C=x_D=0,\qquad
 \kappa=2\varepsilon\sqrt{1-\varepsilon^2}>0.
$$
For sufficiently small positive $\varepsilon$, the strict residual
inequalities persist by entropy continuity. They also persist for
sufficiently small positive $b$ and small perturbations of $a_0$.
Moreover $\max\{x_C^2,x_D^2\}<\kappa^2$ is strict, so it persists
under all sufficiently small complex pure-state perturbations.
Entanglement is open at each of these pure sources. This gives the
claimed relative open set; $a_0>23/24$ and small $b<1/4$ keep it
outside the bias rectangle of Theorem 13.1.

**Corollary 14.6 (A necessary additional condition for a pure counterexample).**
Every pure counterexample to the original inequality must satisfy
$$
 (1-a^2)\bigl(\max\{x_C^2,x_D^2\}-\kappa^2\bigr)>a^2\tau_\psi,
$$
in addition to the preceding residual conditions.

Proof.
The contrapositive of Theorem 14.2 requires
$(1-a^2)d_\psi>a^2\tau_\psi\geq0$. Thus $d_\psi>0$, and its
positive-part operation can be removed in this strict inequality.
The preceding proved sufficient regions also exclude a counterexample.

**Proposition 14.7 (An explicit physical mixed-state ball in the residual region).**
Let $\rho_0=|\psi_0\rangle\langle\psi_0|$ and $a_0=999/1000$
be the exact product source and bias in Proposition 14.5. Put
$\eta=1/20000$. Every physical complex density matrix and independent
biases satisfying
$$
 \tfrac12\|\rho-\rho_0\|_1\leq\eta,\qquad
 |a-a_0|\leq\eta,\qquad 0\leq b\leq\eta
$$
obey
$$
 \Delta(\rho;a,b)>\frac{19}{1000},\qquad
 M>\frac7{20},\qquad
 \ell_E-2I(P)>\frac{651}{500000}\quad(E=C,D).
\tag{14.9}
$$
This region contains faithful states with negative partial transpose
and a nonempty open subset of the physical state-and-bias domain.

Proof.
For any density matrix $A$, changing the parameter of either binary
unitary channel by $s$ changes its output by half trace distance at
most $|s|/2$, since the difference is
$(s/2)(A-UAU^{\dagger})$ and $\|A-UAU^{\dagger}\|_1\leq2$.
Channel contractivity and the triangle inequality therefore bound
the distance of $P,Q,R$ from their values at $(\rho_0,a_0,0)$ by,
respectively,
$$
 \eta+b/2,\qquad \eta+|a-a_0|/2,\qquad
 \eta+(b+|a-a_0|)/2.
$$
All are at most $\delta=1/10000$, as are the marginal distances.
The entropy-continuity estimate proved in Theorem 13.1 gives
$$
 B_d(\delta)=\delta\log d+(1+\delta)\log(1+\delta)
                   -\delta\log\delta.
$$
The same rational logarithm series used in Proposition 14.5 gives
$\log2<694/1000$, $\log4<1387/1000$ and
$\log10000<9211/1000$. Since $\log(1+\delta)\leq\delta$, these imply
$$
 B_2(\delta)<\frac{109051}{10^8}<\frac{1091}{10^6},\qquad
 B_4(\delta)<\frac{115981}{10^8}<\frac{1160}{10^6}.
$$
The absolute entropy coefficients in the original deficit and in
$\ell_E-2I(P)$ consequently give errors bounded by
$$
 8B_4(\delta)+12B_2(\delta)<\frac{23}{1000},\qquad
 2B_4(\delta)+6B_2(\delta)<\frac9{1000}.
$$
At the exact base point Proposition 14.5 gives
$\Delta\geq I(P)>42/1000$ and, for both margins,
$\ell_E-2I(P)>10302/10^6$. Subtracting the displayed errors proves
the deficit and marginal inequalities in (14.9). The largest
eigenvalue changes by at most $2\delta$, so
$$
 M\geq\frac{613}{650}-2\delta=\frac{61287}{65000}>\frac7{20}.
$$

For a faithful entangled member, retain $u,v$ from Proposition 14.5,
put $\varepsilon=1/50000$, and set
$$
 |\chi\rangle=\sqrt{1-\varepsilon^2}\,|uv\rangle
                 +i\varepsilon|Xu\,Xv\rangle,\qquad
 \rho_*=(1-\varepsilon^2)|\chi\rangle\langle\chi|
                         +\varepsilon^2 I_4/4.
$$
The two local pairs are orthonormal. Hence the distance from $\rho_0$
is at most $\varepsilon+\varepsilon^2<\eta$, while
$\rho_*\succeq\varepsilon^2I_4/4$. In local Schmidt coordinates its
partial transpose has eigenvalue
$$
 \varepsilon^2/4-\varepsilon(1-\varepsilon^2)^{3/2}<0.
$$
Thus $\rho_*$ is faithful and entangled. Choose $a=a_0$ and
$0<b<\eta$. The strict distance and parameter inequalities, positivity
and the negative partial-transpose eigenvalue persist under sufficiently
small physical perturbations. This gives a nonempty open subset.

The unrestricted pure-state sign, and therefore the original mixed-state
sign of Open assertion 12.5, remain unresolved outside the proved regions.

## 追加锚（本行以下为增补区）


## 15. Bell-sign covariance and neighborhoods uniform over both biases

Use Definitions 1.1--1.2 with the original independent $a,b\in[0,1]$,
complex density matrices and entropy deficit. Write
$I(A)=S(A_C)+S(A_D)-S(A)$, including for the source $A=\rho$.

**Definition 15.1 (Bell-sign moments).** For any source put
$$
 \kappa=\operatorname{tr}(\rho K),\qquad
 \lambda=\operatorname{tr}(\rho L),\qquad
 \mu=\operatorname{tr}(\rho KL),\qquad
 \delta=\mu-\kappa\lambda,\qquad
 \beta=(1-|\kappa|)(1-|\lambda|).
$$
These are real, because $K,L$ are commuting Hermitian involutions;
$KL=-YY$. For a pure product with unit local Bloch vectors
$(x_E,y_E,z_E)$ they become
$$
 \kappa=x_Cx_D,\qquad \lambda=z_Cz_D,\qquad \mu=-y_Cy_D.
$$
For a general pure source write
$e_0=S(\rho_C)=S(\rho_D)$.

**Theorem 15.2 (An exact independent-control entropy decomposition).**
For every physical source define
$$
 \begin{aligned}
 A_E&=S(P_E)+S(Q_E)-S(R_E)-S(\rho_E),\\
 B_E&=S(Q)-S(\rho)-S(Q_E)+S(\rho_E),\\
 J_0&=S(P)+S(Q)-S(R)-S(\rho).
 \end{aligned}
$$
All $A_E,B_E,J_0$ are nonnegative, and the unchanged deficit is
$$
 \Delta=I(P)+I(\rho)+B_C+B_D+2A_C+2A_D-3J_0.
\tag{15.1}
$$

Proof.
Let $U,V$ be independent binary controls with probabilities
$\pi_u=(1+(-1)^u a)/2$ and $\eta_v=(1+(-1)^v b)/2$, and form
$$
 \Omega_{UVCD}=\sum_{u,v}\pi_u\eta_v|uv\rangle\langle uv|
       \otimes K^uL^v\rho L^vK^u.
$$
The conditional quantum entropies given $U$, given $V$, and given
$(U,V)$ are, respectively, $S(P),S(Q),S(\rho)$. Their marginal
counterparts are $S(P_E),S(Q_E),S(\rho_E)$. Independence of the
controls therefore gives
$$
 A_E=I(U:V\mid E)_\Omega,\qquad
 J_0=I(U:V\mid CD)_\Omega.
$$
Their nonnegativity is finite-dimensional strong subadditivity
(Lieb and Ruskai, *Proof of the strong subadditivity of
quantum-mechanical entropy*). The two terms in $B_E$ are the Holevo
informations of the actual $U$-ensemble before and after partial
trace. Relative-entropy data processing makes $B_E\geq0$; see
Watrous, *The Theory of Quantum Information*. Every positive-weight
ensemble member is supported on its average, so the relative
entropies are finite. Zero-weight members are omitted.

Substitute the displayed definitions and
$I(\rho)=S(\rho_C)+S(\rho_D)-S(\rho)$ into the right side of (15.1).
The joint terms are $3S(R)-4S(P)-S(Q)$, and the marginal terms are
$\sum_E[3S(P_E)+S(Q_E)-2S(R_E)]$. All source entropy terms cancel.
Thus (15.1) retains the original coefficients and both full endpoint
mutual informations of (1.4).

For a pure source, put $J=S(P)+S(Q)-S(R)=J_0$. Equation (15.1) gives
$$
 \Delta\geq I(P)+2e_0-3J.
\tag{15.2}
$$
Equivalently, with $s_E=S(P_E)+S(Q_E)-S(R_E)$ and
$F_Q=S(Q)-I(Q)$, the exact identity is
$$
 \Delta=I(P)+F_Q+2(s_C+s_D)-3J.
$$
Here $s_E=A_E+e_0$ and $F_Q=B_C+B_D-2e_0$, which gives (15.2)
without discarding a negative endpoint term.

**Lemma 15.3 (The pure-source Gram comparison).**
For a pure source, $J\geq0$. If $\delta=0$, then $J=0$. If
$\beta>0$ and $0<\varepsilon=|\delta|/\beta\leq1$, then
$$
 J\leq\varepsilon\min\{S(P),S(Q)\}\leq\varepsilon\log2.
\tag{15.3}
$$
If $\beta=0$, necessarily $\delta=0$.

Proof.
The joint spectral probabilities of the commuting signs are
$$
 p_{kl}=\operatorname{tr}\!\left(\rho\frac{(I+kK)(I+lL)}4\right)
       =\frac{1+k\kappa+l\lambda+kl\mu}{4},\qquad k,l\in\{\pm1\}.
$$
They are nonnegative and sum to one. Introduce unit control vectors
$$
 |\xi_k\rangle=\sqrt{\pi_0}|0\rangle+k\sqrt{\pi_1}|1\rangle,
 \qquad
 |\zeta_l\rangle=\sqrt{\eta_0}|0\rangle+l\sqrt{\eta_1}|1\rangle,
$$
and the control matrix
$$
 G=\sum_{k,l}p_{kl}|\xi_k\rangle\langle\xi_k|
                         \otimes|\zeta_l\rangle\langle\zeta_l|.
\tag{15.4}
$$
For $\rho=|\psi\rangle\langle\psi|$, its $(uv,u'v')$ entry is
$$
 \sqrt{\pi_u\eta_v\pi_{u'}\eta_{v'}}
       \sum_{k,l}p_{kl}k^{u+u'}l^{v+v'}.
$$
This is the actual overlap of the four vectors
$\sqrt{\pi_u\eta_v}K^uL^v|\psi\rangle$. Their frame operator is
$R$, so $G$ and $R$ have the same nonzero spectrum. The two margins
$G_A,G_B$ are the binary Gram matrices of $Q,P$, respectively.
Consequently
$$
 S(G)=S(R),\qquad S(G_A)=S(Q),\qquad S(G_B)=S(P),\qquad
 J=I(A:B)_G.
\tag{15.5}
$$
These facts include zero control weights and zero eigenvalues.

Set $p^0_{kl}=(1+k\kappa)(1+l\lambda)/4$. Then
$$
 p_{kl}=p^0_{kl}+\delta kl/4,\qquad p^0_{kl}\geq\beta/4.
$$
When $\delta=0$, the preparation in (15.4) factorizes as
$G=G_A\otimes G_B$, proving $J=0$. Otherwise assume the hypotheses
on $\varepsilon$, and define
$$
 p^1_{kl}=p^0_{kl}+\operatorname{sgn}(\delta)\beta kl/4.
$$
This is a probability distribution: it is nonnegative, and the
perturbation has zero total mass and zero one-coordinate marginals.
Moreover $p=(1-\varepsilon)p^0+\varepsilon p^1$. Preparing the
same local vectors gives
$$
 G=(1-\varepsilon)G_A\otimes G_B+\varepsilon G^1,
$$
where $G^1$ is separable and has the same margins $G_A,G_B$.
Relative-entropy convexity, in its usual finite-dimensional scope
(Watrous, *The Theory of Quantum Information*), gives
$$
 J=D(G\Vert G_A\otimes G_B)
 \leq\varepsilon D(G^1\Vert G_A\otimes G_B)
 =\varepsilon I(A:B)_{G^1}.
$$
For the last mutual information retain a classical label $(k,l)$
preparing the product pure states. Data processing from that label
to $B$ gives $I(A:B)_{G^1}\leq I(A:kl)=S(G_A)$, since its
conditional $A$-states are pure. Interchanging $A,B$ gives the other
bound in (15.3). Both compared states are supported on
$\operatorname{supp}G_A\otimes\operatorname{supp}G_B$, so these
relative entropies remain finite when the margins are singular.
Finally $P,Q$ are binary mixtures of pure states, hence each has
entropy at most $\log2$.

If $\beta=0$, at least one of the two classical signs is
deterministic in $p$. Its product expectation then satisfies
$\mu=\kappa\lambda$, so $\delta=0$ as claimed.

**Theorem 15.4 (A product-source region uniform over both biases).**
For every pure product source, the source-only condition
$$
 3(1+|\lambda|)|\mu-\kappa\lambda|
 \leq(1-|\kappa|)(1-z_C^2)(1-z_D^2)
\tag{15.6}
$$
implies $\Delta\geq0$ for all independent $a,b\in[0,1]$.
If $\delta=0$, the stronger bound $\Delta\geq I(P)$ holds for all
these biases. Condition (15.6) contains an open neighborhood, among
product sources, of every $\delta=0$ source with $|\kappa|<1$ and
$|z_C|,|z_D|<1$.

Proof.
The case $\delta=0$ follows directly from (15.2), since $e_0=0$.
This also handles $\beta=0$. For the remaining case put
$$
 u=1-z_C^2,\quad v=1-z_D^2,\quad
 w=u+v-uv=1-\lambda^2,\quad \alpha=uv/w.
$$
Here $w>0$ and $0\leq\alpha\leq1$. Let
$$
 f(t)=H_2\!\left(\frac{1+\sqrt{1-t}}2\right),\qquad0\leq t\leq1.
$$
It is continuous and concave, with $f(0)=0$. On the interior,
$$
 f'(t)=\frac12\int_0^1\frac{ds}{1-(1-t)s^2},\qquad
 f''(t)=-\frac12\int_0^1\frac{s^2\,ds}{[1-(1-t)s^2]^2}\leq0;
$$
continuity extends concavity to the endpoints. Writing $c=1-b^2$,
the exact binary product-source spectra give
$$
 S(P_C)=f(cu),\qquad S(P_D)=f(cv),\qquad S(P)=f(cw).
$$
Since $u,v\leq w$, concavity gives
$f(cu)\geq(u/w)f(cw)$ and $f(cv)\geq(v/w)f(cw)$. Thus
$$
 I(P)\geq\alpha S(P).
\tag{15.7}
$$
Condition (15.6) is exactly $3\varepsilon\leq\alpha$ after
cancelling the positive factors in
$w=(1-|\lambda|)(1+|\lambda|)$. It ensures
$\varepsilon\leq1/3$, so Lemma 15.3 applies. Equations (15.2),
(15.3) and (15.7) yield
$$
 \Delta\geq(\alpha-3\varepsilon)S(P)\geq0.
$$
If $w=0$, both $Z$-signs of the product are deterministic and
$\delta=0$, already handled without division. All bias endpoints
and singular spectra are included. At the stated $\delta=0$ sources
the right side of (15.6) is positive, so the source condition is
strict and persists under small product-source perturbations.

**Theorem 15.5 (An all-pure source condition and the independent-sign bound).**
For every complex pure source with $\delta=0$,
$$
 \Delta\geq I(P)+2e_0
 \quad\text{for every independent }a,b\in[0,1].
\tag{15.8}
$$
For $\beta>0$, the source-only condition
$$
 3(\log2)|\delta|\leq2e_0\beta
\tag{15.9}
$$
implies $\Delta\geq I(P)\geq0$ for every independent pair of biases.
If (15.9) is strict, the uniform lower margin is
$$
 m=2e_0-3(\log2)|\delta|/\beta>0,\qquad \Delta\geq I(P)+m.
\tag{15.10}
$$
In particular, (15.9) is strict at every entangled pure source with
$\beta>0$ and $\delta=0$, and persists in a neighborhood among all
complex pure sources.

Proof.
For $\delta=0$, Lemma 15.3 gives $J=0$, so (15.2) proves (15.8),
including $\beta=0$. Otherwise $e_0\leq\log2$ and (15.9) imply
$\varepsilon=|\delta|/\beta\leq2/3$. Lemma 15.3 therefore applies,
and $3J\leq3\varepsilon\log2\leq2e_0$. This proves the conclusion
and the margin (15.10). The strictness and neighborhood assertion
follow from continuity of the moments and entropy with $\beta>0$.

**Proposition 15.6 (A nonplanar product and an entangled residual bridge).**
The new source regions intersect the previous residual domain at
biases outside Theorem 13.1 and sources outside the sufficient
conditions and mixed ball of §14. The pure-source intersection has
nonempty interior among complex pure sources.

Proof.
Take the exact unit Bloch vectors
$$
 n_C=\left(\frac5{\sqrt{313}},\frac{60}{13\sqrt{313}},\frac{12}{13}\right),
 \qquad
 n_D=\left(\frac7{\sqrt{1201}},-\frac{168}{25\sqrt{1201}},\frac{24}{25}\right),
$$
and let $\rho_0=|\psi_0\rangle\langle\psi_0|$ be their product.
Their unit norms follow from
$x_E^2=(1-z_E^2)/(1+z_E^2)$ and $y_C=x_Cz_C$, $y_D=-x_Dz_D$.
All six components are nonzero, the local vectors are unequal, and
$\mu=\kappa\lambda$. Both $\beta$ and the right side of (15.6) are
positive. Thus this product lies in the interior of the all-bias
product region.

At $a_0=999/1000$, $b_0=0$, the $P$-spectrum and $I(P)$ depend
only on $z_C=12/13,z_D=24/25$. Proposition 14.5 therefore gives
$$
 M=613/650>7/20,\qquad 42/1000<I(P)<43/1000.
$$
The actual marginal radii give
$S(R_E)=e(a_0z_E)\geq e(z_E)$ and $S(Q_E)\leq e(a_0)$.
The rational entropy intervals in Proposition 14.5 give
$e(z_E)\geq H_2(1/50)>98/1000$ and
$e(a_0)=H_2(1/2000)<5/1000$. Hence
$$
 \ell_C,\ell_D>93/1000>86/1000>2I(P).
\tag{15.11}
$$
Thus the old residual conditions are strict. The source-moment
condition (14.1) fails: $\tau_{\psi_0}=0$ and
$d_0=\max\{x_C^2,x_D^2\}-\kappa^2>0$, whereas $a_0<1$.
Also $a_0>23/24$, outside the bias rectangle of Theorem 13.1.

To obtain entangled sources, put
$$
 E_{++}=\frac{(I+K)(I+L)}4=|\Phi^+\rangle\langle\Phi^+|,
 \quad |\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2,
$$
$$
 W_\theta=I+(e^{i\theta}-1)E_{++},\qquad
 |\psi_\theta\rangle=W_\theta|\psi_0\rangle.
$$
This unitary commutes with $K,L,KL$, so $\kappa,\lambda,\mu$ and
$\beta>0$ are fixed, and $\delta=0$ throughout. Let $A$ be the
$2\times2$ coefficient matrix of $\psi_0$, and $s=A_{00}+A_{11}$.
Writing $t=e^{i\theta}-1$, the diagonal entries each gain $ts/2$.
Since $\det A=0$,
$$
 \det A_\theta=\frac{s^2}{4}(t^2+2t)
              =\frac{s^2}{4}(e^{2i\theta}-1).
$$
Moreover $p_{++}=|s|^2/2=(1+\kappa)(1+\lambda)/4>0$. Thus
$$
 \tau_{\psi_\theta}=4|\det A_\theta|^2
                   =4p_{++}^2\sin^2\theta>0
$$
for small nonzero $\theta$. These are entangled pure sources with
$e_\theta>0$ satisfying (15.9) strictly, and therefore have a full
pure-source neighborhood covered by Theorem 15.5.

For small $\theta$, (15.11) and the old spectral condition persist
by entropy continuity. The old condition (14.1) still fails:
$d_\theta\to d_0>0$ while $\tau_{\psi_\theta}\to0$, so
$(1-a_0^2)d_\theta>a_0^2\tau_{\psi_\theta}$. Small positive $b$
and small perturbations of $a_0$ preserve these strict inequalities.
Finally $x_C(\psi_0)=5/\sqrt{313}>1/4$, whereas the center of the
mixed ball in Proposition 14.7 has $x_C=0$. The half trace distance
between these sources is at least $|x_C|/2>1/8$, by testing $XI$.
This separation persists for small $\theta$, and excludes that old
ball of radius $1/20000$. All stated exclusions and strict residual
conditions persist in a sufficiently small pure-source neighborhood.

**Theorem 15.7 (Physical mixed-state balls uniform over every bias).**
Let $\sigma$ be a pure source for which either $\delta=0$ and
$e_0>0$, or $\beta>0$ and (15.9) is strict. Define $m=2e_0$ in
the first case, and use (15.10) in the second; in either case $m>0$.
For any $0<t_0\leq1$ satisfying
$$
 E(t_0):=8B_4(t_0)+12B_2(t_0)<m/2,
\tag{15.12}
$$
every physical complex density matrix with
$\tfrac12\|\rho-\sigma\|_1\leq t_0$ satisfies
$$
 \Delta(\rho;a,b)>m/2
 \quad\text{for all independent }a,b\in[0,1].
\tag{15.13}
$$
Here $B_d(t)=t\log d+(1+t)H_2(t/(1+t))$ is the entropy-continuity
bound proved in Theorem 13.1. Such a positive $t_0$ always exists.
The ball contains faithful states with negative partial transpose.
For the entangled centers of Proposition 15.6, a sufficiently small
such ball also intersects the old residual domain in a physical
open set.

Proof.
Theorem 15.5 gives $\Delta(\sigma;a,b)\geq m$, uniformly over the
entire bias square, since $I(P)\geq0$. For each fixed pair of biases,
channel contractivity bounds every output trace distance by $t_0$,
and partial trace gives the same bound for each marginal. The
absolute entropy coefficients of the original deficit are eight in
dimension four and twelve in dimension two. Thus
$$
 |\Delta(\rho;a,b)-\Delta(\sigma;a,b)|\leq E(t_0)<m/2,
$$
which proves (15.13) without restricting either bias. The function
$E$ tends to zero with $t_0$, so (15.12) has positive solutions.
This extension to mixed states uses entropy continuity.

Every center in the theorem is entangled. Write its nonzero Schmidt
coefficients as $\sqrt r,\sqrt{1-r}$, where $0<r<1$, and put
$s=\sqrt{r(1-r)}>0$. For sufficiently small $\gamma>0$, the state
$$
 \rho_\gamma=(1-\gamma)\sigma+\gamma I_4/4
$$
is faithful and has half trace distance $3\gamma/4<t_0$ from
$\sigma$. Its partial transpose has eigenvalue
$\gamma/4-(1-\gamma)s<0$ whenever
$\gamma<4s/(1+4s)$. These strict properties persist under small
physical perturbations.

At the centers from Proposition 15.6 the old residual inequalities
and exclusions hold strictly at suitable interior biases. Reduce
$t_0$ further to preserve them at those biases, and use continuity
also in the biases. This yields the asserted physical open
intersection, while the positivity conclusion (15.13) continues to
hold throughout the full independent bias square.

**Proposition 15.8 (The mixed-source control matrix has a different budget).**
The control matrix (15.4), formed from the moments of a mixed source,
can have zero mutual information while $J_0>0$.

Proof.
Take $\rho=(I_4+YI)/4=|+y\rangle\langle+y|\otimes I_2/2$
and $a=b=0$. Then $S(\rho)=\log2$ and
$\kappa=\lambda=\mu=\delta=0$. Formula (15.4) gives $G=I_4/4$,
so $I(A:B)_G=0$. Direct Pauli conjugation gives
$P=Q=R=I_4/4$, and therefore
$$
 J_0=S(P)+S(Q)-S(R)-S(\rho)=\log2.
$$
The original deficit is zero in this example. Thus the pure-source
spectral identification (15.5) supplies no mixed-source comparison
$J_0\leq I(A:B)_G$.

The unrestricted pure-product, pure-source and mixed-source sign
questions remain open outside the proved regions. All conclusions in
this section concern the original deficit with its independent biases
and unchanged endpoint terms.

## 追加锚（本行以下为增补区）

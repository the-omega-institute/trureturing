# AURIC--Robin R4：读出与余量作为联合关系

> 来源：用户于 2026-11-06（Asia/Singapore）在本会话提供的 AURIC--Robin R4 LaTeX 研究工作稿；原稿未另署作者或模型。本文为参考输入，Lean 是仓库的数学真源；本次仅转换 Markdown，未作形式化认证。正文中的固定快照、项目核读叙述与理论结论均保留原稿口径；原稿不含 TikZ 图；本次保留全部正文与数学内容，不新增外部图像。

**AURIC–Robin R4**\
Readout and residual as a joint relation\
Research note\| November 2026 (Singapore)

## 1　The joint relation is the object to retain

Let $\Omega_I$ be the source states consistent with a protocol $I$. For a target $T$ and readout $r$, define the exact residual $e=T-r$. The joint feasible relation is

$$
\mathcal R_I=\{(r(\omega),e(\omega)):\omega\in\Omega_I\}.
$$

If $R_I$ and $E_I$ are its two marginal ranges, then $\mathcal R_I\subseteq R_I\times E_I$, usually strictly. For every objective $\Phi$ and certified enclosure $\mathcal R_I\subseteq\widehat\mathcal R_I\subseteq R_I\times E_I$,

$$
\inf_{R_I\times E_I}\Phi\ \le\
 \inf_{\widehat\mathcal R_I}\Phi\ \le\ \inf_{\mathcal R_I}\Phi.
$$

Thus a relation can improve an objective bound without narrowing either marginal interval. The proof is monotonicity of the infimum under inclusion.

**Example.** Let $c\in[1,2]$, $t\in[-1,1]$, $r=c+t$, and $e=-t$. The true total is $r+e=c\in[1,2]$. Marginal intervals alone give $r\in[0,3]$, $e\in[-1,1]$, hence the weaker enclosure $[-1,4]$. Its negative endpoint combines values that cannot share the same source. Retaining common uncertainty symbols is a central idea of affine arithmetic [\[1\]](#ref-aa); no novelty of this general numerical principle is asserted.

For a fixed source and target, write $\delta_m=r_{m+1}-r_m$. Then

$$
\boxed{r_{m+1}=r_m+\delta_m,\qquad
 e_{m+1}=e_m-\delta_m,\qquad r_m+e_m=T.}
$$

An error radius $\rho_m$ is a different object: $|e_m|\le\rho_m$ does not identify $e_m$ with $\rho_m$. Also, an equation defining $e=T-r$ gives no new bound on an otherwise unrestricted target $T$.

## 2　A general relational refinement theorem

Suppose certified intervals containing a fixed real target are nested:

$$
L_m\le T\le U_m,\qquad
 L_m\le L_{m+1}\le U_{m+1}\le U_m.
$$

Define $W_m=U_m-L_m$, and the complementary distances

$$
e_m^-=T-L_m,\qquad e_m^+=U_m-T.
$$

They satisfy the exact relation

$$
\boxed{e_m^-\ge0,\quad e_m^+\ge0,\quad e_m^-+e_m^+=W_m.}
$$

If $a_m=L_{m+1}-L_m$ and $b_m=U_m-U_{m+1}$, then

$$
e_{m+1}^-=e_m^--a_m,\quad e_{m+1}^+=e_m^+-b_m,\quad
 W_{m+1}=W_m-a_m-b_m.
$$

#### 定理 2.1：Normalized refinement

When $W_m>0$ and $a_m+b_m>0$, put

$$
q_m=\frac{T-L_m}{W_m},\qquad
 \eta_m=\frac{a_m+b_m}{W_m},\qquad
 \theta_m=\frac{a_m}{a_m+b_m}.
$$

If $W_{m+1}>0$, then

$$
\boxed{q_m=\eta_m\theta_m+(1-\eta_m)q_{m+1}.}
$$

**证明。**

The identity $T-L_m=a_m+(T-L_{m+1})$ gives the formula after division by $W_m$. All weights and normalized positions lie in $[0,1]$.

$\square$

If $a_m+b_m=0$, no refinement occurred. If $W_{m+1}=0$, the target is exactly determined and no $q_{m+1}$ is defined. If $W_m=0$, stop.

#### 命题 2.2：Center–radius coupling

For $[L_m,U_m]=[c_m-\rho_m,c_m+\rho_m]$, nesting is equivalent to

$$
\boxed{|c_{m+1}-c_m|+\rho_{m+1}\le\rho_m.}
$$

**证明。**

The two endpoint inequalities say $-(\rho_m-\rho_{m+1})\le c_{m+1}-c_m\le\rho_m-\rho_{m+1}$.

$\square$

This is a constraint on a certified center and radius, in addition to the exact residual identity $e_{m+1}=e_m-(c_{m+1}-c_m)$.

If $\eta_m\ge\eta_0>0$ uniformly, then $W_m\le(1-\eta_0)^mW_0$. Nesting alone does not imply this rate, or even $W_m\to0$. If $W_m\to0$ and $T\ne0$, a finite stage certifies its strict sign; equality $T=0$ need not be finitely certified. Normalized positions $q_m$ need not converge even when the widths tend to zero.

## 3　A positive three-coordinate lift for a signed tail

Let $f,g$ be measurable on $[x_0,\infty)$, with $g\ge|f|$ and $\int_{x_0}^\infty g<\infty$. Define

$$
J(y)=\int_y^\infty f(t)\,dt,\quad
 H(y)=\int_y^\infty g(t)\,dt,\quad
 \mathcal B(y,z)=\int_y^z f(t)\,dt.
$$

Fix a base $x\ge x_0$. For $y\ge x$, put

$$
P_y=\frac{H(x)-H(y)+\mathcal B(x,y)}2,\quad
 M_y=\frac{H(x)-H(y)-\mathcal B(x,y)}2,\quad R_y=H(y).
$$

#### 定理 3.1：Common-budget lift

The three coordinates are nonnegative and obey

$$
\boxed{P_y+M_y+R_y=H(x),\qquad \mathcal B(x,y)=P_y-M_y.}
$$

For $z\ge y$, let $D=H(y)-H(z)$ and $B=\mathcal B(y,z)$. Then

$$
\boxed{\Delta P=\frac{D+B}2\ge0,\quad
 \Delta M=\frac{D-B}2\ge0,\quad\Delta R=-D.}
$$

**证明。**

$P_y=\int_x^y(g+f)/2$ and $M_y=\int_x^y(g-f)/2$ are nonnegative. Adding them and the remaining mass $H(y)$ gives $H(x)$. The same identities on $[y,z]$ prove the update. In particular $|B|\le D$.

$\square$

When $H(x)>0$, division by it puts the state on a simplex. These are three constrained coordinates, of intrinsic dimension two. The channels are formed from the chosen majorant; they are not generally the Jordan positive and negative parts of $f$.

For $R_y>0$ and $D>0$, set $\nu=D/R_y$ and $\xi=(D+B)/(2D)$. Then

$$
\begin{pmatrix}P_z\\M_z\\R_z\end{pmatrix} =
 \begin{pmatrix}
 1&0&\nu\xi\\
 0&1&\nu(1-\xi)\\
 0&0&1-\nu
 \end{pmatrix}
 \begin{pmatrix}P_y\\M_y\\R_y\end{pmatrix}.
$$

Every column sums to one. These triangular nonnegative matrices are closed under composition. Indeed, for third-column entries $(a_i,b_i,r_i)$ with $a_i+b_i+r_i=1$, the product in chronological order has entries $(a_1+a_2r_1,b_1+b_2r_1,r_2r_1)$. This is deterministic budget accounting; no stochastic independence is assumed. Zero masses are handled by the unnormalized identities, without division.

The readout and exact tail are coupled by $J(x)=P_y-M_y+J(y)$, with $|J(y)|\le R_y$. This lift exactly represents the original majorant bound. A stronger one-sided bound requires additional information about the actual source.

## 4　Application to the Robin readout and its residual

Let all logarithms be natural, and for an integer $N>e$ define

$$
X=\log N,\quad r(N)=\frac{\sigma(N)}N,\quad
 S(N)=\gamma+\log\log X-\log r(N).
$$

For real $x>1$, set

$$
\psi(x)=\sum_{p^k\le x}\log p,\quad
 Q(x)=\sum_{p^k\le x}\frac1{kp^k},\quad
 \varepsilon(x)=\frac{\psi(x)-x}{x\log x},
$$

$$
f(t)=(\psi(t)-t)\frac{\log t+1}{t^2\log^2t},\qquad
 J(x)=\int_x^\infty f(t)\,dt.
$$

Partial summation, as detailed in R3 [\[4\]](#ref-r3), gives

$$
J(x)=\gamma+\log\log x+\varepsilon(x)-Q(x).
$$

For completeness, if $F(x)=\log\log x+\varepsilon(x)-Q(x)$, then $F'=-f$ between prime powers. At $q=p^k$, both $\varepsilon$ and $Q$ jump by $1/(kq)$, so $F$ is continuous. The standard Mertens limit $Q(x)-\log\log x\to\gamma$ and $\varepsilon(x)\to0$ fix the constant. Absolute tail convergence follows from the explicit estimate below.

Define the finite readout

$$
G_N(x)=\log\frac{\log X}{\log x}-\log r(N)-\varepsilon(x)+Q(x).
$$

Then the original target is recovered exactly:

$$
\boxed{S(N)=G_N(x)+J(x).}
$$

Changing the cutoff produces paired updates

$$
G_N(y)-G_N(x)=\mathcal B(x,y),\qquad J(y)-J(x)=-\mathcal B(x,y).
$$

The same $\varepsilon-Q$ occurs with opposite signs. Bounding its two occurrences independently can erase an exact cancellation.

Johnston–Yang [\[2\]](#ref-jy) prove, for $t\ge2$,

$$
|\psi(t)-t|\le9.39t(\log t)^{1.515}e^{-0.8274\sqrt{\log t}}.
$$

For $t\ge e$, an integrable majorant for $f$ is therefore

$$
g(t)=9.39\frac{\log t+1}{t}e^{-0.8274\sqrt{\log t}},\qquad
 H(y)=9.39\int_{\log y}^{\infty}(u+1)e^{-0.8274\sqrt u}\,du.
$$

For $e\le x\le y$, the previous section applies without RH. Its lower and upper certificates for the target are

$$
\boxed{
 G_N(x)-H(x)+2P_y\ \le S(N)\le\ G_N(x)+H(x)-2M_y.}
$$

They improve monotonically as $y$ increases. Strict positivity is certified as soon as $2P_y>H(x)-G_N(x)$. This condition is a useful stopping test, not a uniform proof that all relevant $N$ satisfy it.

## 5　A direct arithmetic relation with prime-counting error

Use the CA threshold notation of [\[3\]](#ref-cns):

$$
F(t,k)=\frac{\log(1+1/(t+\cdots+t^k))}{\log t},\quad
 F(x_k,k)=\lambda,\quad z=x_1,
$$

$$
N=N^+(\lambda)=\prod_p p^{\#\{k\ge1:F(p,k)\ge\lambda\}}.
$$

Equality layers are included. The function $F(t,k)$ strictly decreases in $t>1$, and also in $k$ for fixed $t$. Put $X=\log N$.

#### 定理 5.1：Shared-source surplus

Every prime power $p^k\le z$ is selected in $N$. Consequently

$$
D(z):=X-\psi(z)
 =\sum_{k\ge2}\left[\vartheta(x_k)-\vartheta(z^{1/k})\right]\ge0,
$$

and

$$
\boxed{D(z)+(\psi(z)-z)=X-z.}
$$

**证明。**

For $t>1$ and $k\ge2$, write $s=t+\cdots+t^k<kt^k$. Bernoulli’s inequality gives $(1+1/s)^k>1+k/s>1+t^{-k}$, hence $F(t,k)>F(t^k,1)$. If $p^k\le z$, then $F(p,k)\ge F(p^k,1)\ge F(z,1)=\lambda$, with strictness for $k\ge2$. This proves selection. The two identities follow from $X=\sum_{k\ge1}\vartheta(x_k)$ and $\psi(z)=\sum_{k\ge1}\vartheta(z^{1/k})$. Only finitely many summands are nonzero. Finally, add and subtract $X$.

$\square$

#### 推论 5.2：Coupling at an internal slope balance

If, in addition, $X>1$ and $\lambda=1/(X\log X)=F(z,1)$, then

$$
\boxed{0<D(z)+\psi(z)-z<\tfrac12.}
$$

**证明。**

The integral of the strictly convex function $1/t$ over $[z,z+1]$ gives $1/(z+1/2)<\log(1+1/z)<1/z$. Thus

$$
z\log z<X\log X<(z+1/2)\log z<(z+1/2)\log(z+1/2).
$$

Since $t\log t$ increases on $t>1$, $z<X<z+1/2$.

$\square$

The extra slope balance is a hypothesis, not a property of every CA integer. The two errors cannot be varied independently on this arithmetic source. This pointwise relation alone does not bound the signed integral $J(z)$.

**Illustration.** For $N=720720$ at its balanced slope, $z\approx13.13358933261149$. Here $D=\log2$ exactly, and

$$
\psi(z)-z\approx-0.33873052184611,\qquad
 X-z\approx0.35441665871383.
$$

Their sum with $D\approx0.69314718055995$ verifies the displayed coupling. These decimals illustrate the exact formulas; the proof does not rely on them.

## 6　A quantitative cancellation from the shared relation

For the CA state above, assume $X>1$, write $M=X-z$, and let $h(t)=\log\log t$ on $t>1$. Define its concavity remainder by

$$
\mathcal K_z(M)=h(z)+h'(z)M-h(z+M).
$$

Since $h''(t)=-(\log t+1)/(t^2\log^2t)<0$, this remainder is nonnegative whenever $z,z+M>1$.

#### 定理 6.1：Cancellation of the linear displacement

The exact shared-source relation implies

$$
\boxed{
 \log\frac{\log X}{\log z}-\varepsilon(z)
 =\frac{D(z)}{z\log z}-\mathcal K_z(M).
 }
$$

Under the internal slope balance of the previous section,

$$
\boxed{
 0<\mathcal K_z(M)<\frac{\log z+1}{8z^2\log^2z}.
 }
$$

**证明。**

Substitute $\psi(z)-z=M-D(z)$ and $h(z+M)-h(z)=h'(z)M-\mathcal K_z(M)$, with $h'(z)=1/(z\log z)$. The two linear terms in $M$ cancel. For $0<M<1/2$, Taylor’s integral formula gives

$$
\mathcal K_z(M)=\int_0^M(M-t)
 \frac{\log(z+t)+1}{(z+t)^2\log^2(z+t)}\,dt.
$$

The positive integrand factor decreases on $z+t>1$; its logarithmic derivative is $[1/(\log u+1)-2-2/\log u]/u<0$. Bound it by its value at $z$ and use $M^2/2<1/8$.

$\square$

At the critical normalization, this curvature uncertainty is very small:

$$
\sqrt z\log z\,\mathcal K_z(M)
 <\frac{\log z+1}{8z^{3/2}\log z}=O(z^{-3/2}).
$$

This is a quantitative gain from retaining the dependence of two readouts, not a new assumption about their separate errors.

For an exact Robin identity, define the positive prime-power remainder

$$
R_*(z)=\sum_{p\le z}\sum_{\substack{k\ge2\\p^k>z}}\frac1{kp^k}.
$$

The Euler factors give $\log r(N)=Q(z)+R_*(z)-C(N)$, where $C(N)=\sum_{p\mid N}-\log(1-p^{-a_p-1})$. Consequently

$$
\boxed{
 S(N)=J(z)+C(N)-R_*(z)
       +\frac{D(z)}{z\log z}-\mathcal K_z(M).
 }
$$

The endpoint error has been absorbed into a positive arithmetic surplus and a controlled curvature term. The integrated signed discrepancy $J(z)$ remains, so this identity does not prove its required uniform lower bound.

## 7　A second lift: gain, residual, and exponent cost

For primes $p$ and $k\ge2$, let

$$
f_k(p)=-\log(1-p^{-k}),\quad
 w_{p,k}=f_k(p)-f_{k+1}(p)=F(p,k)\log p>0.
$$

Their total is $B_0=\sum_{p,k\ge2}w_{p,k}=\log\zeta(2)$. For any finite $n=\prod p^{a_p}$, define

$$
A(n)=\sum_{p\mid n}\sum_{k=2}^{a_p}w_{p,k},\qquad
 K(n)=\sum_{p\mid n}(a_p-1)\log p
 =\log\frac{n}{\operatorname{rad}n}.
$$

The unselected budget is

$$
E(n)=B_0-A(n)=C(n)+V(n)\ge0,
$$

where $C=\sum_{p\mid n}f_{a_p+1}(p)$ and $V=\sum_{p\nmid n}f_2(p)$ as in R3.

For a slope $\lambda>0$, put

$$
K_\lambda=\sum_{p,k\ge2:\,F(p,k)\ge\lambda}\log p,
 \qquad
 \mathcal G(\lambda)=\sum_{p,k\ge2}(w_{p,k}-\lambda\log p)_+.
$$

Only finitely many atoms are selected: their number is at most $B_0/(\lambda\log2)$. Therefore these expressions are finite.

#### 定理 7.1：Coupled budget and supporting inequality

For the CA integer $N^+(\lambda)$,

$$
\boxed{E(N^+(\lambda))+\lambda K_\lambda+\mathcal G(\lambda)=B_0.}
$$

All three terms are nonnegative, and the old readout is recovered by $A(N^+(\lambda))=\lambda K_\lambda+\mathcal G(\lambda)$. For every finite integer $n$ and every $\lambda>0$,

$$
\boxed{A(n)\le\lambda K(n)+\mathcal G(\lambda),\qquad
 E(n)\ge\max\{0,B_0-\lambda K(n)-\mathcal G(\lambda)\}.}
$$

**证明。**

For a selected atom, split $w=\lambda\log p+(w-\lambda\log p)$. Summation proves the CA equality, including zero surplus at ties. For any other selection, the sum of its signed surpluses is at most the sum of all positive surpluses. This proves the inequality; the residual bound follows from $E=B_0-A\ge0$.

$\square$

The cost $K$ also enters $\log n$ and hence the Robin denominator. This coupling therefore constrains which readout and residual values can coexist at a specified size cost. Taking the infimum of $\lambda K+\mathcal G(\lambda)$ gives a concave upper envelope for attainable gain as a function of cost. Equality for every discrete cost is not asserted. The support is retained in the protocol: from $E=C+V$, recover $C=E-V$ using $V$ determined by that support. Merging $C$ and $V$ without this retained information would not preserve the old readout.

At $N=720720$, $K=\log24$ and the three budget terms are approximately

$$
E=0.1617242206600083,\quad
 \lambda K=0.0905606327758986,\quad
 \mathcal G=0.2454154490348384.
$$

## 8　The relation itself has an integral and jump structure

The preceding slope family has further exact relations:

#### 定理 8.1：Layer-cake identities

For every $\lambda>0$,

$$
\boxed{
 \mathcal G(\lambda)=\int_\lambda^\infty K_t\,dt,
 \qquad B_0=\int_0^\infty K_t\,dt,
 }
$$

$$
\boxed{
 E(N^+(\lambda))=\int_0^\lambda(K_t-K_\lambda)\,dt.
 }
$$

**证明。**

For each atom with threshold $q=F(p,k)$ and cost $c=\log p$, $(w-\lambda c)_+=\int_\lambda^\infty c\,1_{t\le q}\,dt$ and $w=\int_0^\infty c\,1_{t\le q}\,dt$. Tonelli’s theorem applies to the nonnegative summands. Subtract $\mathcal G(\lambda)+\lambda K_\lambda$ from the total integral. Endpoint conventions do not change integrals; they do determine the selected cost $K_\lambda$ and the residual at a tie.

$\square$

The function $\mathcal G$ is convex and continuous on $(0,\infty)$. On each interval without a threshold, $\mathcal G'=-K_\lambda$. Local finiteness of thresholds follows from the atom-count bound on any interval bounded away from zero. At a threshold, a zero-surplus atom can enter or leave without a jump in $\mathcal G$; its mass transfers between $E$ and $\lambda K_\lambda$.

For $0<\lambda_1<\lambda_2$, write $A_i=A(N^+(\lambda_i))$ and $K_i=K_{\lambda_i}$. The atoms present only at $\lambda_1$ have thresholds in $[\lambda_1,\lambda_2)$, so

$$
\boxed{\lambda_1(K_1-K_2)\le A_1-A_2\le\lambda_2(K_1-K_2).}
$$

The upper inequality is strict when the cost difference is positive. This controls readout changes and residual changes by their common cost change. It is stronger structural information than the separate ranges $0\le A\le B_0$ and $0\le E\le B_0$.

### A variational readout with nonnegative residual

Define $U(b)=\inf_{\lambda>0}\{\lambda b+\mathcal G(\lambda)\}$ for $b\ge0$. It is nondecreasing and concave, and $A(n)\le U(K(n))\le B_0$. The last bound follows by taking $\lambda\downarrow0$ and using dominated convergence in $\mathcal G(\lambda)\uparrow B_0$. The optimization residual

$$
\delta(n)=U(K(n))-A(n)\ge0
$$

therefore gives the exact Robin decomposition

$$
\boxed{
 S(n)=\left[\gamma+\log\log(\log n)
 -\log r(\operatorname{rad}n)-U(K(n))\right]+\delta(n).
 }
$$

Here $n>e$. For CA higher-exponent profiles, $U(K_\lambda)=A(N^+(\lambda))$: the universal upper bound gives one direction and the optimizing slope gives the other. Hence $\delta=0$ on these profiles. This variational choice excludes a negative residual but gives no automatic positive slack at the extremal states; the bracket is not proved uniformly positive.

## 9　Arithmetic operations and sufficient recursive state

For exact quantities $X=x+e$, $Y=y+d$, the arithmetic lifts are

$$
X+Y=(x+y)+(e+d),
$$

$$
\boxed{XY=xy+(xd+ye+ed).}
$$

The product residual retains the mixed term $ed$. A first-order approximation may omit it only with a separate certified remainder bound. If $x,y>0$, write $X=x(1+u)$ and $Y=y(1+v)$. Then

$$
\frac{XY}{xy}-1=u+v+uv.
$$

When $1+u,1+v>0$, logarithmic residuals obey

$$
\log\frac{XY}{xy}=\log(1+u)+\log(1+v).
$$

Thus the relation depends on the operation and its domain. Orthogonal projection has a different relation: if $P$ is an orthogonal projection on a real or complex Hilbert space, then $v=Pv+(I-P)v$, $\langle Pv,(I-P)v\rangle=0$, and $\|v\|^2=\|Pv\|^2+\|(I-P)v\|^2$. Orthogonality is a hypothesis, not a consequence of merely naming a pair of quantities.

#### 定理 9.1：Recoverability and update closure

Let $\pi:\Omega\to Q$ encode source states, let $f:\Omega\to Y$ be an old readout, and let $T:\Omega\to\Omega$ be an allowed update. Maps $\bar f$ and $\bar T$ on $\pi(\Omega)$ with

$$
f=\bar f\circ\pi,\qquad \pi\circ T=\bar T\circ\pi
$$

exist if and only if $\pi(\omega)=\pi(\omega')$ implies both

$$
f(\omega)=f(\omega'),\qquad
 \pi(T\omega)=\pi(T\omega').
$$

**证明。**

Necessity follows by substitution. Conversely, define each barred map using any representative of a fiber of $\pi$. The two conditions say exactly that its value does not depend on that representative.

$\square$

For a guarded update on $D\subseteq\Omega$, legality must also be constant on fibers: $\pi(\omega)=\pi(\omega')$ implies $\omega\in D\iff\omega'\in D$. Apply the successor condition on $D$.

This is the precise test for whether a proposed finite lift is sufficient. For the tail-budget matrices, $D$ and $B$ for the next interval are supplied by the retained source and interval protocol. The three mass coordinates alone are not asserted to predict an unspecified future prime interval. Likewise, three exact coordinates do not imply bounded bit complexity, an efficient inverse, or a universal three-dimensional dynamical model.

## AURIC interface and scope of this revision

The current five-role interpretation can be instantiated at each refinement without assigning permanent numerical meanings to the symbols:

| Role | Meaning in the present readout–residual analysis |
|:---|:---|
| $F[\mathrm{null}]$ | Source, reference target, scale, certification protocol, and allowed updates. |
| $F[1]$ | The current readout or the first complementary component. |
| $F[3]$ | Its residual or the second complementary component. |
| $F[1,3]$ | The joint admissible relation, including shared parameters and the coupled update law. |
| $F[2]$ | A completed target readout or certified normalized state, as defined for this layer. |

The formulation is a candidate research interface, not a new assumption about the primes. “Analyze all dual concepts by their relation” is a methodological program. For a theorem, the two domains, common source, relation, normalization, and allowed operations must be specified. Some joint relations are full Cartesian products; a nontrivial constraint must be proved rather than inferred from the word “dual.”

Three obligations remain distinct: recovery of the old target; closure of updates with retained source data; and a contraction or sign certificate. A normalized invariant need not satisfy the last obligation automatically. No global Robin/RH proof, literature novelty, or efficient universal decision procedure is claimed.

The supplied R3 note and visible discussion are the local starting point. The public repository landing page was accessible, but the theory file could not be retrieved at the pinned commit:\
`d3c4ee1ee7f60f48b7dcdbd4967972029e18dfed`.\
This standalone extension makes no repository integration, source-level formal verification, or merge claim.

## 来源与参考

<a id="ref-aa"></a>

\[1\] M. V. A. Andrade, J. L. D. Comba and J. Stolfi,  *Affine Arithmetic* , draft submitted to INTERVAL’94, especially §§2–3. <https://graphics.stanford.edu/~comba/papers/aa-93-12-petersburg-paper.pdf>.

<a id="ref-jy"></a>

\[2\] D. R. Johnston and A. Yang, *Some explicit estimates for the error term in the prime number theorem*, arXiv:2204.01980v2, Theorem 1.1. <https://arxiv.org/pdf/2204.01980>.

<a id="ref-cns"></a>

\[3\] G. Caveney, J.-L. Nicolas and J. Sondow,  *On SA, CA, and GA numbers* , arXiv:1112.6010v2, especially §2. <https://arxiv.org/pdf/1112.6010>.

<a id="ref-r3"></a>

\[4\] AURIC research discussion, *AURIC–Robin R3: Conserved arithmetic mass, normalized refinements, and finite windows*, 6 November 2026. Companion scoped proof note.

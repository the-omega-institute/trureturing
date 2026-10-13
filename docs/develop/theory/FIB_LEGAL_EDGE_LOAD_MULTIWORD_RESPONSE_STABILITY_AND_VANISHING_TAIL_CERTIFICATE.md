# FIB harmonic-edge load: multiword response stability and a vanishing-tail certificate

This volume gives ordinary conditional proofs and one exact four-state illustration. Explicit finite-marginal, actual full-posterior and uniform-tail hypotheses make a block-conditional-null multiword response stable. An independently proved actual-law defect tail also gives a finite certificate with a vanishing tail allowance. The illustration has neither a block reset nor a positive two-word null direction at any length. Its risk is already excluded by a cheaper comparator; its contribution here is the productive response mechanism.

## 1. Complete domain and actual-law interfaces

Retain the full open-path domain and objective of [Stationary, §§1–2][S]:

$$
B_n=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\},\qquad
h(s,v)=\begin{cases}sv/(s+v)&s+v>0,\\0&s=v=0,\end{cases}
$$

$$
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\quad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\quad c_\star=\lim_n\kappa_n/n.
$$

Every legal Hamming-one edge is present, with endpoint insertion convention $w_0=w_{n+1}=0$ and no first-to-last constraint. All-zero words, endpoint ones, every legal seam, structural zeros and zero-mass vertices remain. Put $X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}$, $(Tx)_i=x_{i+1}$ and $\mathcal E_i=\sigma(X_j:j\ne i)$.

For one normalized two-sided stationary law $P$ on $X$, choose $[0,1]$ Borel versions

$$
q_i(P)=\mathbb E_P[X_i\mid\mathcal E_i],\quad \ell_i(P)=(X_i-q_i(P))^2,\quad
q_{r,i}(P)=\mathbb E_P[X_i\mid X_{i-r},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+r}].
$$

The radius-zero field is trivial. [Stationary, equations (2.1)–(2.6)][S] gives

$$
d(P)=\lim_n\Phi_n(P_n)/n=\mathbb E_P\ell_0(P)=\inf_rD_r(P)\le c_\star,
\qquad D_r(P)=\mathbb E_P(X_0-q_{r,0}(P))^2.
\tag{1.1}
$$

All clocks below are the original emitted-bit integer coordinates. Neighbor-one fibers force the center, posterior and loss to zero. Zero-total finite fibers contribute zero and require no division; posterior versions there do not affect an integral.

For every finite $N$, retain [Universal, Definition 4.1][U]'s entire exact-real domain

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,\ M_0,M_1\ge0,
\ A=M_0+M_1,\ A\mathbf1=\mathbf1,\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.2}
$$

Here $\lambda$ is an $N$-dimensional row, $M_0,M_1$ are $N\times N$, and $M_w=M_{w_1}\cdots M_{w_n}$. Structural zeros, zero stationary masses, reducibility, periodicity and noncontractive boundaries are allowed. [Universal, Proposition 4.2][U] supplies one coherent stationary joint law with interval masses $\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1})$ and visible cylinders $P_\theta([w])=\lambda M_w\mathbf1$. Empty word products are identities; seams use ordered joint products. Entrywise $M_1^2=0$ is not required of every unpruned presentation.

Fix $C=[1,L]$, $\mathcal H_C=\sigma(X_j:j\notin C)$, $f_C=f(X_C)$ and $F=\max_{B_L}|f|$. Conditional nullity means $\mathbb E_P[f_C\mid\mathcal H_C]=0$ under this actual $P$. The matrix condition $\sum_{w\in B_L}f(w)M_w=0$ is sufficient by [Conditional Response, §3][R], before attainment. Under same-law attainment only, that supplier's Theorem 3.1 and equation (2.2) give

$$
S_P(f):=\sum_{i\in\mathbb Z}\mathbb E_P[f_C\ell_i(P)]=0,\qquad
0\le D_r(P)-c_\star\le c_\star/(r+1),\qquad c_\star\le\bar c:=3-2\sqrt2<1/4.
\tag{1.3}
$$

The ceiling is unconditional; the zero-response and projection-budget statements require attainment.

## 2. Exterior projection and conditional response stability

For any stationary legal $P$, define its actual one-sided predictors and defects, without an attainment hypothesis:

$$
p^L_r=\mathbb E_P[X_0\mid X_{-r},\ldots,X_{-1},X_1,X_2,\ldots],\quad
p^R_r=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_r],
$$

$$
e_L(r)=\mathbb E_P(q_0-p^L_r)^2,\quad e_R(r)=\mathbb E_P(q_0-p^R_r)^2,\quad
\tau_P(R)=\sum_{r\ge R}(e_L(r)+e_R(r)).
\tag{2.1}
$$

**Lemma 2.1 (Actual exterior projection).** For an actual conditional-null $f_C$, let $p_i$ condition on all coordinates in the exterior half-line containing $i$, except $i$: use $j\le0$ on the left and $j\ge L+1$ on the right. Then

$$
\mathbb E_P[f_C\ell_i(P)]=-\mathbb E_P[f_C(q_i(P)-p_i)^2]\quad(i\notin C).
\tag{2.2}
$$

Consequently the response omitted outside $I_R=[1-R,L+R]$ has absolute sum at most $F\tau_P(R)$. If $\tau_P(R)$ is finite for some $R$, the entire response is absolutely convergent.

Proof. The loss $(X_i-p_i)^2$ is $\mathcal H_C$-measurable, so its product with $f_C$ has expectation zero. Both $f_C$ and $q_i-p_i$ are $\mathcal E_i$-measurable. Expanding the square and conditioning on $\mathcal E_i$ eliminates the cross term. This proves (2.2), which is [Conditional Response, equation (3.5)][R]'s projection identity without its attained-law budget. Stationarity identifies the squared defects at $i=-r,L+1+r$ with $e_R(r),e_L(r)$. The omitted offsets are exactly $r\ge R$; the remaining sites are finite. $\square$

The loss in this lemma always uses $P$'s own posterior. In particular, the actual locally reweighted law $P^{(z)}=(1+zf_C)P$, $|z|F\le1/2$, is normalized by nullity, equivalent to $P$, and has the same $\mathcal H_C$ marginal. Conditional Bayes gives $q_i(P^{(z)})=q_i(P)$ outside $C$. Inside $C$, on a free fiber with legal completion values $f_0,f_1$, it gives

$$
q_i(P^{(z)})-q_i(P)
=\frac{zq_i(P)(1-q_i(P))(f_1-f_0)}{1+z((1-q_i(P))f_0+q_i(P)f_1)}.
\tag{2.3}
$$

Forced fibers remain zero. The denominator is at least $1/2$ on positive fibers; null exceptions are preserved by equivalence. Conditional squared-loss projection therefore gives, whenever Lemma 2.1 ensures absolute convergence,

$$
\sum_i\bigl(\mathbb E_{P^{(z)}}(X_i-q_i(P^{(z)}))^2-d(P)\bigr)
=zS_P(f)-\sum_{i\in C}\mathbb E_{P^{(z)}}(q_i(P^{(z)})-q_i(P))^2.
\tag{2.4}
$$

This is the actual-law reweighting identity of [Conditional Response, equation (3.6)][R]. It follows by projecting under $P^{(z)}$ and then using its density to integrate the fixed loss from $P$. A reweighted law need not be stationary; no stationary risk identity is applied to it.

**Theorem 2.2 (Conditional stability with actual tails).** Let $P_s$, $0\le s\le\epsilon$, be actual stationary legal laws on these same coordinates, with every finite marginal continuous at $s=0$. Let $f_s:B_L\to\mathbb R$ be conditional-null under its own $P_s$, with $\sup_s\|f_s\|_\infty=M<\infty$ and $\|f_s-f_0\|_\infty\to0$. Specify a common $[0,1]$ finite-coordinate Borel function $g_0$ of exterior coordinates and its translates $g_i$, such that $g_i=q_i(P_0)$ $P_0$-almost surely. Assume actual posterior versions satisfy

$$
\sup_{i\in\mathbb Z}\operatorname*{ess\,sup}_{P_s}|q_i(P_s)-g_i|\le\delta_s\longrightarrow0,
\qquad \sup_{0\le s\le\epsilon}\tau_{P_s}(R)\le\eta(R)<\infty,\quad \eta(R)\longrightarrow0.
\tag{2.5}
$$

The tail bound need only hold for all sufficiently large $R$. Then every complete $S_{P_s}(f_s)$ is absolutely convergent, and $S_{P_s}(f_s)\to S_{P_0}(f_0)$. A nonzero reference response remains nonzero for all sufficiently small parameters satisfying these hypotheses.

Proof. Lemma 2.1 bounds each omitted absolute response by $M\eta(R)$, uniformly in $s$. On any fixed $I_R$, replacing the actual loss by $(X_i-g_i)^2$ costs at most $2M\delta_s$ per site; replacing $f_s$ by $f_0$ costs at most $\|f_s-f_0\|_\infty$. The resulting bounded integrand is a fixed finite-coordinate function, whose expectations converge by finite-marginal continuity. Thus each finite partial sum converges. First make the two tails arbitrarily small by choosing $R$, then take $s\to0$ on that finite interval. This proves the full-series limit and absolute convergence. Nonzero persistence follows from an error smaller than half the reference absolute value. $\square$

The common $g_i$ is specified as a function on legal records, rather than transporting a $P_0$-only equivalence class to a possibly singular $P_s$. Finite-marginal continuity alone is insufficient: actual full-posterior control and uniform summable tails are separate hypotheses.

## 3. A finite certificate retaining nearby exterior sites

**Theorem 3.1 (Vanishing-tail finite certificate).** Let $P$ be an actual stationary legal law with a conditional-null $f_C$. Suppose an actual-law bound $\tau_P(R)\le\eta(R)$ is proved independently of attainment. For integers $R,r\ge0$, define

$$
U_{R,r}(P,f)=\sum_{i\in I_R}\mathbb E_P[f_C(X_i-q_{r,i}(P))^2],\qquad I_R=[1-R,L+R].
\tag{3.1}
$$

Same-law attainment implies

$$
|U_{R,r}(P,f)|\le F\eta(R)+2(L+2R)F\sqrt{\frac{c_\star}{r+1}}.
\tag{3.2}
$$

A verified strict inequality

$$
|U_{R,r}(P,f)|>F\eta(R)+2(L+2R)F\sqrt{\frac{\bar c}{r+1}}
\tag{3.3}
$$

certifies $d(P)<c_\star$. If $S_P(f)\ne0$ and $\eta(R)\to0$, some finite $R,r$ give (3.3), without assuming attainment in this detectability statement.

Proof. Under attainment, (1.3) sets the full response to zero. Lemma 2.1 makes its full-posterior partial sum $V_R$ on $I_R$ satisfy $|V_R|\le F\eta(R)$. For each retained site, projection under the same $P$, stationarity, squared-loss Lipschitz continuity and Cauchy–Schwarz give

$$
|U_{R,r}-V_R|\le2(L+2R)F\sqrt{D_r(P)-c_\star}
\le2(L+2R)F\sqrt{c_\star/(r+1)}.
$$

This proves (3.2); monotonicity in the nonnegative ceiling and (1.1) prove the strict certificate. For arbitrary $P$ with nonzero $S$, choose $R$ so $F\eta(R)<|S|/4$. Then $|V_R|>3|S|/4$. For this fixed $R$, increasing-field $L^2(P)$ projection gives $U_{R,r}\to V_R$. Choose finite $r$ making the approximation error and square-root allowance each smaller than $|S|/4$. The left side then exceeds $|S|/2$ and the threshold is smaller than $|S|/2$. $F=0$ cannot give nonzero $S$. $\square$

For $P_\theta$, (3.1) is determined by its actual finite marginal on $[1-R-r,L+R+r]$. On a positive radius-$r$ exterior atom $u,v$, the posterior is $\lambda M_uM_1M_v\mathbf1/(\lambda M_uAM_v\mathbf1)$; zero denominators have zero contribution, forced atoms have zero numerator, and empty words handle $r=0$. All block/window overlaps are retained.

[Two-word, Theorems 2.1 and 3.1][W] cancel exterior terms exactly for a positive conditional-null pair, and remove the constant allowance from the interior-only $T_{L,r}$. Here nearby exterior sites remain in $U_{R,r}$ and the independently proved tail allowance vanishes. This theorem does not remove the interior-only constant for arbitrary multiword directions, nor supply a universal or efficient radius.

## 4. An exact law with no reset and no positive pair

Use an auxiliary parameter $0\le s\le10^{-6}$ for estimates, and certify the single exact candidate $t=10^{-100}$. Set

$$
b=2/3,\quad q=1/3,\quad p=3/10+100s,\quad a=1-p,\quad Z=b+2p,\quad l=(b,p)/Z,
$$

$$
B=\begin{pmatrix}a-ps&ps\\b(1-s)&bs\end{pmatrix},\quad
C_0=\begin{pmatrix}s&1-s\\2s&1-2s\end{pmatrix},\quad D=\operatorname{diag}(p,q),\quad
R=DC_0,\quad K=B+R=\begin{pmatrix}a&p\\b&q\end{pmatrix}.
$$

In order free $1$, free $2$, tail $1$, tail $2$, define

$$
M_0=\begin{pmatrix}B&0\\C_0&0\end{pmatrix},\qquad
M_1=\begin{pmatrix}0&D\\0&0\end{pmatrix},\qquad
\lambda=(b,p,bp,pq)/Z=(l,lD),\quad P_s=P_{\theta_s}.
\tag{4.1}
$$

Rows sum to one because $B\mathbf1=(a,b)^{\mathsf T}$, $D\mathbf1=(p,q)^{\mathsf T}$ and $C_0\mathbf1=\mathbf1$. The four stationary numerators sum to $Z$ since $b+q=1$. Direct multiplication gives $lK=l$, $\lambda M_0=(l,0)$ and $\lambda M_1=(0,lD)$; hence $\lambda A=\lambda$, while $M_1^2=0$. Thus (4.1) belongs to the original $\Theta_4$, using the joint law of §1. At $s=t$, all entries of $B,C_0$ and both diagonal entries of $D$ are positive. Free states communicate, each reaches its tail, and tails reach both free states; $B_{11}>0$ is a self-loop. A positive path for any legal word uses free $1$ for ordinary zeros, its $p$ event edge for a one and $C_{0,11}=t$ for the following zero. Initial zeros, final ones, all-zero words and legal extensions are included.

**Proposition 4.1 (All lengths and actual no reset).** At the exact candidate, every nonempty legal word matrix has rank two, and no legal block makes its visible past and future conditionally independent.

Proof. Put $G=[B;C_0]$, $Q_{\rm mat}=[I,0]$, $U=[I;0]$ and $V=[0,I]$. Then $M_0=GQ_{\rm mat}$, $M_1=UDV$, $Q_{\rm mat}G=B$, $VG=C_0$, $Q_{\rm mat}U=I$, and

$$
\det B=bs(a-p)>0,\quad\det C_0=-s,\quad\det D=pq>0,\quad\det R=-pqs\ne0.
$$

After a zero, completed atoms $0,10$ transfer by $B,R$. A word beginning with zero has form $GTQ_{\rm mat}$ or $GTDV$, where $T$ is a product of these invertible atoms. A longer word beginning with one has prefix $UR$ and the same continuation; the singleton one is $UDV$. Full-rank outside injections/projections and invertible middle factors give rank two at every length. The empty word retains rank four.

To prove a law-level statement, set $m=p(1+q)$ and compute $lB=(b-ms,ms)/Z$. The matrices

$$
E=\begin{pmatrix}l\\lB\end{pmatrix},\qquad O=[\mathbf1,B\mathbf1],\qquad
\det E=\frac{m(b+p)s-bp}{Z^2}<0,\quad\det O=b-a=p-q<0
\tag{4.2}
$$

are invertible: $p<q$, and $(1+q)(b+p)s<b$ on the auxiliary range. For each legal $w$, $M_{0w0}=GT_wQ_{\rm mat}$ with invertible $T_w=Q_{\rm mat}M_wG$. Since $\lambda G=l$, the actual table $H_{ij}=P_t([0^{i+1}w0^{j+1}])$, $i,j\in\{0,1\}$, is $ET_wO$. Its determinant is nonzero. Past/future conditional independence given $w$ would factor this very table into a column times a row, contradicting its determinant. $\square$

**Proposition 4.2 (No positive two-word null direction at any length).** Under this exact actual $P_t$, distinct equal-length positive block words cannot support a conditional-null $\alpha\mathbf1_{[v]}-\beta\mathbf1_{[w]}$ with $\alpha,\beta>0$.

Proof. For any nonzero nonnegative row $x$, the second coordinate of normalized $xB$ is $s(px_1+bx_2)/(ax_1+bx_2)\le s$, whereas the first coordinate of normalized $xR$ is $s(px_1+2qx_2)/(px_1+qx_2)\le2s$. The two image sets are disjoint since $3t<1$. If two atom products are positively proportional, applying a positive row forces their final atoms to coincide. Invertibility cancels this final atom. Repetition leaves identical sequences, or a nonempty positive product proportional to $I$. The latter is impossible because its off-diagonal entries are positive.

Conditional nullity of the proposed pair, tested against exterior zero guards of lengths one and two on both sides, gives $E(\alpha T_v-\beta T_w)O=0$. Equation (4.2) implies $\alpha T_v=\beta T_w$. Parsing $0v0$ and $0w0$ after their first zero into completed $0,10$ atoms is unique. The preceding cancellation argument forces identical sequences, hence $v=w$, a contradiction. This uses actual exterior tests and full support, rather than inferring pair absence from word ranks. $\square$

## 5. The exact six-word cofactor direction

Write $u=\operatorname{tr}B$, $d=\det B$, $r=\operatorname{tr}R$, $e=\det R$, $h=\operatorname{tr}(BR)$. Define three-component columns and alternating coefficients by

$$
\begin{aligned}
v_0&=(u^4-3u^2d+d^2,\ 0,\ -ud(u^2-2d))^{\mathsf T},\\
v_2&=(2uh-dr,\ ud,\ -d(ur+h))^{\mathsf T},\\
v_3&=(r^2-2e,\ ur,\ r(h-ur))^{\mathsf T},\qquad v_4=(e,h,-ue)^{\mathsf T},\\
k_0&=-450\det(v_2,v_3,v_4),\quad k_2=450\det(v_0,v_3,v_4),\\
k_3&=-450\det(v_0,v_2,v_4),\quad k_4=450\det(v_0,v_2,v_3).
\end{aligned}
\tag{5.1}
$$

On the entire $B_6$, put $f_s(000000)=k_0$, $f_s(000100)=f_s(001000)=k_2$, $f_s(001010)=f_s(010100)=k_3$, $f_s(010010)=k_4$, and zero on every other legal six-word. Coefficients zero do not remove words or edges.

**Lemma 5.1 (Exact nullity and coefficient control).** This direction is matrix-null and actual block-conditional-null under $P_s$. At $s=t$, it is nonzero and $F<1$.

Proof. Cayley–Hamilton and its polarization give

$$
B^2=uB-dI,\quad R^2=rR-eI,\quad BR+RB=uR+rB+(h-ur)I,
$$

$$
BRB=hB+dR-drI,\qquad RBR=eB+hR-euI.
$$

Substitution shows that $B^5$, $B^2RB+BRB^2$, $BR^2+R^2B$, $RBR$ have respective coefficient columns $v_0,v_2,v_3,v_4$ in the ordered generators $(B,R,I)$. Alternating-minor expansion gives $k_0v_0+k_2v_2+k_3v_3+k_4v_4=0$, without assuming those generators independent. The six listed word transfers between $G,Q_{\rm mat}$ are respectively $B^5,B^2RB,BRB^2,BR^2,R^2B,RBR$. Thus $\sum_{B_6}f_s(w)M_w=0$ exactly.

For every finite exterior cylinder $H$, the actual joint law gives $\mathbb E_s[\mathbf1_Hf_C]=\lambda L_{\rm ext}(\sum f_s(w)M_w)R_{\rm ext}\mathbf1=0$, with unspecified coordinates summed by $A$. Empty products and all seams are included. Bounded monotone-class extension gives nullity for the full $\mathcal H_C$.

At zero, $(u,r,h,d,e)=(7/10,1/3,1/5,0,0)$, so $(k_0,k_2,k_3,k_4)=(-7/25,2401/10000,0,0)$. On the auxiliary range the five invariant changes are at most $500s$: the induced row-sum norms satisfy $\|B-B(0)\|_\infty,\|R-R(0)\|_\infty\le102s$, and the trace/product and displayed determinant formulas imply this bound. With $|u|,|r|,|d|,|e|<1$, $|h|<2$, each $v$ entry has absolute value at most $10$ and polynomial derivative-sum at most $40$ in these invariants. It changes by at most $20000s$. The six-term determinant formula and three-factor telescoping give

$$
\|f_s-f_0\|_\infty\le10^{11}s,
\qquad 450\cdot6\cdot3\cdot10^2\cdot20000<10^{11}.
\tag{5.2}
$$

At $t=10^{-100}$ this proves nonzero $k_2$ and $F<1$. The determinant formula also bounds all $f_s$ by $450\cdot6\cdot10^3$, so the family is uniformly bounded. $\square$

## 6. Actual posterior continuity and an independent vanishing tail

At zero, $B(0)=\left(\begin{smallmatrix}7/10&0\\2/3&0\end{smallmatrix}\right)$ and $C_0(0)=\left(\begin{smallmatrix}0&1\\0&1\end{smallmatrix}\right)$. After $00$ the hidden row is supported on free $1$, after $10$ on free $2$; their next-one probabilities are $3/10,1/3$, and after one zero is forced. The event mass is $p/Z=9/38$; stationarity and no11 give pair masses $(10/19,9/38,9/38)$. Hence $P_0$ is precisely [TwoStep, Definition 2.1 and Proposition 2.2][T]'s law $Q$.

Specify on all legal exterior records the local Borel function $g_i=0$ on forced fibers and, on free fibers, $g_i=A_0,B_0,D_0$ according as $X_{i-2}+X_{i+2}=0,1,2$, where

$$
A_0=200/543,\qquad B_0=100/247,\qquad D_0=50/113.
\tag{6.1}
$$

[TwoStep, Proposition 2.4][T]'s full-word odds $200/343,100/147,100/147,50/63$ survive every farther exterior completion. Increasing-field projection identifies $g_i=q_i(Q)$, with no transported reference-only null exceptions.

**Lemma 6.1 (Uniform actual posterior restriction).** For $0<s\le10^{-6}$ and every finite radius $j\ge5$,

$$
|q_{j,i}(P_s)-g_i|\le\delta_s:=20000s\quad P_s\text{-almost surely},\qquad
|q_i(P_s)-g_i|\le\delta_s\quad P_s\text{-almost surely}.
\tag{6.2}
$$

Proof. For $T=B,R$ and nonzero nonnegative column $z$, $(Tz)_1/(Tz)_2\in[2/5,6/5]$. Indeed this ratio lies between the two column row-ratios, which for $B$ are $(a-ps)/(b(1-s)),p/b$, and for $R$ are $p/(2q),p(1-s)/(q(1-2s))$. All lie in that interval. The normalized row estimates in Proposition 4.2 put rows after $B,R$ within $4s$ in $L^1$ of the respective coordinate rows.

On a free-center finite exterior let $x,y$ be its distance-two bits. Factoring $x0$ and $0y$ gives center-zero and center-one masses $l_xB^2z_y$ and $l_xRz_y$. The row $l_x$ ends in $B$ if $x=0$, in $R$ if $x=1$. For $y=0$, $z_y=B\beta$; for $y=1$, retain the forced following zero and obtain $z_y=R\beta$. At radius five the remaining right stretch already contains a completed atom, so $\beta_1/\beta_2\in[2/5,6/5]$. Normalize $l_x$ to sum one.

Scale $z_y$ by $\beta_1$ for $y=0$ and by $\beta_2$ for $y=1$. For $y=0$ its errors from $(7/10,2/3)^{\mathsf T}$ are $-100s+ps(\beta_2/\beta_1-1)$ and $bs(\beta_2/\beta_1-1)$. For $y=1$ its errors from $(3/10,1/3)^{\mathsf T}$ are $100s+ps(\beta_1/\beta_2-1)$ and $2qs(\beta_1/\beta_2-1)$. The ratio bounds give coordinatewise relative errors at most $500s$, hence absolute errors at most $500s$.

Also $\|B^2-B(0)^2\|_\infty\le204s$. All scaled columns and transfer row-sum norms are at most one. The row, matrix and column changes bound the one-mass error by $(4+102+500)s=606s$ and the zero-mass error by $(4+204+500)s=708s$. In context order $00,01,10,11$, the reference totals are $543/1000,247/1000,247/450,113/450$, all greater than $1/5$. Subtracting at most $1314s$ leaves actual totals above $1/10$. For two masses $v,u$, the quotient identity bounds posterior error by the larger mass error divided by the actual total, hence by $7080s<20000s$. The reference quotients are exactly (6.1).

Every bound holds for arbitrary nonnegative farther factors on positive atoms. Forced fibers have both posteriors zero; zero-total atoms need no quotient. Increasing-field projection under $P_s$ itself gives the full-posterior bound. A countable intersection supplies simultaneous versions at all sites and finite radii. $\square$

At the exact candidate, $A_0>1/3$, $D_0<9/20$ and $\delta_t<1/1000$ put every actual free full posterior inside $[1/4,1/2]$. Every finite posterior containing the neighbors is its conditional average on that free atom. Thus the infinite and finite defects of [Universal, Theorem 2.2][U] vanish here; the band is only a necessary condition for attainment.

**Lemma 6.2 (Candidate-owned actual tail).** Without assuming attainment, for $0<s\le10^{-6}$,

$$
e_{L,s}(r),e_{R,s}(r)\le9^{-\lfloor(r-4)/2\rfloor}\quad(r\ge4),\qquad
\tau_{P_s}(R)\le\eta(R):=\frac92\,9^{-\lfloor(R-4)/2\rfloor}\quad(R\ge4).
\tag{6.3}
$$

At zero the defects vanish for $r\ge2$. In particular $\eta(104)<5\cdot10^{-40}$, and the family satisfies the uniform vanishing-tail hypothesis of Theorem 2.2.

Proof. For a positive $T=\left(\begin{smallmatrix}\alpha&\beta\\\gamma&\zeta\end{smallmatrix}\right)$ the logarithmic ratio map has derivative bounded by

$$
\left|\frac{d}{dz}\log\frac{\alpha e^z+\beta}{\gamma e^z+\zeta}\right|
\le\frac{|\sqrt{\alpha\zeta}-\sqrt{\beta\gamma}|}{\sqrt{\alpha\zeta}+\sqrt{\beta\gamma}}.
\tag{6.4}
$$

Divide the derivative denominator by $e^z$ and apply AM–GM to $\alpha\gamma e^z+\beta\zeta e^{-z}$. The image width is $|\log(\alpha\zeta/(\beta\gamma))|$. For $B$ the cross ratio is $(a-ps)/(p(1-s))$; for $R$ it is $(1-2s)/(2(1-s))$. Each cross ratio and its reciprocal are at most three. Therefore each atom has Hilbert image diameter at most $\log3$ and contraction at most $(\sqrt3-1)/(\sqrt3+1)<1/3$. Transposition proves the same for row messages, including arbitrary nonnegative inputs after their first positive atom.

A known legal exterior stretch of $r$ bits retains the center-adjacent zero, reserves at most one further boundary bit for an unmatched event or initial alignment, and contains at least $k=\lfloor(r-2)/2\rfloor$ completed $0,10$ atoms. Changing the omitted boundary message changes its propagated log ratio by at most $\log3\,3^{-(k-1)}$. Both free center completions use that same free-state message; their odds are a ratio of two nonnegative linear forms. If componentwise $mz\le z'\le Mz$, this odds ratio changes by a factor in $[m/M,M/m]$, so its log change is at most the Hilbert distance. Logistic has derivative at most $1/4$.

For fixed retained exterior data, all farther completions consequently have posterior range at most $(\log3/4)3^{-(k-1)}$. The one-sided conditional posterior is the conditional average of the full posterior on these data. First applying the estimate to finite farther completions and then taking conditional-projection limits for the infinite retained side and the full exterior bounds $|q_0-p^{L,R}_r|$ by that range almost surely. Squaring and using $\log3<4$ gives the first inequality in (6.3); forced centers contribute zero. This argument uses actual transfers and conditional fields, without a chain-mixing or attained-law budget.

Each exponent occurs twice on each side. Summing the geometric series from $R$ therefore gives the second bound, possibly overcounting one term when $R$ is odd. At $R=104$, it is $(9/2)9^{-50}<5\cdot10^{-40}$ because $9^5>10^4$. At zero the reference local posterior gives the stated zero defects. $\square$

## 7. Reference sign, complete positive response and a finite violation

**Lemma 7.1 (Reference sign with all endpoints).** The exact complete reference response satisfies $S_Q(f_0)>1/1200$.

Proof. Put $a_0=7/10$, $h_0=1/5$. The reference identities $B(0)^2=a_0B(0)$ and $B(0)R(0)B(0)=h_0B(0)$ express $f_0$ as the sum of two pair directions: each has coefficient $-a_0h_0$ at $000000$ and $a_0^4$ at $001000$ or $000100$. Each is matrix-null and balances positive mass

$$
J=a_0h_0Q([000000])=a_0^4Q([001000])=(10/19)a_0^5h_0=16807/950000>1/60.
$$

[Two-word, Theorem 2.1][W] identifies each pair's common full exterior law and its actual posterior restrictions, so every exterior response cancels, including both seams. This application is at the reference law only.

For the $000000/001000$ pair, the common left pair $(X_{-1},X_0)$ has probabilities $(49,30,21)/100$ at $00,01,10$: divide the stationary four-word products $0000,0100,1000$ by the initial $00$ mass. Given final $00$, $X_7$ has probabilities $7/10,3/10$. Using (6.1), the six zero-word-minus-one-word conditional loss differences, in coordinate order, are

$$
\begin{gathered}
\tfrac{49}{100}(A_0^2-B_0^2)+\tfrac{21}{100}(B_0^2-D_0^2),\qquad
\tfrac7{10}A_0^2+\tfrac3{10}B_0^2,\qquad 2A_0-1,\qquad A_0^2,\\
\tfrac7{10}(A_0^2-B_0^2)+\tfrac3{10}(B_0^2-D_0^2),\qquad0.
\end{gathered}
$$

At coordinates two and four the inserted one forces the second word's loss to zero; at three the difference is $A_0^2-(1-A_0)^2$. The endpoints use the common actual exterior, and at six both local loss functions coincide. The sum is

$$
H=2A_0-1+\tfrac{289}{100}A_0^2-\tfrac{38}{100}B_0^2-\tfrac{51}{100}D_0^2
<-\frac{3015243}{10^8}<-1/40.
\tag{7.1}
$$

Indeed $A_0<369/1000$, $B_0>404/1000$, $D_0>442/1000$ give numerator $-26200000+39350529-6202208-9963564$. The reference pair chain is reflection invariant: reversing states exchanges $01,10$, their stationary masses agree, and its only nontrivial reversed flux equality is $(10/19)(3/10)=(9/38)(2/3)$. Multiplication of these flux identities reverses every cylinder. Its posterior table is also reflection symmetric. Thus the reflected $000100$ pair has the same $H$, and $S_Q(f_0)=-2JH>1/1200$. $\square$

For finite marginals, write $v_s=(b,p,bp,pq)$. Then $\|v_s-v_0\|_1=200s$, $Z_s-Z_0=200s$ and $Z_s\ge1$, so adding and subtracting $v_0/Z_s$ gives $\|\lambda_s-\lambda_0\|_1\le400s$. The stochastic marked kernel $M_x(i,j)$ has row $L^1$ changes $(200+2p)s,2bs,2s,4s$, all at most $300s$. Telescoping $n$ stochastic kernels and marginalizing hidden paths gives

$$
\|(P_s)_n-Q_n\|_1\le(400+300n)s.
\tag{7.2}
$$

This additive estimate includes new paths absent at zero and the changing stationary row. Together with (5.2), (6.2), (6.3), it verifies all hypotheses of Theorem 2.2.

**Theorem 7.2 (Exact productive response and finite certificate).** At $t=10^{-100}$, the complete actual response has absolute sum less than $11$ and $S_{P_t}(f_t)>1/2000$. It also strictly violates Theorem 3.1's finite necessary bound at $R=104$, $r=10^{12}$.

Proof. For the ten sites $i=-1,\ldots,8$, the comparison integrand $f_0(X_C)(X_i-g_i)^2$ depends on fourteen coordinates $[-3,10]$ and has absolute value at most one. Equation (7.2) changes its expectation by at most $4600t$; coefficient replacement costs at most $10^{11}t$, and replacing $g_i$ by the actual posterior costs at most $2\delta_t$ since $F<1$. Each actual response differs from its reference by less than $2\cdot10^{11}t$, so all ten cost less than $2\cdot10^{12}t$. These include six interior and four near exterior/seam sites.

For $i=-r,7+r$ with $2\le r\le103$, $(X_i-g_i)^2$ is $\mathcal H_C$-measurable. The same conditional-null square expansion as Lemma 2.1, now with the exterior-measurable comparison $g_i$, gives $\mathbb E_t[f_C\ell_i]=-\mathbb E_t[f_C(q_i-g_i)^2]$, of magnitude at most $\delta_t^2$. There are exactly $204$ such sites. For $r\ge104$, Lemmas 2.1 and 6.2 bound both exterior tails by $5\cdot10^{-40}$. Reference exterior terms are zero. Hence

$$
|S_{P_t}(f_t)-S_Q(f_0)|<2\cdot10^{12}t+204(20000t)^2+5\cdot10^{-40}<1/10000.
\tag{7.3}
$$

This gives $S_{P_t}(f_t)>1/1200-1/10000>1/2000$. The same partition bounds its entire absolute sum by $10+204\delta_t^2+5\cdot10^{-40}<11$. No exterior cancellation at positive $t$ has been assumed.

For the finite certificate, $I_{104}=[-103,110]$ has $214$ sites. For every $r\ge5$, Lemma 6.1 applies also to the finite posteriors: the ten near terms have the same reference error bound $2\cdot10^{12}t$. On the other $204$ retained sites the comparison loss has expectation zero against $f_t$, and replacing $g_i$ by $q_{r,i}$ costs at most $2\delta_t$ per site. Therefore

$$
U_{104,r}(P_t,f_t)>1/1200-2\cdot10^{12}t-408\delta_t>1/2000\quad(r\ge5).
$$

At $r=10^{12}$, the threshold with $\bar c<1/4$ and $F<1$ is smaller than $5\cdot10^{-40}+214/10^6<1/4000$. This proves a strict finite violation using exact inequalities; no large-window evaluation or efficiency claim is involved. [Conditional Response, Theorem 3.1][R] also directly forbids this nonzero complete response under same-law attainment. $\square$

## 8. Cheaper risk exclusion and attribution

Write $W=d(Q)=D_2(Q)=\frac1{38}(1372/543+588/247+63/113)$ from [TwoStep, Theorem 3.1][T] and its full-word localization. Both partial derivatives of $h$ lie in $[0,1]$ off the origin; continuity extends its coordinate Lipschitz bound to all nonnegative masses. The free radius-two fibers are disjoint pairs of five-word masses. Equation (7.2) therefore gives $|D_2(P_t)-W|\le1900t$.

Reuse [Two-word, §5, equation (5.6)][W]'s actual comparator $\widehat Q$: its pair transition rows are $(7/10,3/10,0)$, $(0,0,1)$, $(33/50,17/50,0)$ and stationary row $(11/21,5/21,5/21)$. That source verifies its full-posterior localization and actual risk, including forced and zero fibers. Thus

$$
d(\widehat Q)=\frac1{21000}\left(\frac{8217594}{5951}+\frac{3628548}{2739}+\frac{400554}{1271}\right)>\frac{15103}{105000},\qquad d(\widehat Q)\le c_\star.
$$

The positive cross-products $353,79,89$ bound the three summands of $38W$ by $252671/10^5,238057/10^5,55753/10^5$, respectively. Consequently $W<546481/3800000<14382/100000$, since $38\cdot14382-546481=35$. At the single exact candidate $1900t<1/100000$, so

$$
d(P_t)\le D_2(P_t)\le W+1900t<\frac{14383}{100000}<\frac{15103}{105000}<d(\widehat Q)\le c_\star.
\tag{8.1}
$$

The middle strict gap has numerator $85000$ over $10500000000$. This cheaper exclusion does not identify $D_2(P_t)$ with actual $d(P_t)$. The auxiliary interval supplies additive continuity and transfer estimates; no whole-interval risk exclusion or relative-to-zero mass bound is asserted here.

The contribution is a `repo-derived` synthesis relative to these suppliers: independently summable actual exterior defects extend the response route beyond every positive pair on this law and produce the expanded finite certificate. [Stationary][S] owns the actual risk identity; [Universal][U] owns the complete producer domain, posterior-defect interface and compact separation criterion; [Conditional Response][R] owns the attained-law zero response and projection budget. [TwoStep][T] owns the reference law and ratios. [Two-word][W] owns exact pair cancellation and the stronger comparator. [Renewal, §8][P7] retains its separate reset and effective-three-state exclusions.

Conditional Brier scoring and squared posterior discrepancy are mature tools in [Dawid–Lauritzen–Parry][DLP], §4.2, especially Example 4.4 and equation (14). Its everywhere-positive full-product strict-propriety argument is not transplanted to hard no11. Hilbert contraction and the positive-matrix cross-ratio diameter are mature tools in [Lemmens–Nussbaum][LN], §2.1, Theorem 2.9; Lemma 6.2 proves the needed two-dimensional specialization directly. Conditional projection, Cayley–Hamilton, alternating minors and uniformly summable-series continuity are established mathematics. This bounded comparison supports scoped application attribution, without worldwide priority or exhaustive absence claims.

## 9. Unchanged arbitrary-finite target

**Open Problem 9.1 (Productive attained-law gap).** With $C_N=\sup_{\theta\in\Theta_N}d(P_\theta)$ and $U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta)$, still decide whether some exact finite $\theta$ attains $c_\star$, or whether $C_N<c_\star$ for every finite $N$. By [Universal, Theorem 6.2][U], the latter remains equivalent to

$$
\forall N\ge1\ \exists r,m\ge1:\qquad U_{N,r}<\kappa_m/(m+1).
$$

This one law and its two pointwise certificates do not bound a full compact-domain maximum. The next response-route obligation is to construct a productive actual conditional-null direction, or another strict finite certificate, for every remaining hypothetical finite attainer, with justified exterior control. Contraction and matrix null-space dimension alone supply no productive sign. Positive pair availability, uniform contraction, universal block length and a tail envelope on arbitrary noncontractive boundaries remain unproved. All original zero, reducible and periodic cases remain in $\Theta_N$.

There is no hidden-minimality, observer/producer resource equality, effective-radius, empirical machine-learning benefit, exact optimum or kernel-verification claim. The exact illustration's productive response is distinct information from its already cheaper risk exclusion; the original arbitrary-finite problem remains open.

[S]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[R]: FIB_LEGAL_EDGE_LOAD_CONDITIONAL_NULL_RESPONSE_AND_FINITE_CERTIFICATE.md
[T]: FIB_LEGAL_EDGE_LOAD_TWO_STEP_BULK_SEPARATION.md
[W]: FIB_LEGAL_EDGE_LOAD_TWO_WORD_EXTERIOR_CANCELLATION_AND_VANISHING_CERTIFICATE.md
[P7]: FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md
[DLP]: https://arxiv.org/html/1104.2224v2
[LN]: https://arxiv.org/html/1304.7921v1

## 追加锚（本行以下为增补区）

# Arithmetic holographic RT IV

## 104. A finite rational obstruction for equal-polar supported records

### 104.1. Original domain and the equal-polar hypothesis

Retain the four original two-coordinate fibres and the calibrated Gram domain
\[
\mathcal E=\{G\in\operatorname{Herm}(8):G\succeq0,\ G_{ff}=I_2\}.
\]
The local channels have dimensions \(\mathbb C^8\to\mathbb C^4\), the correlated encoding is fixed, and the error has the original unhalved diamond normalization with arbitrary reference. With \(T_{ff}=I_2\) and \(T_{fg}=J_2/2\) for distinct fibres, [RT III §91](ARITHMETIC_HOLOGRAPHIC_RT_III.md) gives the calibrated equality
\[
F(G,H)=\max_{\rho,W}2\operatorname{Tr}[(T-G\odot H)W],
\qquad \rho\succeq0,\quad \rho\text{ fibre-block diagonal},\quad
\operatorname{Tr}\rho=1,\quad0\preceq W\preceq\rho.
\tag{104.1}
\]
Assume throughout the original-domain parts of this section that \((G,H)\) is a local minimum on the full domain \(\mathcal E^2\), that
\[
\operatorname{rank}G=7,\qquad \operatorname{rank}H=6,
\qquad0<t=F(G,H)<\tfrac14,
\tag{104.2}
\]
and that the support \(S\) of the full kernel vector of \(G\) has occupancy \((2,1,1,0)\). Write its whole original fibre as \(F=\{1,2\}\) and its singleton coordinates as \(J=\{3,4\}\). Their actual original partners remain outside \(S\).

The additional equal-polar hypothesis is that reciprocal diagonal phase changes of \(G,H\) and a record-space basis choice put the supported \(H\) records in the form
\[
h_1=e_1,\quad h_2=e_2,\quad
h_3=(c,su),\quad h_4=(c,s\overline u),\qquad
c,s>0,\quad c^2+s^2=1,\quad |u|=1.
\tag{104.3}
\]
This is a substantive restriction on the two singleton records. It is not a reduction of arbitrary supported Grams by a real gauge. Zero values of either polar coordinate would make an original cross-fibre product entry zero and force the matrix-unit error to be at least \(1/2\); thus the positive convention loses no subquarter endpoint. No symmetry is imposed on outside records.

**Theorem 104.1.** There is no local minimum satisfying (104.2)–(104.3) and the stated support condition.

The proof keeps the same original common normer throughout. RT III §§95–97 supply the supported quotient, the equality of principal and full complete norms, unrestricted principal one-party best responses, and the rank-one-quotient exclusion. In this occupancy their consequences are
\[
\operatorname{rank}H_S=\operatorname{rank}\mathsf R=2,
\quad G_S=H_S\odot\overline{\mathsf R},
\quad \mathsf R\succeq0,\quad \mathsf R_{ii}=1,
\quad \mathsf R\operatorname{diag}(\overline a)H_S=0.
\tag{104.4}
\]
Here \(a\) spans the full kernel of \(G\). Section 99 supplies uniqueness of all principal normers, including singular competitors, positive definiteness of the common principal density, and invertibility of the coefficient and witness cross blocks. Sections 101–102 exclude the real-gauge and both-unbiased endpoints. These results concern the full calibrated domain; they do not assert joint local minimality on a principal or fixed-rank domain.

### 104.2. Interior complete-norm reconstruction

First consider a coefficient on the principal original density domain \(F\cup J\) that is fixed by conjugation followed by interchange of 3 and 4. Suppose its \(F\) block and both original singleton diagonal entries vanish. The latter condition is separate: the antiunitary alone only equates those two entries. Put
\[
U_J=\frac1{\sqrt2}\begin{pmatrix}1&i\\1&-i\end{pmatrix},
\qquad U=\operatorname{diag}(I_2,U_J).
\]
In these real coordinates write
\[
L=\begin{pmatrix}0&E\\E^T&J_0\end{pmatrix},
\quad E\in M_2(\mathbb R)\text{ invertible},
\quad J_0=J_0^T,\quad\operatorname{Tr}J_0=0.
\tag{104.5}
\]
Averaging primal and dual variables under the antiunitary retains their feasibility and objective. Thus the fixed primal density and reduced dual may be written
\[
\begin{aligned}
\rho&=\operatorname{diag}(P,\pi I_2),\quad P\succeq0,\quad\pi\ge0,
\quad\operatorname{Tr}P+2\pi=1,\\
\kappa(L)&=\min\{t:Z\succeq0,\ Z-2L\succeq0,
\ Z_{FF}\preceq tI_2,\ \operatorname{Tr}Z_{JJ}\le2t,\ Z=Z^T\}.
\end{aligned}
\tag{104.6}
\]
The trace inequality is precisely the pair of original singleton inequalities after averaging. The density domain has not been enlarged by treating \(J\) as a whole fibre. Strict primal and dual feasibility give attained equal optima by finite-dimensional semidefinite duality. The general complete-norm SDP framework is standard; see J. Watrous, [Semidefinite Programs for Completely Bounded Norms](https://theoryofcomputing.org/articles/v005a011/), Theory of Computing 5 (2009), 217–238. The explicit two-singleton reconstruction below follows from the displayed complementary equations.

Put \(M_E=E^TE\), \(s_E=\operatorname{Tr}M_E\). Let \(Y_0\) be the unique symmetric solution of
\[
M_EY_0+Y_0M_E=J_0,\qquad
\gamma=\operatorname{Tr}(Y_0M_EY_0)\ge0.
\tag{104.7}
\]
In a basis diagonalizing \(M_E\), each entry of \(Y_0\) is the corresponding entry of \(J_0\) divided by the positive sum of the two eigenvalues.

**Lemma 104.2.** There is an optimal fixed density with \(P\succ0\) and \(\pi>0\) exactly when
\[
\gamma<2,\qquad t_0=\sqrt{\frac{s_E}{2-\gamma}}>0,
\qquad\|t_0Y_0\|_{\mathrm{op}}<1.
\tag{104.8}
\]
Then \(\kappa(L)=t_0\), and every such fixed normer has
\[
\pi=\frac1{2(2-\gamma)},\quad
P=\frac\pi{t_0^2}E(I-t_0^2Y_0^2)E^T,\quad
W_{FJ}=\frac\pi{2t_0}E(I-t_0^2Y_0^2),\quad
W_{JJ}=\frac\pi2(I+t_0Y_0).
\tag{104.9}
\]

**Proof.** For necessity take an optimal real dual. Complementarity with the positive density gives \(Z_{FF}=tI_2\) and \(\operatorname{Tr}Z_{JJ}=2t\). Invertibility of \(E\) gives inertia \((2,2)\) for \(L\), so the fixed-density optimal split and its complement have rank two. They are obtained from the positive and negative spectral projectors of \(\rho^{1/2}L\rho^{1/2}\). Thus
\[
(Z-2L)W=0,\qquad Z(\rho-W)=0.
\tag{104.10}
\]
Both dual matrices have the positive definite \(F\) block \(tI_2\), and both have rank two. Write
\[
N=Z-L=\begin{pmatrix}tI_2&B_1\\B_1^T&D_1\end{pmatrix}.
\]
Their zero Schur complements give
\[
B_1^TE+E^TB_1=tJ_0,\qquad
D_1=(B_1^TB_1+M_E)/t,\qquad
2t^2=\|B_1\|_F^2+s_E.
\tag{104.11}
\]
From (104.10), direct expansion yields \(N\rho N=L\rho L\). Its \(FF\) and \(FJ\) blocks imply
\[
t^2P=\pi(EE^T-B_1B_1^T),\qquad
EE^TB_1+B_1M_E=tEJ_0.
\tag{104.12}
\]
Multiply the second equation by \(E^{-1}\) and compare with the first equation in (104.11). Then \(Y=E^{-1}B_1\) is symmetric and satisfies \(M_EY+YM_E=tJ_0\), so \(Y=tY_0\). Positivity of \(P\) gives \(I-Y^2\succ0\). Taking traces proves (104.8), the density normalization in (104.9), and the formula for \(P\). The \(FF\) diagonal block of dual complementarity gives \(E W_{JF}=tP/2\), proving the cross formula. The rank-two graph equations in (104.10) then give \(W_{JJ}=\pi(I+Y)/2\). No full identity \(LW=t\rho/2\) is asserted.

Conversely assume (104.8), set \(t=t_0\), \(Y=tY_0\), and define
\[
N=\begin{pmatrix}tI_2&EY\\YE^T&(YM_EY+M_E)/t\end{pmatrix},
\qquad Z=N+L.
\]
Both \(N+L\) and \(N-L\) have zero Schur complement and are PSD of rank two. Their diagonal bounds satisfy (104.6). Define
\[
\begin{aligned}
W&=\begin{pmatrix}E(I-Y)/t\\I_2\end{pmatrix}
\frac\pi2(I+Y)
\begin{pmatrix}(I-Y)E^T/t&I_2\end{pmatrix},\\
V&=\begin{pmatrix}-E(I+Y)/t\\I_2\end{pmatrix}
\frac\pi2(I-Y)
\begin{pmatrix}-(I+Y)E^T/t&I_2\end{pmatrix}.
\end{aligned}
\tag{104.13}
\]
These matrices are PSD, have rank two, and sum to the density in (104.9), whose trace is one. They satisfy \((Z-2L)W=ZV=0\). Consequently \(2\operatorname{Tr}(LW)=\operatorname{Tr}(Z\rho)=t\). This proves the criterion with the original unhalved normalization. \(\square\)

### 104.3. Prescribed shapes of the same common normer

In (104.5) fix an invertible real \(C_1\), a nonzero symmetric traceless \(Q_0\), and \(j>0\). Suppose
\[
S=E^{-1}C_1=s_0I+kQ_0\succ0,\qquad
w_0^2=\tfrac12\operatorname{Tr}Q_0^2>0.
\tag{104.14}
\]
The coefficients are \(s_0=\operatorname{Tr}S/2\) and \(k=\operatorname{Tr}(SQ_0)/(2w_0^2)\), so \(s_0>|k|w_0\).

**Lemma 104.3.** A positive-density optimal fixed pair and a scale \(\alpha>0\) have
\[
W_{FJ}=\alpha C_1,\qquad
W_{JJ}-\tfrac12\operatorname{Tr}(W_{JJ})I=\alpha Q_0,
\qquad\pi=\alpha j/t
\tag{104.15}
\]
if and only if, with \(Y_0=-kI/2+2Q_0/j\),
\[
M_EY_0+Y_0M_E=J_0,\qquad
j^2=s_E(js_0+4w_0^2).
\tag{104.16}
\]
Its positive norm is fixed by
\[
t^{-2}=2s_0/j+k^2/4+4w_0^2/j^2.
\tag{104.17}
\]

**Proof.** Formula (104.9) and (104.15) give the traceless part \(2Q_0/j\) of \(Y_0\). Cayley–Hamilton in dimension two gives \((Y_0^2)_{\rm tl}=(\operatorname{Tr}Y_0)(Y_0)_{\rm tl}\); the cross formula then gives \(k=-\operatorname{Tr}Y_0\). Its scalar part proves (104.17). Tracing the Sylvester equation and using \(\operatorname{Tr}J_0=0\) gives
\[
\operatorname{Tr}(M_EQ_0)=jks_E/4,\qquad
\gamma=s_E(4w_0^2/j^2-k^2/4).
\tag{104.18}
\]
Combining (104.17) with \(t^2=s_E/(2-\gamma)\) gives the second equation of (104.16).

Conversely define \(t>0\) by (104.17). Under (104.16), equations (104.18) give \(t^2=s_E/(2-\gamma)\). Moreover
\[
t^{-2}-\|Y_0\|_{\mathrm{op}}^2
=\frac{2(s_0-|k|w_0)}j>0,
\qquad\|Y_0\|_{\mathrm{op}}=|k|/2+2w_0/j.
\]
Lemma 104.2 applies. Set \(\alpha=\pi t/j\). The scalar and traceless parts of
\(j(I-t^2Y_0^2)/(2t^2)=s_0I+kQ_0\) give (104.15). The proof never divides by \(k\); it includes \(k=0\) and repeated eigenvalues of \(M_E\). This is a coefficient-level criterion, with no assertion that arbitrary coefficient data have physical Gram realizations. \(\square\)

### 104.4. Actual quotient, phase equation and complete scalar residual

Return to (104.2)–(104.3). The same-normer argument in RT III §103.2 fixes the same principal norming pair \(\rho,W\) under conjugation followed by interchange of 3 and 4. It uses the unrestricted one-party best response and uniqueness of all principal normers; it does not assume a rank-preserving average. After choosing the kernel phase and a positive rescaling,
\[
a_S=(c,sm,z,\overline z),\qquad m\in\mathbb R\setminus\{0\},
\quad z\ne0,\qquad
W_{ij}=-\frac{\alpha a_i\overline{a_j}}{2\overline{H_{ij}}},\quad\alpha>0
\tag{104.19}
\]
across different original fibres. Put \(A=c^2\), \(B=s^2\), \(d=A-B\), \(u=p+iq\), and \(h=A+B\overline u^2\). The delivered endpoint exclusions give \(dpq\ne0\). The original matrix-unit tests and \(|\mathsf R_{ij}|\le1\) give \(A,B>1/4\).

For unit quotient records \(b_i\) with \(\mathsf R_{ij}=\langle b_i,b_j\rangle\), linear in the second argument, the weighted full-kernel relation is
\[
\begin{aligned}
b_1+\overline z b_3+z b_4&=0,&
mb_2+\overline u\,\overline z b_3+uzb_4&=0,\\
b_3&=\frac{-ub_1+mb_2}{2iq\overline z},&
b_4&=\frac{\overline u b_1-mb_2}{2iqz}.
\end{aligned}
\tag{104.20}
\]
Their equal unit norms imply that \(r=\mathsf R_{12}\) is real. If \(|r|=1\), the last two formulas make all four records collinear, contradicting \(\operatorname{rank}\mathsf R=2\). Thus \(-1<r<1\). The same formulas show that the actual \(\mathsf R,G_S,L_S\) have the antiunitary symmetry. The original diagonal coefficients vanish since \(L_{ii}=1-1\), so (104.5) applies with the positive density and invertible cross blocks supplied by §99.

Set
\[
\begin{aligned}
v&=-\Re z,&w&=-\Re(z\overline u),&z&=-v+i(pv-w)/q,\\
v&=mg+2Bmp-Br,&w&=g+2Ap-Amr,\\
\eta&=v-A,&\zeta&=w/m-B,&
M_0&=\begin{pmatrix}\eta&g\\g&\zeta\end{pmatrix}\succ0.
\end{aligned}
\tag{104.21}
\]
These are the actual cross-stress identities of §103.4. Its same-witness commutator and the quotient unit norms give
\[
\begin{aligned}
g[dm+p(B-Am^2)]+dmp-2ABp^2(m^2-1)&=0,\\
4(v^2+w^2-2pvw)&=1+m^2-2mpr.
\end{aligned}
\tag{104.22}
\]
For every supported coordinate \(j\), substitution of (104.19) and the full equation \(Ga=0\) gives
\[
(LW)_{jj}=-\frac\alpha2\left[|a_j|^2+
\overline{a_j}\sum_{\substack{i\in S\\i\text{ in a different fibre}}}
\frac{T_{ji}a_i}{H_{ji}}\right].
\tag{104.23}
\]
The product-term sum is restricted to supported coordinates in a different original fibre:
\(\alpha\overline{a_j}\sum_{i\in S,\ i\notin f(j)}G_{ji}a_i/2=-\alpha|a_j|^2/2\),
where \(f(j)\) is the original fibre containing \(j\). Same-fibre off-diagonal Gram entries vanish, and all outside kernel coordinates vanish. Hence no outside assumption is hidden in (104.23). The original dual gives \((LW)_{33}=t\pi/2>0\). Its imaginary and real parts are
\[
\begin{aligned}
\Im\left[z(1+m\overline u)+\frac{z^2}{\overline h}\right]&=0,\\
j:=-|z|^2-\frac12\Re\left[z(1+m\overline u)+\frac{z^2}{\overline h}\right]&>0,
\qquad\pi=\alpha j/t.
\end{aligned}
\tag{104.24}
\]
The complex denominator is conjugated before taking the imaginary part.

Write \(T_0=\eta+\zeta\), \(\lambda=(\zeta-\eta)/d\), \(\Delta=\eta\zeta-g^2\), \(R_z=|z|^2\), and \(H_0=|h|^2\). From (104.22),
\[
\eta=(T_0-d\lambda)/2,\quad\zeta=(T_0+d\lambda)/2,
\quad g=p(T_0-\lambda)/2,\quad
K_0=T_0-2pg>0.
\tag{104.25}
\]
The last inequality traces \(M_0\) against \(\begin{pmatrix}1&-p\\-p&1\end{pmatrix}\succ0\).

Within the real antiunitary coordinates, rotate the singleton plane so the complex error vector is multiplied by \(z/|z|\). This computes the same coefficient norm and preserves \(\pi I_2\); it is not a physical real gauge. In this basis define
\[
\begin{aligned}
F_0&=\begin{pmatrix}-q\eta&g-p\eta\\-mqg&m(\zeta-pg)\end{pmatrix},
&M_E&=F_0^TF_0/(2q^2R_z),\\
Q_0&=-\frac{R_z}{2H_0}
\begin{pmatrix}\Re h&\Im h\\\Im h&-\Re h\end{pmatrix},
&w_0^2&=R_z^2/(4H_0),\\
s_0&=R_zK_0/(2\Delta),&k&=-\lambda H_0/\Delta.
\end{aligned}
\tag{104.26}
\]
The actual cross shape is \(E^{-1}C_1=s_0I+kQ_0\), by the two-by-two inverse and (104.22), and
\[
s_0^2-k^2w_0^2=q^2R_z^2/\Delta>0.
\tag{104.27}
\]
In particular it is positive definite. No division by \(\lambda\) or \(k\) has occurred.

Let \(e_1=1/2-K_{13}\), \(e_2=1/2-K_{23}\), and \(\ell=1/2-K_{34}\), where here \(K=G_S\odot H_S\). Direct substitution of (104.20) gives
\[
ze_1=\frac{-\eta+i(p\eta-g)/q}{2},\qquad
ze_2=\frac{m[-g+i(pg-\zeta)/q]}2.
\tag{104.28}
\]
Put \(D_0=[p\eta+(m^2-1)g-pm^2\zeta]/(2q)\). The third kernel row and (104.24) yield the rotated actual singleton coefficient
\[
\ell_{\rm rot}=\frac h{R_z}
\left[\frac{\eta+m^2\zeta}{2}-j+iD_0\right],\qquad
J_0=\begin{pmatrix}\Re\ell_{\rm rot}&\Im\ell_{\rm rot}\\
\Im\ell_{\rm rot}&-\Re\ell_{\rm rot}\end{pmatrix}.
\tag{104.29}
\]
Indeed \(z(e_1+m\overline ue_2)=-(\eta+m^2\zeta)/2+iD_0\), while
\(\overline\ell z^2/\overline h=-j-z(e_1+m\overline ue_2)\); conjugation gives (104.29).

**Lemma 104.4.** On these actual data the complete prescribed Sylvester equation in (104.16) is equivalent to the two scalar equations
\[
\mathcal F_1=jks_E-4\operatorname{Tr}(M_EQ_0)=0,
\qquad
\mathcal F_2=j^2-s_E(js_0+4w_0^2)=0.
\tag{104.30}
\]

**Proof.** Write \(B_0=F_0^TF_0\),
\(b_c=(B_{0,11}-B_{0,22})+2iB_{0,12}\), and
\(K_1=d(m^2+1)+m^2-1\). Expanding (104.25) gives
\[
D_0=-\lambda pK_1/(4q),\qquad
\Im(b_c\overline h)=-pqK_1\Delta.
\tag{104.31}
\]
For \(D_E=M_EY_0+Y_0M_E-J_0\), its traceless component perpendicular to \(Q_0\) vanishes: the corresponding imaginary part, after multiplying its complex coordinate by \(R_z\overline h\), is
\(-k\Im(b_c\overline h)/(4q^2)-H_0D_0=0\).
The anticommutator with \(Q_0\) contributes only a scalar and a multiple of \(Q_0\). Directly from (104.26) and (104.29),
\[
\operatorname{Tr}(M_ES)=\frac{\eta+m^2\zeta}{2},\qquad
\operatorname{Tr}(J_0Q_0)=j-\frac{\eta+m^2\zeta}{2}.
\tag{104.32}
\]
Thus
\[
D_E=-\frac{\mathcal F_1}{2j}I
-\frac{\mathcal F_2}{2jw_0^2}Q_0.
\tag{104.33}
\]
For its second trace, expand
\(\operatorname{Tr}(D_EQ_0)=-k\operatorname{Tr}(M_EQ_0)+4w_0^2s_E/j-\operatorname{Tr}(J_0Q_0)\)
and use \(\operatorname{Tr}(M_ES)=s_Es_0+k\operatorname{Tr}(M_EQ_0)\); the mixed terms cancel. Equations (104.31)–(104.32) prove (104.33), including \(\lambda=0\). Since \(I,Q_0\) are independent, (104.30) is equivalent to the whole residual being zero. Lemma 104.3 then applies, with the same original norm (104.17). \(\square\)

### 104.5. Original-coordinate normalization and a two-sided ratio window

The following operations act on all eight coordinates. Changing the sign of the second record-space basis vector and reciprocally rephasing coordinate 2 sends \((u,m)\) to \((-u,-m)\). Swapping the two coordinates of the whole fibre, swapping the record basis and reciprocally rephasing the singleton records by \(\overline u,u\), followed by rescaling the kernel by \(1/m\), sends
\[
(A,u,m,z,\alpha)\longmapsto
(B,\overline u,1/m,\overline uz/m,\alpha m^2).
\tag{104.34}
\]
The reciprocal phases preserve product coefficients, and the whole-fibre swap simultaneously reindexes the product and target matrices. Thus the full norm, ranks, fibre identities and full-domain local-minimum property are preserved. These operations normalize
\[
\tfrac12<A<\tfrac34,\quad B=1-A,\quad0<d<\tfrac12,
\quad0<p<1,\quad q\ne0.
\tag{104.35}
\]
Both signs of \(q\) are retained.

**Lemma 104.5.** In this chart,
\[
1<\mu<m<(A/B)\mu,\qquad
\mu=\frac{d/p+\sqrt{(d/p)^2+4AB}}{2A}.
\tag{104.36}
\]
Equivalently \(p(Am-B/m)>d>p(Bm-A/m)\).

**Proof.** Write \(X=p(Am-B/m)\), \(Y=p(Bm-A/m)\),
\(F_*=d(m-1/m)+2p\), and \(h_2=d^2+(1-d^2)p^2\).
First \(X\ne d\): if equality held, (104.22) would give
\(d=2ABp(m-1/m)\); comparison gives \(pd(Am+B/m)=0\), impossible because \(Am^2+B>0\).
The actual positive matrix obeys
\[
M_0(-1)=M_0(r)+(r+1)\operatorname{diag}(B,A)\succ0.
\]
Eliminating \(g\) in (104.22) gives the exact identities
\[
\operatorname{Tr}M_0(-1)=\frac{pdF_*}{X-d},\qquad
\det M_0(-1)=\frac{h_2(d-Y)}{X-d}.
\tag{104.37}
\]
If \(m>0\), then \(X-Y=pd(m+1/m)>0\); determinant positivity forces \(X>d>Y\). Both functions are increasing on \(m>0\), with respective positive roots at level \(d\) equal to \(\mu\) and \((A/B)\mu\). Also \(X(1)=pd<d\), so \(\mu>1\).
If \(m<0\), determinant positivity instead gives \(X<d<Y\). Put \(n=-m>0\). Then \(p(A/n-Bn)>d\), which forces \(n<1\), since for \(n\ge1\) its left side is at most \(pd<d\). Hence \(F_*=d(1/n-n)+2p>0\), while \(X-d<0\). The trace in (104.37) would be negative. This contradiction proves (104.36). Only a Loewner comparison at \(r=-1\) was used; no physical endpoint completion is asserted. \(\square\)

### 104.6. Coherent-input and actual-partner bounds

Let
\[
c_*=(\sqrt{33}-5)/4,\qquad
h_2=|h|^2=d^2+(1-d^2)p^2.
\]
The original product bounds on coordinates \(2,3,4\) are
\[
|K_{23}|,|K_{24}|\le B,\qquad |K_{34}|\le h_2.
\]
For \(0<\theta\le1\), use the legitimate original block density with masses
\(1-\theta,\theta/2,\theta/2\) on these coordinates, zero elsewhere. If \(v\) consists of the square roots of those masses, then \(2vv^*-I\) is a Hermitian contraction. The compressed coefficient has zero trace, and the complete-norm formula gives
\[
\begin{aligned}
t&\ge\|\sqrt\rho L\sqrt\rho\|_1
\ge4\sum_{i<j}\rho_i\rho_j\Re L_{ij}\\
&\ge2d\theta+(\tfrac12-h_2-2d)\theta^2.
\end{aligned}
\tag{104.38}
\]
This is the original transpose-consistent block-density consumer of §91. It uses one allowed coherent input, not a change to the actual common pair.

Taking \(\theta=1\) for \(d\le1/4\), and \(\theta=1/(4d)\) otherwise, proves
\[
h_2>\begin{cases}
1/4,&0<d\le1/4,\\
4d^2-2d+1/2,&1/4\le d<1/2.
\end{cases}
\tag{104.39}
\]
For \(d\le1/4\), this gives \(p^2>1/5>c_*\). For the other range, put
\(d_*=(7-\sqrt{33})/4=1/(3+c_*)\). Then
\[
\frac{3d^2-2d+1/2}{1-d^2}
=c_*+\frac{(3+c_*)(d-d_*)^2}{1-d^2}\ge c_*.
\tag{104.40}
\]
Thus \(p^2>c_*\). The rational lower bound \(p>56/131\) follows from
\(33\cdot17161^2-98349^2=45971592>0\). If \(m\ge21/4\), the inequalities \(B>1/4\), \(A<3/4\) imply
\[
Bm-A/m>m/4-3/(4m)\ge131/112.
\]
Together with \(p>56/131\) this contradicts \(p(Bm-A/m)<d<1/2\). Hence \(1<m<21/4\).

Let \(o\) be the actual original partner of singleton coordinate 3. Its full unit \(H\) record is orthogonal to \(h_3\). Projection in the full record space gives
\[
|H_{o4}|^2\le1-|H_{34}|^2=1-h_2.
\]
The record \(h_o\) may have arbitrary complex components outside the supported two-dimensional span. Since \(|G_{o4}|\le1\) and \(|1/2-G_{o4}H_{o4}|<1/4\), one has \(|G_{o4}H_{o4}|>1/4\), whence \(h_2<15/16\). As \(1-h_2=4ABq^2\), the resulting strict bounds are
\[
c_*<p^2<15/16,\qquad |q|>1/4,\qquad
1<m<21/4,\qquad1/4<h_2<15/16.
\tag{104.41}
\]
They use the actual full-space partner and its full norm, without selecting an outside completion.

### 104.7. Regularized separation from the unbiased boundary

The unit-norm equation gives
\[
|z|^2=\frac{1+m^2-2mpr}{4q^2},\qquad
\tfrac12<v<\tfrac{25}2,\quad |z|,|w|,|g|<\tfrac{25}2.
\tag{104.42}
\]
For \(g\), use \(g^2<\eta\zeta<|z|^2/m\); and \(v>A>1/2\) also implies \(|z|^2>1/4\).
Set \(\kappa=(m-1)/d\) and \(\xi=[p(Am-B/m)-d]/d\). Multiplying the second endpoint inequality in Lemma 104.5 by \(2m\) gives
\[
0<\kappa<m+2/p<139/14<10.
\tag{104.43}
\]
The commutator rearranges exactly to
\[
g+p=\frac{p^2(Am^2+B)}{m\xi}>0.
\tag{104.44}
\]
Since \(Am^2+B-m=(m-1)(Am-B)>0\), (104.42) yields
\(\xi>2c_*/27>1/80\). The last inequality follows from
\(c_*>27/160\), equivalently \(\sqrt{33}>227/40\).
With \(m=1+d\kappa\), the apparent factors \(d\) cancel:
\[
\begin{aligned}
C_*&=m-p[1+A\kappa(m+1)]=-m\xi<-1/80,\\
g&=\frac{2ABp^2\kappa(m+1)-mp}{C_*},\\
\lambda&=1-r+p(m+1/m)-\kappa(m+1)(g+p)/m.
\end{aligned}
\tag{104.45}
\]
These are regular expressions on the indicated bounded coordinates. No division by \(\Delta\) or \(j\) enters the following margin.

**Lemma 104.6.** Every actual point satisfies
\[
d>10^{-6},\qquad
\kappa>1/32,\qquad
m-1>1/32000000.
\tag{104.46}
\]

**Proof.** At \(d=0,m=1\), the closure of the positive cross-stress and unit-norm conditions would give
\[
v=w,\quad \eta=\zeta=v-1/2,\quad g=v-p+r/2,
\quad r\le2p-1,\quad
4(1-p)v^2=1-pr,
\quad v\ge v_0:=\sqrt{1+2p}/2>1/2.
\]
The actual complex expression (104.24) then becomes
\[
j_0(v,p)=v-\frac{v^2(1+2p)}{p(1+p)}.
\tag{104.47}
\]
For \(0<p<1\),
\[
4(1+2p)^3-25p^2(1+p)^2
=4+24p+23p^2-18p^3-25p^4
\ge4+24p-20p^2\ge4+4p>0.
\]
Hence \(j_0(v_0,p)<-v_0/4<-1/8\). This function is decreasing for \(v\ge1/2\), since \((1+2p)/(p(1+p))>3/2\).

For an explicit margin suppose \(0<d\le10^{-6}\). From (104.43), \(m-1<10d\). The two linear identities in (104.21) and (104.42) give
\[
|w-v|<146d,\qquad r<2p-1+145d.
\tag{104.48}
\]
For the first, the three contributions are bounded by \(125d,12d,17d/2\). For the second, test \(M_0\) on \((1,-1)\) and use
\((m-1)^2/m<m-1\), \(|g|<25/2\), and
\(|Bm+A/m-1|<m-1\).
Writing \(e=w-v\), the exact unit-norm expansion is
\[
4(1-p)v^2=1-pr+(m^2-1)/2-p(m-1)r
-4(1-p)ve-2e^2.
\]
As \(1-p>1/32\), (104.48) implies
\[
4v^2\ge1+2p-E_d,\qquad
E_d=12260d+1364224d^2.
\tag{104.49}
\]
Indeed a lower bound before division is
\((1-p)(1+2p)-155d-7300(1-p)d-42632d^2\).

Set \(z_0=-v+i(p-1)v/q\), \(h_0=p\overline u\). Then
\[
|z-z_0|<584d,\quad |z_0|<25,\quad|h-h_0|\le d,
\quad |h|\ge p>2/5.
\]
Comparison of the squared, linear and reciprocal-quadratic terms of (104.24) with their values at \((z_0,m=1,h_0)\) gives, respectively, bounds
\(21900d,1950d,29329d\). For the last one, use
\[
\left|\frac{z^2}{\overline h}-\frac{z_0^2}{\overline h_0}\right|
\le\frac{(|z|+|z_0|)|z-z_0|}{|h|}
+\frac{|z_0|^2|h-h_0|}{|h|p}
<(54750+15625/4)d.
\]
Consequently \(|j-j_0(v,p)|<54000d\).
If \(v<v_0\), (104.49) gives \(v_0-v\le E_d/4\), and the absolute derivative of \(j_0\) on this intervening interval is less than 7. If \(v\ge v_0\), its monotonicity is enough. In both cases
\[
j<-1/8+75455d+2387392d^2<0
\qquad(0<d\le10^{-6}).
\tag{104.50}
\]
The final comparison is exact at the right endpoint, where its value is
\(-387051661/7812500000\). This contradicts \(j>0\).
Finally
\(p(Am-B/m)-pd=p(m-1)(A+B/m)<m-1\).
The first endpoint inequality and \(1-p>1/32\) give
\(m-1>d/32\), proving the other claims. In addition
\(|dm+p(B-Am^2)|=md\xi>1/80000000\). \(\square\)

### 104.8. Opposite-polar and quotient-rank margins

**Lemma 104.7.** The actual chart satisfies
\[
A<3/4-1/50000,\qquad1-r^2>10^{-10}.
\tag{104.51}
\]

**Proof.** For the first claim suppose \(3/4-1/50000\le A<3/4\) and put \(\epsilon=(B-1/4)/B\le1/12500\). The actual 23 and 24 errors imply
\[
\Re(\overline u^2\mathsf R_{23})>1-\epsilon,
\qquad\Re(u^2\mathsf R_{24})>1-\epsilon.
\]
Thus \(\|b_3-u^2b_2\|,\|b_4-\overline u^2b_2\|<\sqrt{2\epsilon}\).
By the first identity in (104.20), \(b_1\) differs from a real multiple of \(b_2\) by norm less than \(25\sqrt{2\epsilon}\). Projecting orthogonally onto \(b_2\) gives
\(1-r^2<1250\epsilon\le1/10\). Hence \(r\ne0\). For \(\sigma=\operatorname{sign}r\),
\(|r-\sigma|\le1-r^2<1250\epsilon\).
Set \(x=\mathsf R_{23}\), \(y=\mathsf R_{13}\). Gram Cauchy–Schwarz gives
\[
|y-rx|\le\sqrt{1-r^2}\sqrt{1-|x|^2}<50\epsilon,
\qquad |x-u^2|<\sqrt{2\epsilon}.
\]
Therefore \(|y-\sigma u^2|<\sqrt{2\epsilon}+1300\epsilon<44/375\), so
\(|K_{13}-\sigma A\overline u^2|<11/125\). Its original error then forces
\[
|1/2-\sigma A\overline u^2|<169/500.
\]
But (104.41) gives \(|\Re u^2|<7/8\), and \(A>7/10\) implies that the square of this modulus is greater than
\(1/4+A^2-7A/8\ge51/400>49/400\). It therefore exceeds \(7/20=175/500\), a contradiction.

For the second claim put \(\delta=\sqrt{1-r^2}\), and suppose \(\delta\le10^{-5}\). Write \(b_2=rb_1+\delta e\) with \(e\perp b_1\) unit. Formula (104.20) and (104.41)–(104.42) bound the perpendicular components of \(b_3,b_4\) by \(21\delta<1\). Choose the unit phases \(\beta_3,\beta_4\) of their nonzero \(b_1\)-components, and \(\beta_1=1\). The elementary identity
\[
\|b_i-\beta_i b_1\|^2=2(1-|\langle b_1,b_i\rangle|)
\le2(1-|\langle b_1,b_i\rangle|^2)
\]
gives distances less than \(30\delta\).
On the distinct original fibres \(\{1,3,4\}\), compare \(\mathsf R\) with the rank-one correlation
\((\mathsf R_0)_{ij}=\overline{\beta_i}\beta_j\). Its oriented edge differences are bounded by \(30\delta,60\delta,30\delta\). Choose phases \(\kappa_i^2=\overline{\beta_i}\). The rank-at-most-two correlation
\(H'=\operatorname{diag}(\kappa)^*H_{134}\operatorname{diag}(\kappa)\)
satisfies \(H'\odot H'=H_{134}^{\odot2}\odot\overline{\mathsf R_0}\).
This is a comparison matrix, not a replacement physical channel.

If \(E\) and \(E_0\) denote the sums of the three squared edge errors for the actual product and this comparison, respectively, then
\(\sqrt E\ge\sqrt{E_0}-\sqrt{5400}\delta>\sqrt{E_0}-74\delta\).
The uniform original density on \(\{1,3,4\}\), the traceless three-dimensional trace-norm bound, and RT III Theorem 93.1 give
\[
t\ge\frac23\sqrt E>
\frac{\sqrt{21-9\sqrt[3]9}}6-\frac{148}3\delta.
\tag{104.52}
\]
The first constant exceeds \(251/1000\): use \(\sqrt[3]9<2081/1000\) and
\((21-9\cdot2081/1000)/36>(251/1000)^2\).
For \(\delta\le10^{-5}\), the right side of (104.52) exceeds \(1/4\), contradicting (104.2). \(\square\)

### 104.9. Same-normer denominator bounds

**Lemma 104.8.** The actual quantities satisfy
\[
\frac1{8000000}<j<\frac{3125}8,
\qquad\Delta>10^{-27}.
\tag{104.53}
\]

**Proof.** There are exactly five undirected target edges on \(S\). Every supported kernel entry has modulus less than \(25/2\), and each supported cross-fibre \(|H_{ij}|>1/2\). Hence (104.19) gives \(|W_{ij}|<625\alpha/4\). Summing the ten ordered edges in \(t=2\operatorname{Tr}(LW)\) and using \(|L_{ij}|\le t\) yields
\(t<3125\alpha t\), so \(\alpha>1/3125\).
Also \(|W_{34}|=\alpha|z|^2/(2|h|)\). The inequalities
\(0\preceq W_{JJ}\preceq\pi I_2\), tested on the two equal-modulus vectors aligning the off-diagonal entry, imply \(|W_{34}|\le\pi/2\). Thus
\[
\pi\ge\alpha|z|^2/|h|>\alpha/4,
\qquad1/3125<\alpha<2,\qquad\pi>1/12500.
\tag{104.54}
\]
Here \(\pi<1/2\) follows from the positive whole-fibre density. Since
\(t\ge1/2-B=d/2>1/2000000\) and \(\pi=\alpha j/t\), the two bounds for \(j\) follow.

In the real rotated coordinates of (104.26), the exact cross shapes are
\[
C_1=-\frac{|z|}{\sqrt2}\begin{pmatrix}1&0\\mp&-mq\end{pmatrix},
\qquad E=\frac{F_0}{\sqrt2q|z|},
\qquad |\det E|=\frac{m\Delta}{2|q||z|^2}.
\tag{104.55}
\]
One has \(|\det C_1|=m|q||z|^2/2>1/32\) and
\(\|C_1\|_F^2=|z|^2(1+m^2)/2<285625/128<48^2\). Therefore
\(\sigma_{\min}(C_1)>1/1536\) and
\(\sigma_{\min}(C)>1/4800000\), where \(C=\alpha C_1\).
By (104.9), with \(Y=tY_0\),
\[
C=\frac\pi{2t}E(I-Y^2),\quad0\prec I-Y^2\preceq I,
\quad CC^*\preceq(\pi/(2t))^2EE^*.
\]
It follows that
\(\sigma_{\min}(E)>4t\sigma_{\min}(C)>1/2400000000000\).
Finally \(2|q||z|^2/m>1/42\), so (104.55) yields
\[
\Delta>\frac1{42(2400000000000)^2}>10^{-27}.
\]
Every inequality concerns this same original common pair. \(\square\)

### 104.10. Reciprocal invariants and the complete necessary system

Use the scalar \(a_0\), distinct from the full kernel vector, to define
\[
D=d^2,\quad a_0=(m-1/m)/d,\quad M=m+1/m=\sqrt{4+Da_0^2},
\quad Q=1-p^2,\quad H=p^2+DQ=|h|^2.
\tag{104.56}
\]
The square root is positive. The inverse is \(d=\sqrt D\),
\(m=(M+\sqrt D\,a_0)/2\), so this reparametrizes \((d,m)\) injectively on the normalized chart. It neither recovers nor identifies the two original signs \(q=\pm\sqrt Q\); the necessary equations below hold separately for each sign.
Dividing (104.22) only by positive \(d,m\) gives
\[
x:=g+p=\frac{p^2(M+Da_0)}{p(M+a_0)-2}>0,
\qquad p(M+a_0)-2=2\xi>1/40.
\tag{104.57}
\]
Define
\[
\begin{aligned}
V&=xM-pDa_0-r,&Z&=-xa_0+pM-r,\\
T_0&=V-1,&\lambda&=Z+1,&g&=x-p,\\
\Delta&=(T_0^2-D\lambda^2)/4-g^2,&K_0&=T_0-2pg.
\end{aligned}
\tag{104.58}
\]
These agree with the quantities in (104.25). In particular
\[
g=p(T_0-\lambda)/2,\quad
\eta=(T_0-d\lambda)/2,\quad\zeta=(T_0+d\lambda)/2,
\quad v=(V-dZ)/2,\quad w=m(V+dZ)/2.
\tag{104.59}
\]
The quotient unit-norm and actual phase equations become
\[
\begin{aligned}
N={}&(M-2p)V^2+D(M+2p)Z^2+2Da_0VZ-M+2pr=0,\\
P={}&-2H[(2+pM)Z+pa_0V]+2(V^2-DZ^2)\\
&+p[(a_0-M)(V^2+DZ^2)+2(M-Da_0)VZ]=0.
\end{aligned}
\tag{104.60}
\]
For an explicit check of the phase convention, put
\[
P_H=H[pv-w+m(v-pw)]+2[dvw+Bpw^2-Apv^2].
\]
Expansion gives
\(P_H=qH\Im[z(1+m\overline u)+z^2/\overline h]\)
and \(P=4P_H/(dm)\). Thus the correct conjugated denominator and both nonzero \(q\) signs are retained.

On the actual unit-norm data put
\[
\begin{aligned}
R&=(M-2pr)/(4Q)=|z|^2/m,\\
J_*&=\frac{(2p-p^2M-DQa_0)V^2-D(2p+p^2M+DQa_0)Z^2
-2D(QM+p^2a_0)VZ}{4QH},\\
\overline C&=(MT_0+Da_0\lambda)/4,\\
\Gamma&=(M-Da_0)/4-R-J_*/2,\qquad\overline j=\overline C+\Gamma=j/m.
\end{aligned}
\tag{104.61}
\]
Here \(R\) is a scalar, distinct from the correlation \(\mathsf R\). Substitution of (104.59) into the actual complex expression shows
\(J_*=\Re(z^2/\overline h)/m\) and
\(\overline j=-R+(MV+Da_0Z)/4-J_*/2\), proving these identities without a free choice of singleton coefficient.

Define the positive-square expression
\[
\begin{aligned}
U_0&=T_0/2-pg,\\
\overline B&=M[U_0+Da_0\lambda/(2M)]^2
+D\lambda^2/M+MQg^2,\qquad s_E=\overline B/(2QR).
\end{aligned}
\tag{104.62}
\]
Indeed \(\overline B=\operatorname{Tr}(F_0^TF_0)/m\). Expanding the weighted squared errors first gives
\[
\overline B=M[(T_0^2+D\lambda^2)/4-pgT_0+g^2]
+Da_0\lambda(T_0/2-pg),
\]
and completing the square, using \(M^2-Da_0^2=4\), gives (104.62).
Set
\[
\begin{aligned}
P_+&=-p^2QT_0^2+2Q(D+p^2)T_0\lambda
+p^2(D+p^2)\lambda^2,\\
P_-&=Q^2T_0^2+2p^2QT_0\lambda+(DQ+p^4+p^2)\lambda^2,\\
B_*&=-(MP_++Da_0P_-)/4.
\end{aligned}
\tag{104.63}
\]
This \(B_*\) is \(\operatorname{Tr}(F_0^TF_0\mathsf H)/m\), with
\(\mathsf H=\begin{pmatrix}\Re h&\Im h\\\Im h&-\Re h\end{pmatrix}\).
To verify it, write the trace as \(H_1/m+mH_2\), where
\[
\begin{aligned}
H_1&=[Q\eta^2-(g-p\eta)^2]\Re h+4BpQ\eta(g-p\eta),\\
H_2&=[Qg^2-(\zeta-pg)^2]\Re h+4BpQg(\zeta-pg).
\end{aligned}
\]
Equation (104.59) gives \(H_1+H_2=-P_+/2\) and
\((H_2-H_1)/d=-P_-/2\), proving (104.63).

The complete scalar equations (104.30) are exactly
\[
\begin{aligned}
2R\Delta B_*-\overline j\lambda H^2\overline B&=0,\\
4Q\Delta H\overline j^{\,2}
-\overline B[\overline jK_0H+2R\Delta]&=0.
\end{aligned}
\tag{104.64}
\]
For the first, use
\(\operatorname{Tr}(M_EQ_0)=-\operatorname{Tr}(F_0^TF_0\mathsf H)/(4q^2H)\),
multiply \(\mathcal F_1\) by \(2q^2|z|^2\Delta H\), and divide by \(m^2\). For the second multiply \(\mathcal F_2\) by \(4q^2\Delta H\) and divide by \(m^2\). Every removed denominator is positive. The case \(\lambda=0\) remains included.
The same norm (104.17) is
\[
t^{-2}=\frac{RK_0}{\Delta\overline j}
+\frac{\lambda^2H^2}{4\Delta^2}
+\frac{R^2}{H\overline j^{\,2}}>16.
\tag{104.65}
\]

There are two additional strict consequences of the complete normer:
\[
\overline j>\overline C>0,\qquad\overline B<QR/4.
\tag{104.66}
\]
For the first, \(Y_0=-kI/2+2Q_0/j\) and \(\operatorname{Tr}J_0=0\) give
\[
\operatorname{Tr}(J_0Q_0)
=(j/2)\operatorname{Tr}(J_0Y_0)
=j\operatorname{Tr}(Y_0M_EY_0)>0.
\]
The inequality is strict because \(M_E\succ0\) and the nonzero traceless part \(2Q_0/j\) makes \(Y_0\ne0\). Apply (104.32) and divide by \(m\); also \(\overline C=(\eta+m^2\zeta)/(2m)>0\).
For the second, Lemma 104.2 gives \(s_E=(2-\gamma)t^2<1/8\), which is equivalent to (104.66).
Finally (104.29), together with
\(D_0/m=-dp\lambda(a_0+M)/(4q)\), gives the actual 34 bound
\[
R^2-16H\left[(\overline C-\overline j)^2
+\frac{Dp^2\lambda^2(a_0+M)^2}{16Q}\right]>0.
\tag{104.67}
\]
Its modulus is unchanged by the real coefficient rotation. This is precisely the original matrix-unit inequality \(|1/2-K_{34}|<1/4\).

### 104.11. Full rational root and compact quadratic identities

Lemmas 104.5–104.8 imply that every actual point belongs to the rational box
\[
\mathcal B_*=
[10^{-12},(12499/25000)^2]\times[56/131,31/32]
\times[1/32,425/42]
\tag{104.68}
\]
in the ordered coordinates \((D,p,a_0)\), and to the full auxiliary interval
\[
\mathcal I_r=[-19999999999/20000000000,
19999999999/20000000000].
\tag{104.69}
\]
For (104.68), use \(d<12499/25000\), \(c_*>(56/131)^2\),
\(15/16<(31/32)^2\), and \(a_0=\kappa(m+1)/m>1/32\).
The second endpoint inequality in Lemma 104.5 says \(p(a_0-M)<2\). Since
\(2<M<457/84\), it gives
\(a_0<M+2/p<457/84+131/28=425/42\).
For (104.69), if \(b=1-1/(2\cdot10^{10})\), then
\(b^2>1-10^{-10}>r^2\).
These are bounding boxes; closedness of the actual local-minimum set is not used.

The following intermediate cuts also retain every actual value:
\[
\begin{aligned}
2&\le M\le457/84,&1/40&\le p(M+a_0)-2\le30,\\
0&\le x\le27/2,&10^{-27}&\le\Delta\le10000,\\
1/21&\le R\le625/4,&1/42000000&\le\overline j\le3125/8.
\end{aligned}
\tag{104.70}
\]
The denominator lower bound is (104.57); its upper bound is loose even with \(a_0<20\), \(M<457/84\), \(p<1\). The bound for \(x=g+p\) follows from (104.42), and
\(\Delta<\eta\zeta<625/4<10000\). The last two pairs follow from
\(1/4<|z|^2<625/4\), (104.53), and \(1<m<21/4\).

For fixed \((D,p,a_0)\), both polynomials in (104.60) are quadratic in \(r\). Put
\[
V_0=xM-pDa_0,\quad Z_0=-xa_0+pM,\quad
c_N=M-2p,\quad d_N=D(M+2p),\quad e_N=Da_0.
\]
Their compact coefficients, with no division by a leading term, are
\[
\begin{aligned}
n_2={}&c_N+d_N+2e_N,\\
n_1={}&4[p(M+Da_0)-2]x-2p[2Dp(M+a_0)+4D-1],\\
n_0={}&4(M-2p)x^2-8Da_0px+4Dp^2(M+2p)-M,\\
a_2={}&(1-D)[2+p(a_0+M)],\\
a_1={}&-4(M+Da_0)x+2(M+a_0)p[D(3-p^2)+p^2]
+4D(p^2+1)-4p^2,\\
a_0'={}&4x[Da_0+p^2(M+a_0)]-4Mp(D+p^2)-4Da_0p^3
+8Dp^4-16Dp^2-8p^4.
\end{aligned}
\tag{104.71}
\]
Thus \(N=n_2r^2+n_1r+n_0\) and \(P=a_2r^2+a_1r+a_0'\).
To check (104.71), substitute \(V=V_0-r\), \(Z=Z_0-r\) into (104.60), expand by powers of \(r\), and use
\(M^2-Da_0^2=4\) and
\([p(M+a_0)-2]x=p^2(M+Da_0)\).
This is a polynomial identity after multiplication by the nonzero denominator in (104.57). The auxiliary scalar name \(a_0'\) distinguishes the constant coefficient from the invariant coordinate \(a_0\).

### 104.12. Exact grid-interval algebra

Fix the integer $s=2^{112}$. A grid interval is a pair of integers $[a,b]_s$ with $a\le b$, denoting the real closed interval $[a/s,b/s]$. For rational $x\le y$, put
\[
 \langle x,y\rangle_s=[\lfloor sx\rfloor,\lceil sy\rceil]_s,
 \qquad \langle x\rangle_s=\langle x,x\rangle_s.
\]
All integers and rational constants in interval expressions are lifted this way. Rational expressions specifying endpoints in this definition are evaluated in $\mathbb Q$ before lifting.

For $X=[a,b]_s$ and $Y=[c,d]_s$, define
\[
\begin{aligned}
 X+Y&=[a+c,b+d]_s,&-X&=[-b,-a]_s,\\
 X-Y&=X+(-Y),\\
 XY&=\left[\left\lfloor\frac{\min(ac,ad,bc,bd)}s\right\rfloor,
            \left\lceil\frac{\max(ac,ad,bc,bd)}s\right\rceil\right]_s.
\end{aligned}                                                    \tag{104.72}
\]
The square $X^{[2]}$ is
\[
 X^{[2]}=\begin{cases}
 [0,\lceil\max(a^2,b^2)/s\rceil]_s,&a\le0\le b,\\
 [\lfloor\min(a^2,b^2)/s\rfloor,
                \lceil\max(a^2,b^2)/s\rceil]_s,&\text{otherwise}.
 \end{cases}                                                     \tag{104.73}
\]
If $0\notin Y$, define
\[
 Y^{-1}=[\lfloor s^2/d\rfloor,\lceil s^2/c\rceil]_s,
 \qquad X/Y=X(Y^{-1}).                                            \tag{104.74}
\]
Thus division means the outward reciprocal followed by the outward product, not a single rounding of four quotients. If $0\in Y$, this operation is undefined.

For $b\ge0$, the nonnegative square-root interval is
\[
 \sqrt{X}=
 [\lfloor\sqrt{s\max(0,a)}\rfloor,\lceil\sqrt{sb}\rceil]_s.        \tag{104.75}
\]
Both endpoint integers are uniquely specified by the adjacent integer-square inequalities; no approximate square root is part of the definition. A required square root with $b<0$ is impossible.

Intersection is $[\max(a,c),\min(b,d)]_s$, declared empty when its lower integer exceeds its upper integer. For rational $l\le u$, let
\[
 \operatorname{cut}_{l,u}(X)=X\cap\langle l,u\rangle_s.
\]
The operation $\operatorname{pos}(X)$ declares a contradiction if the upper endpoint of $X$ is nonpositive; otherwise it returns $X$ unchanged. It does not clip a negative lower endpoint. Write $\operatorname{zero}(X)$ for $0\in X$.

Every square in §§104.13–104.16 means the interval square (104.73). Products of three or more factors are evaluated left to right, as are sums and differences. Multiplication and division have precedence over addition and subtraction. Parentheses override these rules; each named intermediate is evaluated once and used as the resulting interval. Exponents four mean an iterated square when explicitly written $(X^{[2]})^{[2]}$. No algebraically equivalent reassociation is implicit in these interval expressions.

### 104.13. Root intervals and the rejection predicate

Let the ordered axes be $D,p,a$. The rational root before lifting is
\[
 \mathcal B_s=
 \left\langle\frac1{10^{12}},\left(\frac{12499}{25000}\right)^2\right\rangle_s
 \times\left\langle\frac{56}{131},\frac{31}{32}\right\rangle_s
 \times\left\langle\frac1{32},\frac{425}{42}\right\rangle_s.          \tag{104.76}
\]
Here $a$ is the interval for the positive scalar invariant $a_0$ of (104.56), not a Gram-kernel vector. The symbols $T,\lambda,\Delta,R,J,C,\Gamma,j,B,K$ in this interval calculus enclose respectively $T_0,\lambda,\Delta,R,J_*,\overline C,\Gamma,\overline j,\overline B,K_0$ of §§104.10–104.11. The interval phase coefficients $b_2,b_1,b_0$ correspond to $a_2,a_1,a_0^\prime$ in (104.71). Each box argument consists of three grid intervals contained in $\mathcal B_s$. The widths of the three root intervals, measured in integer grid units, are denoted by $w_D,w_p,w_a$.

Define a rejection predicate $\mathcal R(B)\in\{0,1\}$ through §§104.13–104.16 in their printed order. An empty intersection, an impossible required square root, or a contradiction declared by $\operatorname{pos}$ immediately gives $\mathcal R(B)=1$. Any undefined division, unless its explicitly stated zero-denominator branch below applies, immediately gives $\mathcal R(B)=0$. A stated zero-exclusion or strict-negative-discriminant test also immediately gives value one. If none occurs, §104.16 gives value zero. These are finite mathematical operations on the rational box.

Starting with its intervals $D,p,a$, form
\[
\begin{aligned}
 Q&=1-p^{[2]},\\
 M&=\operatorname{cut}_{2,457/84}\bigl(\sqrt{4+D a^{[2]}}\bigr),\\
 H&=p^{[2]}+DQ.
\end{aligned}                                                     \tag{104.77}
\]
Apply $\operatorname{pos}$ to $H-1/4$, then $15/16-H$, then $2-p(a-M)$. Form
\[
\begin{aligned}
 b&=\operatorname{cut}_{1/40,30}\bigl(p(M+a)-2\bigr),\\
 x&=\operatorname{cut}_{0,27/2}\bigl(p^{[2]}(M+Da)/b\bigr),
 &g&=x-p,\\
 V_0&=xM-pDa,&Z_0&=-xa+pM,\\
 c_N&=M-2p,&d_N&=D(M+2p),&e_N&=Da.
\end{aligned}                                                     \tag{104.78}
\]
The six quadratic coefficients are the following exact interval expressions:
\[
\begin{aligned}
 n_2={}&c_N+d_N+2e_N,\\
 n_1={}&4\bigl(p(M+Da)-2\bigr)x
                    -2p\bigl(2Dp(M+a)+4D-1\bigr),\\
 n_0={}&4(M-2p)x^{[2]}-8Dapx
                    +4Dp^{[2]}(M+2p)-M,\\
 b_2={}&(1-D)\bigl(2+p(a+M)\bigr),\\
 b_1={}&-4(M+Da)x
           +2(M+a)p\bigl(D(3-p^{[2]})+p^{[2]}\bigr)
           +4D(p^{[2]}+1)-4p^{[2]},\\
 b_0={}&4x\bigl(Da+p^{[2]}(M+a)\bigr)
           -4Mp(D+p^{[2]})-4Dap p^{[2]}
           +8D(p^{[2]})^{[2]}-16Dp^{[2]}-8(p^{[2]})^{[2]}.
\end{aligned}                                                     \tag{104.79}
\]
Also form
\[
\begin{aligned}
 c_V&=2+p(a-M),&c_Z&=D\bigl(-2+p(a-M)\bigr),\\
 c_X&=2p(M-Da),&l_V&=-2Hpa,&l_Z&=-2H(2+pM).
\end{aligned}                                                     \tag{104.80}
\]
If the upper endpoint of $n_1^{[2]}-4n_2n_0$ is strictly negative, reject. Otherwise do the same test on $b_1^{[2]}-4b_2b_0$. A zero upper endpoint does not pass either rejection test.

### 104.14. Complete auxiliary interval and root contractions

Initialize the full existential interval independently at every box:
\[
 r=\left\langle-\frac{19999999999}{20000000000},
                  \frac{19999999999}{20000000000}\right\rangle_s.
                                                                    \tag{104.81}
\]
Put $L_1=n_2b_1-b_2n_1$ and $L_0=n_2b_0-b_2n_0$. If $0\notin L_1$, replace $r$ by $r\cap(-L_0/L_1)$. If $0\in L_1$, make no division and reject only if $0\notin L_1r+L_0$.

For a quadratic coefficient triple $(c,b,d)$ and the current $r=[l,u]_s$, set the current exact midpoint interval
\[
 m=\left[\left\lfloor\frac{l+u}{2}\right\rfloor,
          \left\lfloor\frac{l+u}{2}\right\rfloor\right]_s,
 \quad A=2cr+b.                                                   \tag{104.82}
\]
If $0\notin A$, replace $r$ by
\[
 r\cap\left(m-\frac{cm^{[2]}+bm+d}{A}\right).                     \tag{104.83}
\]
If $0\in A$, retain $r$ unchanged. Perform this operation four times, in exactly the order
\[
 (n_2,n_1,n_0),\ (b_2,b_1,b_0),\ (n_2,n_1,n_0),\ (b_2,b_1,b_0).
                                                                    \tag{104.84}
\]
A new midpoint (104.82) is formed from the current interval before every operation, including after any preceding contraction. Empty intersections reject as specified in §104.13.

Next reject if zero is absent from $n_2r^{[2]}+n_1r+n_0$, and then reject if zero is absent from $b_2r^{[2]}+b_1r+b_0$.

### 104.15. Original residuals and positive inequalities

Form
\[
 V=V_0-r,\qquad Z=Z_0-r,\qquad
 T=\operatorname{pos}(V-1),\qquad \lambda=Z+1.                     \tag{104.85}
\]
Reject if zero is absent from either of the following expressions, tested in this order:
\[
\begin{aligned}
 N&=c_NV^{[2]}+d_NZ^{[2]}+2e_NVZ-M+2pr,\\
 P&=c_VV^{[2]}+c_ZZ^{[2]}+c_XVZ+l_VV+l_ZZ.
\end{aligned}                                                     \tag{104.86}
\]
The second expression is the displayed coefficient expansion of the correct original phase polynomial; it is the interval expression (104.86), rather than a reassociated unexpanded expression, that defines this predicate.

In the following order define
\[
\begin{aligned}
 \Delta&=\operatorname{cut}_{10^{-27},10000}
       \left(\operatorname{pos}\left((T^{[2]}-D\lambda^{[2]})/4-g^{[2]}\right)\right),\\
 R&=\operatorname{cut}_{1/21,625/4}\bigl((M-2pr)/(4Q)\bigr),\\
 J&=\bigl[(2p-p^{[2]}M-DQa)V^{[2]}
       -D(2p+p^{[2]}M+DQa)Z^{[2]}
       -2D(QM+p^{[2]}a)VZ\bigr]/(4QH),\\
 C&=\operatorname{pos}\bigl((MT+Da\lambda)/4\bigr),\\
 \Gamma&=\operatorname{pos}\bigl((M-Da)/4-R-J/2\bigr),\\
 j&=\operatorname{cut}_{1/42000000,3125/8}(C+\Gamma),\\
 U&=T/2-pg,\\
 B&=M\bigl(U+Da\lambda/(2M)\bigr)^{[2]}
                     +D\lambda^{[2]}/M+MQg^{[2]}.
\end{aligned}                                                     \tag{104.87}
\]
Here $B$ in (104.87) is an auxiliary interval, distinct from the geometric box argument of $\mathcal R$; $R,j$ are the scalar invariant quantities. Apply $\operatorname{pos}$ first to
\[
 QR-4B                                                            \tag{104.88}
\]
and then to
\[
 R^{[2]}-16H\left((C-j)^{[2]}
       +Dp^{[2]}\lambda^{[2]}(a+M)^{[2]}/(16Q)\right).             \tag{104.89}
\]
The latter retains the original singleton coefficient; no free coefficient is substituted.

### 104.16. Complete scalar normer tests

Define, in order,
\[
\begin{aligned}
 K&=T-2pg,\\
 P_+&=-p^{[2]}QT^{[2]}+2Q(D+p^{[2]})T\lambda
                            +p^{[2]}(D+p^{[2]})\lambda^{[2]},\\
 P_-&=Q^{[2]}T^{[2]}+2p^{[2]}QT\lambda
                  +(DQ+p^{[2]}p^{[2]}+p^{[2]})\lambda^{[2]},\\
 B_0&=-(MP_++DaP_-)/4,\\
 F_1&=2R\Delta B_0-j\lambda H^{[2]}B,\\
 F_2&=4Q\Delta H j^{[2]}-B\bigl(jKH+2R\Delta\bigr).
\end{aligned}                                                     \tag{104.90}
\]
Reject if zero is absent from $F_1$, then reject if zero is absent from $F_2$. No division by $\lambda$ occurs. Finally apply $\operatorname{pos}$ to
\[
 RK\Delta H j+\lambda^{[2]}H^{[2]}Hj^{[2]}/4
               +R^{[2]}\Delta^{[2]}-16\Delta^{[2]}Hj^{[2]}.       \tag{104.91}
\]
If it declares no contradiction, let $\mathcal R(B)=0$.

Equations (104.88), (104.89) and (104.91) are respectively the strict complete-norm trace bound, actual singleton-34 bound and the positive multiple of $t^{-2}-16$. The positivity of $K$ is not separately tested; omitting that necessary condition only weakens this predicate. Every explicit test has been listed; there is no numerical tolerance, iteration stopping heuristic or unprinted oracle.

### 104.17. The finite split recursion

For a box $B=\prod_{k=1}^3[l_k,u_k]_s$, choose the smallest index maximizing
\[
 \frac{u_k-l_k}{w_k}.                                             \tag{104.92}
\]
The ratios are compared exactly as rational numbers. Set $m_k=\lfloor(l_k+u_k)/2\rfloor$. If $l_k<m_k<u_k$, let $B^-$ and $B^+$ replace the chosen coordinate by $[l_k,m_k]_s$ and $[m_k,u_k]_s$, respectively. They are closed and have union $B$. If the midpoint is not interior, designate $B$ unresolved whenever it has not already been rejected.

Define a four-component finite recursion $\mathcal C_n(B)=(v,l,u,h)$, whose components count visited nodes, rejected leaves, unresolved leaves and maximum depth:

- If $\mathcal R(B)=1$, set $\mathcal C_n(B)=(1,1,0,0)$ for every $n\ge0$.
- If $\mathcal R(B)=0$ and either $n=0$ or the midpoint in (104.92) is not interior, set $\mathcal C_n(B)=(1,0,1,0)$.
- Otherwise evaluate the upper child first and then the lower child, writing $\mathcal C_{n-1}(B^\pm)=(v_\pm,l_\pm,u_\pm,h_\pm)$, and set
\[
 \mathcal C_n(B)=
 (1+v_++v_-,\ l_++l_-,\ u_++u_-,\ 1+\max(h_+,h_-)).              \tag{104.93}
\]
This is a finite mathematical definition by induction on $n$, even without any assumption of a closed feasible set or successful termination of an unbounded search. It uses only the rational root, the integer $s$, formulas (104.72)–(104.91), four scalar contractions and the rational tie rule (104.92).

**Lemma 104.9.** Suppose a set of real parameter tuples is contained in a box $B$ and the full interval (104.81), and every tuple obeys the exact real counterparts of all equations, strict inequalities and interval cuts used in §§104.13–104.16. If the unresolved component of $\mathcal C_n(B)$ is zero, that set is empty.

**Proof.** Formulas (104.72)–(104.75) enclose the real operations, by their signed endpoint extrema and integer-square bounds. Every cut is a superset of the hypothesized value. A strict positive expression has a positive member of its enclosure; a required zero belongs to its enclosure. A real quadratic root makes its discriminant nonnegative, including the degenerate linear and constant cases. The common-root linear elimination preserves any root. At each step (104.83), the segment between a root and the newly chosen midpoint is contained in the current interval, so the derivative enclosure and the scalar mean-value theorem retain that root. Undefined division makes no rejection. Hence $\mathcal R(B)=1$ excludes every such tuple. Induction on $n$, using the exact closed union $B=B^-\cup B^+$, proves the assertion. An unresolved leaf would have been counted rather than rejected. $\square$


### 104.18. A finite identity and its original-domain consequence

**Proposition 104.10.** For the integer-grid operations, cuts, root intervals, contractions and tie rule of §§104.12–104.17,
\[
\boxed{\mathcal C_{30}(\mathcal B_s)
=(1186883,\ 593442,\ 0,\ 30).}
\tag{104.94}
\]

**Proof.** Evaluate the finite recursion (104.93) with its rational root (104.76). At each node use the ordered operations (104.72)–(104.91), the four contractions (104.84), and the exact comparison (104.92). The resulting counts are 593441 internal binary nodes and 593442 rejected leaves, with no unresolved leaf and maximal depth 30. Their sum is 1186883. All constants, intermediate rounding rules and finite bounds entering this identity are specified in the preceding definitions; the identity requires no unspecified real oracle or additional input. \(\square\)

**Proof of Theorem 104.1.** A hypothetical original local minimum gives the same common positive-density normer by §§104.1–104.4. The legitimate full-coordinate transformations of §104.5 place it in the normalized chart. The quantitative lemmas in §§104.6–104.9 imply every root and intermediate cut in §104.11. Its actual quotient and phase equation, complete scalar normer, positive trace gap, exact norm and original singleton error give all the real counterparts tested in §§104.13–104.16. Neither sign of \(q\) has been removed. By (104.94), the unresolved component of the complete finite recursion is zero. Lemma 104.9 therefore excludes this point from its root, a contradiction. \(\square\)

The implication concerns positive-subquarter local minima on the full calibrated domain with ranks \((7,6)\), the specified support and equal-polar \(H\) records. It does not give a quarter lower bound for every nonstationary equal-polar pair, or a uniform gap above one quarter. The genuinely unequal-polar part of \((2,1,1,0)\) and the six other rank-\((7,6)\) support patterns
\[
(1,1,1,1),\ (2,2,1,0),\ (2,1,1,1),\ (2,2,2,0),\ (2,2,1,1),\ (2,2,2,1)
\]
remain outside this conclusion, as do other unequal and lower ranks. The calibration reduction in [RT II §72](ARITHMETIC_HOLOGRAPHIC_RT_II.md) can change rank and is not asserted to preserve the local-minimum class here. Thus it does not extend this subclass implication to every leaking channel. The unrestricted global optimum remains in the interval \([\sqrt3-3/2,1/4]\).

## 105. Complementary-polar exclusion from the same principal normer

### 105.1. Original domain and the complementary-polar hypothesis

Retain the original calibrated \(\mathbb C^8\to\mathbb C^4\) channels, fixed correlated encoding, four two-coordinate fibres and unhalved arbitrary-reference error \(F(G,H)\) of (104.1). Suppose \((G,H)\) is a local minimum on the full domain \(\mathcal E^2\), with
\[
\operatorname{rank}G=7,\qquad \operatorname{rank}H=6,
\qquad 0<t=F(G,H)<\tfrac14.
\tag{105.1}
\]
Suppose that the support \(S\) of the full kernel vector of \(G\) has occupancy \((2,1,1,0)\). Label its whole original fibre \(F=\{1,2\}\) and its singleton coordinates \(J=\{3,4\}\); the two singleton partners remain outside \(S\).

Use inner products linear in their second argument and choose the supported \(H\) record basis so that \(h_1=e_1,h_2=e_2\). The additional complementary-polar hypothesis is
\[
|\langle h_1,h_3\rangle|=|\langle h_2,h_4\rangle|=c,
\qquad
|\langle h_2,h_3\rangle|=|\langle h_1,h_4\rangle|=s,
\qquad c,s\ge0,\quad c^2+s^2=1.
\tag{105.2}
\]
This is a restriction on the two polar angles; for \(c\ne s\) they are unequal. No symmetry is imposed on the outside records or on the other Gram.

**Theorem 105.1.** There is no full-domain local minimum satisfying (105.1), the stated support condition and (105.2).

For the proof, [RT III §§95–97](ARITHMETIC_HOLOGRAPHIC_RT_III.md) give
\[
\operatorname{rank}H_S=\operatorname{rank}\mathsf R=2,
\qquad G_S=H_S\odot\overline{\mathsf R},
\qquad \mathsf R\succeq0,
\qquad \mathsf R_{ii}=1,
\qquad \mathsf R\operatorname{diag}(\overline a)H_S=0,
\tag{105.3}
\]
where \(a\) spans the full kernel of \(G\) and all four supported coordinates are nonzero. The same sections give equality of principal and full complete norms and unrestricted principal one-party best responses. RT III §99 gives uniqueness of every principal norming pair, including singular competitors, and positive definiteness of its density. The same original common normer satisfies
\[
W_{ij}=-\frac{\alpha a_i\overline a_j}{2\overline H_{ij}},
\qquad \alpha>0,
\tag{105.4}
\]
on pairs in distinct supported original fibres. These statements concern a local minimum in the full original domain. They do not assert a joint local minimum on a principal or fixed-rank domain.

### 105.2. Phase normalization and endpoints

If \(c=0\) or \(s=0\), an original cross-fibre product entry vanishes and its matrix-unit error is \(1/2\), contradicting (105.1). Thus \(c,s>0\). Reciprocal diagonal phase changes of the full Grams preserve every product coefficient, positivity, ranks and the original fibre blocks. Together with a record-space basis choice they put the supported records in the form
\[
h_3=(cv,s\overline v),\qquad
h_4=(s\overline v,cv),\qquad |v|=1.
\tag{105.5}
\]
Indeed, let \(\theta_{11},\theta_{12},\theta_{21},\theta_{22}\) be the phases of the four entries of \(H_{FJ}\), with the column labels referring to 3 and 4. Choose \(\theta\) such that
\[
4\theta=\theta_{11}+\theta_{22}-\theta_{12}-\theta_{21}
\pmod {2\pi}.
\]
With the convention \(H'_{ij}=e^{-i\phi_i}H_{ij}e^{i\phi_j}\), the choices
\[
\phi_1=0,\quad \phi_3=\theta-\theta_{11},\quad
\phi_4=-\theta-\theta_{12},\quad
\phi_2=2\theta-\theta_{11}+\theta_{21}
\]
make the diagonal cross phases \(\theta\) and the off-diagonal cross phases \(-\theta\). Apply the reciprocal phases to \(G\) on the same eight coordinates, and take \(v=e^{i\theta}\). This normalization does not make \(G\) or an outside record real.

Write
\[
v^2=p+iq,\qquad p,q\in\mathbb R,\quad p^2+q^2=1,
\qquad h=H_{34}=2cs p\in\mathbb R.
\tag{105.6}
\]
If \(c=s\), both singleton \(H\) records are unbiased and RT III §102 excludes the case. If \(q=0\), the cross-ratio phase is real, since \(v^4=1\); thus \(H_S\) admits a real diagonal phase gauge, excluded by RT III §101. If \(p=0\), the entry \(H_{34}\) vanishes and again gives matrix-unit error \(1/2\). It remains to consider
\[
c,s>0,\qquad c^2-s^2\ne0,\qquad pq\ne0.
\tag{105.7}
\]

### 105.3. Symmetry of the same principal norming pair

Let \(\Pi\) swap 1 with 2 and 3 with 4. Formula (105.5) gives \(\Pi H_S\Pi=H_S\), since interchanging \(e_1,e_2\) implements that permutation on the records. Also \(\Pi T_S\Pi=T_S\). The principal density domain, consisting of one unrestricted \(F\) block and two scalar singleton blocks, is invariant under \(\Pi\).

The reflected principal Gram \(\Pi G_S\Pi\) and its midpoint with \(G_S\) are feasible. The fixed-\(H_S\) principal objective is convex and invariant under \(\Pi\). The full-domain compression and completion result makes \(G_S\) a global principal one-party best response, so all three Grams have minimum value \(t\). Any norming pair at the midpoint norms both endpoints: its endpoint objectives are at most \(t\), while their average is \(t\). Uniqueness of every principal norming pair at the original coefficient forces the midpoint pair to be the same original \((\rho,W)\). Reflecting it gives another midpoint normer. Therefore
\[
\Pi\rho\Pi=\rho,\qquad \Pi W\Pi=W.
\tag{105.8}
\]
This argument neither assumes symmetry of the full physical \(H\) nor replaces the physical pair by an average of the same rank. The permutation extends to the eight original coordinates by also exchanging the singleton partners and leaving the fourth fibre fixed. That extension preserves the target and original fibre partition; invariance of outside data is not required.

Since \(H_{13}=H_{24}\) and \(H_{14}=H_{23}\), (105.4) and (105.8) imply
\[
a_1\overline a_3=a_2\overline a_4,
\qquad a_1\overline a_4=a_2\overline a_3.
\]
All factors are nonzero. Dividing the two equations gives \(a_4=\sigma a_3\) for some \(\sigma\in\{1,-1\}\), and either equation gives \(a_2=\sigma a_1\). Thus
\[
a_S=(a,\sigma a,b,\sigma b),\qquad
\sigma\in\{1,-1\},\qquad a,b\ne0.
\tag{105.9}
\]
Both parity branches are retained. The ratio \(r=a/b\) may be genuinely complex.

### 105.4. Original unit diagonals force quotient symmetry

Use the orthonormal parity basis \(F_+,F_-,J_+,J_-\), where each pair is the sum and difference of its original coordinates divided by \(\sqrt2\). Put
\[
h_+=cv+s\overline v,
\qquad h_-=cv-s\overline v.
\tag{105.10}
\]
In parity sector \(\tau\in\{1,-1\}\), the \(H_S\) block has rank one and range vector \((1,\overline{h_\tau})\). From (105.3) and the two rank equalities,
\[
\ker\mathsf R
=\operatorname{range}\bigl(\operatorname{diag}(\overline a)H_S\bigr).
\tag{105.11}
\]
Multiplication by \(\operatorname{diag}(\overline a)\) sends parity \(\tau\) to \(\sigma\tau\). Taking the orthogonal complement in (105.11) shows that \(\operatorname{range}\mathsf R\) has basis
\[
w_+=(-h_\sigma/r,0,1,0)^T,
\qquad
w_-=(0,-h_{-\sigma}/r,0,1)^T.
\tag{105.12}
\]
Consequently
\[
\mathsf R=(w_+,w_-)M(w_+,w_-)^*,\qquad M\succ0,
\]
for a two-by-two Hermitian matrix \(M\). The two original \(J\) diagonal entries equal one, so \(\operatorname{Tr}M=2\) and \(\operatorname{Re}M_{12}=0\). Equality of the original \(F\) diagonal entries similarly gives
\[
\operatorname{Re}\bigl(M_{12}h_\sigma\overline{h_{-\sigma}}\bigr)=0.
\tag{105.13}
\]
But \(\operatorname{Im}(h_+\overline{h_-})=-2csq\ne0\). Since \(M_{12}\) is purely imaginary, (105.13) forces \(M_{12}=0\). Hence
\[
M=\operatorname{diag}(1+z,1-z),\qquad -1<z<1,
\qquad |r|^2=1+\sigma hz>0.
\tag{105.14}
\]
The last identity is the original \(F\) diagonal normalization. It follows that \(\mathsf R\), and therefore the actual \(G_S=H_S\odot\overline{\mathsf R}\), commute with \(\Pi\). This is derived from the original unit diagonals and nonreal phase, rather than imposed on an averaged Gram.

In the original four supported coordinates the same formulas give
\[
\mathsf R_{13}=-\frac{cv+\sigma s\overline v z}{r},\qquad
\mathsf R_{14}=-\frac{\sigma s\overline v+cvz}{r},\qquad
\mathsf R_{34}=z,
\tag{105.15}
\]
and hence
\[
G_{13}=-\frac{c^2+\sigma cs v^2z}{\overline r},\qquad
G_{14}=-\frac{\sigma s^2+cs\overline v^2z}{\overline r}.
\tag{105.16}
\]
The other two cross entries follow by \(\Pi\) symmetry. Reality of \(z\) is a consequence of the preceding diagonal constraints.

### 105.5. Antisymmetric-mode contradiction

Let \(L=(T-G\odot H)_S\), \(E=L_{FJ}\) and \(C=W_{FJ}\). Both \(E\) and \(C\) commute with the two-coordinate swap. The complete-norm complementary equations for the same original \((\rho,W)\) imply
\[
EC^*=\tfrac t2\rho_F,
\tag{105.17}
\]
so \(EC^*\) is Hermitian. For clarity, the principal dual is
\[
\min\{u:Z\succeq0,\ Z-2L\succeq0,
\ Z_{FF}\preceq uI_2,\ Z_{33},Z_{44}\le u\}.
\]
Strict feasibility gives attained primal and dual optima. Positive definiteness of \(\rho_F\) gives \(Z_{FF}=tI_2\). The products \((Z-2L)W=0\) and \(Z(\rho-W)=0\) imply \(2LW=Z\rho\); its \(F\) block is (105.17), since \(L_{FF}=0\) and \(\rho_{FJ}=0\). This is the finite-dimensional semidefinite norm framework of J. Watrous, [Semidefinite Programs for Completely Bounded Norms](https://theoryofcomputing.org/articles/v005a011/), Theory of Computing 5 (2009), 217–238, applied to the original principal density domain.

The antisymmetric eigenvalues are \(e_-=E_{13}-E_{14}\) and \(c_-=C_{13}-C_{14}\). The target cross block is \(J_2/2\), whose antisymmetric eigenvalue is zero. Equations (105.4) and (105.16) give
\[
\begin{aligned}
e_-&=\frac{c^3v-\sigma s^3\overline v
+z(\sigma c^2s v^3-cs^2\overline v^3)}{\overline r},\\
c_-&=-\frac{\alpha r|b|^2}{2}
\left(\frac vc-\frac{\sigma\overline v}s\right).
\end{aligned}
\tag{105.18}
\]
Using \(c^2+s^2=1\) and \(v^2=p+iq\), direct multiplication yields
\[
\begin{aligned}
\operatorname{Im}(e_-\overline{c_-})
&=\frac{\alpha|b|^2}{2}(c^2-s^2)q
\left(\frac\sigma{cs}+2pz\right)\\
&=\frac{\alpha\sigma|a|^2}{2cs}(c^2-s^2)q\ne0.
\end{aligned}
\tag{105.19}
\]
For the first equality, multiply the numerator of \(e_-\) by \(\overline v/c-\sigma v/s\). Its imaginary part is
\[
-(c^2-s^2)q\left(\frac\sigma{cs}+2pz\right).
\]
The negative common-stress factor in \(c_-\) gives the first line of (105.19). The second line is precisely \(\sigma+hz=\sigma|r|^2\), from (105.14). Every final factor is nonzero by (105.4), (105.7) and (105.9), for both values of \(\sigma\) and both signs of \(q\). Yet (105.17), diagonalized in the parity basis, requires \(e_-\overline{c_-}\) to be real. This contradiction proves Theorem 105.1. \(\square\)

The conclusion is restricted to the stated full-domain local-minimum rank and support class. It gives neither a uniform gap nor a quarter bound for every nonstationary complementary-polar pair. Together with Theorem 104.1 it excludes equal and complementary polar angles in that class; general unequal, noncomplementary polar angles and the other remaining rank/support classes are unresolved. The calibration reduction in [RT II §72](ARITHMETIC_HOLOGRAPHIC_RT_II.md) does not preserve the ranks or local-minimum property used here, so it does not extend this exclusion to arbitrary leaking channels. The unrestricted global optimum remains between \(\sqrt3-3/2\) and \(1/4\).

## 106. Exact product-preserving rank saturation and global rank descent

### 106.1. Original domain and a kernel-support path

Retain the original calibrated \(\mathbb C^8\to\mathbb C^4\) channels, the four two-coordinate fibres, fixed correlated encoding and unhalved arbitrary-reference error \(F\) of (104.1). Thus
\[
\mathcal E=\{G\in\operatorname{Herm}(8):G\succeq0,\ G_{ff}=I_2\},
\qquad
F(G,H)=\max_{(\rho,W)\in\mathcal C}
                 2\operatorname{Tr}[(T-G\odot H)W],
\tag{106.1}
\]
where \(\mathcal C\) is the original fibre-block density and witness domain. Local minimality always refers to the full domain \(\mathcal E^2\). No external rank constraint is imposed.

For a coordinate set \(S\subseteq\{1,\ldots,8\}\), put \(O=S^c\), \(n=|S|\) and \(o=|O|\). Vectors in \(\mathbb C^S\) are extended by zero on \(O\). Suppose \(G,H\in\mathcal E\) and
\[
\ker G\subseteq\mathbb C^S,
\qquad h=\operatorname{rank}H_S.
\tag{106.2}
\]
The inclusion concerns the entire kernel, including when it has dimension greater than one. In the \(S,O\) partition define
\[
B_H=\begin{pmatrix}H_S&0\\0&I_O\end{pmatrix},\qquad
D_{ij}=\begin{cases}
G_{ij},&i\ne j\text{ and }\{i,j\}\cap O\ne\varnothing,\\
0,&\text{otherwise},
\end{cases}
\tag{106.3}
\]
and, for \(\tau\ge0\), set
\[
G_\tau=G+\tau D,\qquad
H_\tau=\frac{H+\tau B_H}{1+\tau}.
\tag{106.4}
\]

**Theorem 106.1.** Under (106.2), every sufficiently small \(\tau>0\) gives \(G_\tau,H_\tau\in\mathcal E\) with
\[
\begin{aligned}
(G_\tau)_S&=G_S,&(H_\tau)_S&=H_S,\\
G_\tau\odot H_\tau&=G\odot H,&
\ker G_\tau&=\ker G,\\
\operatorname{rank}H_\tau&=h+o.&
\end{aligned}
\tag{106.5}
\]
The pair converges to \((G,H)\) as \(\tau\downarrow0\). If \((G,H)\) is a full-domain local minimum, every sufficiently small such pair is a full-domain local minimum of exactly the same value.

**Proof.** The matrix \(B_H\) is positive semidefinite. Its original fibre blocks are identities even if a fibre is split between \(S\) and \(O\): the cross entry is zero, as required. Thus \(H_\tau\in\mathcal E\) for every \(\tau\ge0\). The Hermitian matrix \(D\) has zero entire original fibre blocks.

For \(x\in\ker G\), condition (106.2) gives \(x_O=0\). Its \(S\) coordinates in \(Dx\) vanish because \(D_{SS}=0\); on \(O\),
\[
(Dx)_i=\sum_{j\in S}G_{ij}x_j=(Gx)_i=0.
\tag{106.6}
\]
Consequently \(D\ker G=0\). Hermiticity makes \(K=(\ker G)^\perp\) invariant under both \(G\) and \(D\). Let \(\eta>0\) be the smallest eigenvalue of \(G|_K\). If \(D\ne0\), then
\[
0\le\tau<\frac{\eta}{\|D\|_{\rm op}}
\quad\Longrightarrow\quad
G_\tau|_K\succ0,
\qquad \ker G_\tau=\ker G.
\tag{106.7}
\]
If \(D=0\), the same conclusion holds for every \(\tau\ge0\). This proves feasibility and the first-kernel assertion near zero.

For positive semidefinite matrices, the kernel of a positive linear combination is the intersection of the kernels, since a zero quadratic form makes each nonnegative summand vanish. Any vector in \(\ker H_S\), extended by zero, lies in \(\ker H\) by the same zero-quadratic-form argument. Therefore for every \(\tau>0\),
\[
\ker H_\tau=\ker H\cap\ker B_H
           =\ker H_S\oplus\{0\}_O,
\qquad
\operatorname{rank}H_\tau=h+o.
\tag{106.8}
\]
No invertibility assumption on \(H_{OO}\) or on a principal Gram is needed.

Both principal blocks on \(S\) and every diagonal entry are unchanged. For \(i\ne j\) with an endpoint in \(O\),
\[
(G_\tau)_{ij}=(1+\tau)G_{ij},\qquad
(H_\tau)_{ij}=\frac{H_{ij}}{1+\tau}.
\tag{106.9}
\]
Their product is unchanged, including original partner zeros. Hence the entire eight-coordinate coefficient \(T-G\odot H\), every complete-norm witness objective and the exact error are unchanged. This is stronger than equality of a principal or uniform-input bound.

The paths (106.4) are continuous at zero. If \((G,H)\) is a local minimum of value \(t\), choose a relatively open neighbourhood \(U\subseteq\mathcal E^2\) on which \(F\ge t\). Every sufficiently small constructed pair lies in \(U\) and has value \(t\). A relatively open neighbourhood of that pair contained in \(U\) witnesses its own full-domain local minimality. This proves the theorem. \(\square\)

### 106.2. The same complete common-witness subset

Suppose now that \((G,H)\) is a full-domain local minimum, \(\operatorname{rank}G=7\), \(0<t=F(G,H)<1/2\), and \(S\) is exactly the support of a fixed vector \(a\) spanning \(\ker G\). Let \(\mathcal A(G,H)\) be the norming pairs in (106.1), and define the complete canonical common-witness subset by
\[
\begin{aligned}
\mathcal A_0(G,H)
 &=\{(\rho,W)\in\mathcal A(G,H):
             b_{G,H}(W;Q,R)\ge0\text{ for every }Q,R\in\mathcal E\},\\
b_{G,H}(W;Q,R)
 &=-2\operatorname{Tr}
       [((Q-G)\odot H+G\odot(R-H))W].
\end{aligned}
\tag{106.10}
\]
[RT III §§92,95](ARITHMETIC_HOLOGRAPHIC_RT_III.md) make this a nonempty compact convex subset. Its definition retains one and the same norming pair for both first-order inequalities.

**Corollary 106.2.** For every sufficiently small \(\tau>0\) in Theorem 106.1,
\[
\mathcal A_0(G_\tau,H_\tau)=\mathcal A_0(G,H).
\tag{106.11}
\]
For each such common pair, its first stress \(\alpha aa^*\), \(\alpha>0\), and supported positive correlation quotient from RT III §95 can be retained unchanged.

**Proof.** RT III Lemma 96.1 says that every canonical common density and witness is supported on \(S\). For such a witness the unchanged principal blocks give
\[
\overline{H_\tau}\odot W=\overline H\odot W,
\qquad
\overline{G_\tau}\odot W=\overline G\odot W.
\tag{106.12}
\]
In (106.10), the terms depending on \(Q,R\) are consequently unchanged, and the constant term is unchanged by the full product identity. Thus \(b_{G_\tau,H_\tau}=b_{G,H}\) for this witness and every original feasible \(Q,R\). The full norming sets \(\mathcal A\) are identical because their complete coefficients agree. This proves one inclusion in (106.11).

The new pair is itself a full-domain local minimum, with the same rank-seven kernel and value. Lemma 96.1 therefore supports all its common pairs on the same \(S\). Reversing the preceding argument proves the other inclusion.

For completeness, the complementary stresses associated with one fixed common pair have the form
\[
\begin{aligned}
P_A&=\operatorname{blockdiag}(\Lambda_A)-2\overline H\odot W
      =\alpha aa^*,\qquad P_AG=0,\\
P_B&=\operatorname{blockdiag}(\Lambda_B)-2\overline G\odot W
      \succeq0,\qquad P_BH=0.
\end{aligned}
\tag{106.13}
\]
Both are supported on \(S\), by RT III §95. Equations (106.12) leave their displayed matrices unchanged with the same multipliers. The first still annihilates \(G_\tau\) by equality of kernels. The second annihilates both \(H\) and \(B_H\): support on \(S\) reduces the latter assertion to \((P_B)_{SS}H_S=0\). It therefore annihilates \(H_\tau\). The same supported diagonal congruence defining the quotient retains that quotient and \(\alpha\). \(\square\)

### 106.3. Removing the opposite full-rank restriction on four-coordinate obstructions

**Corollary 106.3.** Suppose \((G,H)\) is a full-domain calibrated local minimum with \(\operatorname{rank}G=7\), \(0<F(G,H)<1/4\), and kernel support occupancy \((2,1,1,0)\). Impose no assumption on the full rank of \(H\). Then
\[
\operatorname{rank}H_S=\operatorname{rank}\mathsf R=2,
\tag{106.14}
\]
and arbitrarily close full-domain local minima have ranks exactly \((7,6)\), with the same principal Grams, kernel vector, complete error coefficient and canonical common-witness subset. In particular this class has no member for which either principal Gram admits the real diagonal gauge of RT III §101, both supported singleton \(H\) records are unbiased as in RT III §102, the equal-polar hypothesis (104.3) holds, or the complementary-polar hypothesis (105.2) holds.

**Proof.** Put \(h=\operatorname{rank}H_S\) and \(r=\operatorname{rank}\mathsf R\). The whole original fibre in \(S\) gives \(h\ge2\). RT III Lemma 95.2 gives
\[
\operatorname{rank}G_S=3,
\qquad h+r\le4,
\qquad 3\le hr.
\tag{106.15}
\]
The only positive integer possibilities are \((h,r)=(2,2)\) and \((3,1)\). RT III Theorem 97.3 excludes the rank-one quotient for this support, so (106.14) follows. Here \(o=4\); Theorem 106.1 gives opposite rank \(h+o=6\) while retaining first rank seven. Corollary 106.2 retains exactly the same common pairs and quotient.

Each additional condition in the statement depends only on the unchanged supported data. Apply the corresponding rank-\((7,6)\) obstruction, respectively RT III §§101–102 or Theorems 104.1 and 105.1, to any sufficiently close constructed pair. This contradicts its full-domain local minimality. The argument constructs a point satisfying the original rank assumptions of those theorems; it does not read their statements with weakened assumptions. \(\square\)

### 106.4. A finite endpoint with strictly smaller first rank

**Theorem 106.4.** Under (106.2), suppose \(D\ne0\). There is a finite \(\tau_*>0\) such that \(G_\tau\succeq0\) exactly for \(0\le\tau\le\tau_*\). At the endpoint the original full calibrated Grams satisfy
\[
\begin{aligned}
G_{\tau_*}\odot H_{\tau_*}&=G\odot H,\\
\operatorname{rank}G_{\tau_*}&<\operatorname{rank}G,\\
\operatorname{rank}H_{\tau_*}&=h+o.
\end{aligned}
\tag{106.16}
\]
If the original pair is a global minimum, so is the endpoint. No endpoint local-minimum assertion is made for an arbitrary local minimum.

**Proof.** For \(|O|=1\), the first-Gram endpoint factorization is the single-record projection construction in the proof of [B. Lovitz, *On decomposable correlation matrices*, Theorem 1, equations (9)–(13), arXiv:1812.01449v1](https://arxiv.org/pdf/1812.01449v1); see the [source note](../../../Library/QuantumChannels/lovitz2019decomposable.md). The argument below treats all outside coordinates simultaneously and controls the opposite Gram's rank while preserving the original fibre constraints and exact product.

Theorem 106.1 gives a positive interval of feasible \(\tau\) and \(D\ker G=0\). The feasible set of \(\tau\ge0\) is closed and convex. Since \(D\) is Hermitian, nonzero and has trace zero, it has a negative eigenvalue. A corresponding eigenvector \(x\) lies in \(K=(\ker G)^\perp\), because \(D\) annihilates \(\ker G\). Hence
\[
x^*(G+\tau D)x=x^*Gx+\tau x^*Dx<0
\quad\text{for every sufficiently large }\tau.
\tag{106.17}
\]
The feasible interval is bounded and has a positive finite maximum \(\tau_*\).

If \((G+\tau_*D)|_K\) were positive definite, its positive least eigenvalue would permit a further increase of \(\tau\), contradicting maximality. Thus a new vector of \(K\) enters the kernel. The old kernel is still annihilated, proving the strict rank decrease. Equations (106.8)–(106.9) hold for every finite positive feasible \(\tau\), so they prove the other assertions in (106.16). Since the complete objective is unchanged, a global minimum stays global at the endpoint. The near-zero neighbourhood argument of Theorem 106.1 is not invoked at this distant point. \(\square\)

If \(O\ne\varnothing\) and \(F(G,H)<1/2\), then the hypothesis \(D\ne0\) is automatic. Indeed choose \(i\in O\) and \(j\) in any different original fibre. If \(D=0\), then \(G_{ij}=0\), whereas the original matrix-unit test gives
\[
\frac12=|T_{ij}-G_{ij}H_{ij}|\le F(G,H)<\frac12,
\tag{106.18}
\]
a contradiction. This uses an actual original-channel matrix unit and involves no entrywise division.

### 106.5. Residual ranks for a hypothetical subquarter global optimum

**Theorem 106.5.** Suppose the minimum of \(F\) on \(\mathcal E^2\) has value \(0<t_*<1/4\). It has a minimizer in at least one of the following classes:

1. Both full Gram ranks are at most six.
2. One full Gram has rank seven and an everywhere-nonzero spanning kernel vector, while the opposite full rank is at most five.

More precisely, every rank-seven global minimizer whose kernel has a proper coordinate support has an equal-value competitor with both ranks at most six and exactly the same complete product.

**Proof.** The domain is compact: its matrices are positive semidefinite with trace eight and fixed fibre blocks. The objective (106.1) is continuous. Thus the minimum is attained. Every global minimum is a full-domain local minimum. At a positive-subhalf local minimum, RT III Theorem 92.1 gives nonzero positive complementary stresses on both sides. A positive definite Gram would force its complementary stress to vanish, so both Gram ranks are at most seven.

Suppose one rank is seven and interchange the parties if necessary so that it is \(G\). Let \(S\) be the exact support of its kernel vector, and put \(n=|S|\), \(h=\operatorname{rank}H_S\). For any canonical common witness, RT III §§95,97 give a supported quotient of rank \(r\) with
\[
h+r\le n,\qquad
r\le8-\operatorname{rank}H,\qquad r\ge2.
\tag{106.19}
\]
The last assertion uses the complete rank-one-quotient exclusion: RT III Theorem 97.3 allows only a three-singleton support in that case and forces its error strictly above \(1/4\).

If \(S\) is proper, (106.18) makes \(D\ne0\). The endpoint of Theorem 106.4 has the same full coefficient and global value, while
\[
\operatorname{rank}G_{\tau_*}\le6,
\qquad
\operatorname{rank}H_{\tau_*}=h+8-n\le6.
\tag{106.20}
\]
This proves the precise assertion and gives the first alternative.

If \(S\) is all eight coordinates, (106.19) gives \(\operatorname{rank}H\le6\). RT III Theorem 95.1 excludes opposite rank six for such a positive-subhalf full-domain local minimum. Hence \(\operatorname{rank}H\le5\), giving the second alternative. If neither Gram initially had rank seven, the first alternative already held. \(\square\)

This is an existence alternative for a minimizer of the hypothetical value. Another minimizer with proper-support rank seven can coexist with its reduced-rank endpoint. The proof uses an explicit constant-product feasible path, not an assertion that a convex-norm minimizer must be an extreme Gram point.

**Corollary 106.6.** For the original unrestricted one-product channel problem with the fixed correlated encoding and unhalved diamond error, a hypothetical optimum below \(1/4\) has a calibrated representative in one of the two classes of Theorem 106.5.

**Proof.** The exact physical calibration theorem in [RT II §72](ARITHMETIC_HOLOGRAPHIC_RT_II.md#72-exact-physical-calibration-reduction-for-collapsed-fibre-channels) applies to the present target \(T\) with four fibres of size two and one shared branch of weight one. It replaces arbitrary local CPTP maps, including population leakage, by calibrated maps without increasing the full arbitrary-reference error or adding a shared branch. Conversely every \(G,H\in\mathcal E\) realizes calibrated local channels. Hence the unrestricted physical infimum equals the attained minimum (106.1). The established lower bound \(\sqrt3-3/2>0\) makes a hypothetical subquarter value positive, and Theorem 106.5 supplies the stated representative. \(\square\)

The representative conclusion does not preserve the ranks or local minimality of a given leaking pair. The local transfer in Corollary 106.3 takes place wholly inside the calibrated domain. Neither residual class in Theorem 106.5 is excluded here, and the unrestricted global interval remains \([\sqrt3-3/2,1/4]\). General unequal noncomplementary polar angles and the remaining rank/support cases are unresolved.

## 107. Sharp original-channel bound from one cyclic correct-output Gram

### 107.1. Original-channel hypotheses and sharp statement

Index the original logical coordinates by \(j\in\mathbb Z/8\mathbb Z\), with fibres \(\{f,f+4\}\), \(f=0,1,2,3\). Thus \(j=f+4i\) labels the original coordinate \(|f,i\rangle\). Retain the fixed correlated encodings \(V_{\rm in}|j\rangle=|j\rangle\otimes|j\rangle\) and \(V_{\rm out}|f\rangle=|f\rangle\otimes|f\rangle\), and write \(J_{\rm in},J_{\rm out}\) for the induced channels. The target \(\mathcal F\) has coefficients \(T_{jj}=1\), \(T_{j,j+4}=0\), and \(T_{jk}=1/2\) for different fibres.

For arbitrary original CPTP maps \(A,B:\mathbb C^8\to\mathbb C^4\), choose Stinespring isometries and define their correct-output records by
\[
 a_j=(\langle j\bmod4|\otimes I)V_A|j\rangle,
 \qquad b_j=(\langle j\bmod4|\otimes I)V_B|j\rangle.
 \tag{107.1}
\]
Their forward Grams \(G,H\), using inner products conjugate-linear in the first argument, are independent of Stinespring environment isometries. Their original fibre blocks satisfy \(0\le G_{ff},H_{ff}\le I_2\). The error is the original unhalved, arbitrary-reference diamond norm
\[
 \delta(A,B)=\|(A\otimes B)\circ J_{\rm in}
                       -J_{\rm out}\circ\mathcal F\|_\diamond.
 \tag{107.2}
\]

**Theorem 107.1.** Suppose both correct-output Grams are circulant in this same original labeling:
\(G_{j+1,k+1}=G_{jk}\) and \(H_{j+1,k+1}=H_{jk}\), with indices modulo eight. Then
\[
 \delta(A,B)\ge\sqrt2-1>\tfrac14.
 \tag{107.3}
\]
The bound is sharp, with an attaining calibrated physical pair of local Kraus ranks \((3,3)\). The infimum is also \(\sqrt2-1\) in each calibrated simultaneous-cyclic exact-rank class \((7,4)\) and \((7,5)\) with full-support first kernel.

The simultaneous-cyclic hypothesis allows complex entries and arbitrary original output leakage. It is a substantive hypothesis on both correct-output Grams, rather than a phase convention. The proof occupies §§107.2–107.6. Corollary 107.2 below weakens this to a cyclic hypothesis on just one Gram, allowing the other original channel to be arbitrary.

### 107.2. Fourier coordinates and the original complete norm

**Proof of Theorem 107.1.** First assume the pair is calibrated, so its fibre blocks are \(I_2\). Put \(\zeta=\exp(\pi i/4)\), and define
\[
 (C_k)_{ij}=\zeta^{k(j-i)},\qquad P_k=C_k/8,
 \qquad k\in\mathbb Z/8\mathbb Z.
 \tag{107.4}
\]
The \(P_k\) are mutually orthogonal rank-one projections summing to \(I\). A positive semidefinite Hermitian circulant matrix has a unique expansion in the \(C_k\) with nonnegative real coefficients. Calibration is therefore equivalent to
\[
 G=\sum_k g_kC_k,\qquad g_k\ge0,\qquad
 \sum_{k\ {\rm even}}g_k=\sum_{k\ {\rm odd}}g_k=\tfrac12.
 \tag{107.5}
\]
Indeed the two sums are equivalent to \(G_{jj}=1\) and \(G_{j,j+4}=0\). Write \(H\) similarly with coefficients \(h_k\). Since \(C_k\odot C_l=C_{k+l}\), the coefficients of \(K=G\odot H\) are the cyclic convolution \(c=g*h\). Its even and odd coefficient sums are each \(1/2\). The target coefficients are
\[
 (t_0,\ldots,t_7)
  =(\tfrac12,\tfrac18,0,\tfrac18,0,\tfrac18,0,\tfrac18).
 \tag{107.6}
\]
Thus \(L=T-K\) has eigenvalues \(\ell_k=8(t_k-c_k)\), with eigenvalue sum zero separately in each parity sector.

For calibrated original Grams, the adaptive complete-norm theorem of [RT III §91](ARITHMETIC_HOLOGRAPHIC_RT_III.md#91-adaptive-original-channel-witnesses-and-an-obstruction-to-all-two-fibre-tests) gives
\[
 F(G,H)=\delta(A,B)
 =\max\{2\operatorname{Tr}(LW):
    \rho=\bigoplus_f\rho_f\ge0,\ \operatorname{Tr}\rho=1,
    \ 0\le W\le\rho\}.
 \tag{107.7}
\]
The forward-Gram convention makes the actual coefficient map use \(L^{\mathsf T}\). For a pure reference/input state, its error output is \(V L^{\mathsf T}V^*\), where \(V^*V\) is a fibre-block density. With \(\rho=(V^*V)^{\mathsf T}\), its trace norm is \(\|\sqrt\rho L\sqrt\rho\|_1\). Every such density is realizable. The zero fibre blocks of \(L\) make this norm twice the positive-part trace. Convexity and Jordan decomposition handle mixed and Hermitian inputs, while Hermitian block dilation handles arbitrary operator inputs. Hence (107.7) has the original complete, unhalved normalization.

Let \(J\) send \(j\) to \(j+4\). The densities \(\rho_{\rm even}=(I+J)/8\) and \(\rho_{\rm odd}=(I-J)/8\) are feasible, with eigenvalue \(1/4\) on their selected parity. Taking \(W\) to be one quarter of the positive spectral projection of \(L\) within that parity gives respectively
\[
 \begin{aligned}
 E&=\tfrac14\sum_{k\ {\rm even}}|\ell_k|
     =2\sum_{k\ {\rm even}}|t_k-c_k|,\\
 O&=\tfrac14\sum_{k\ {\rm odd}}|\ell_k|
     =2\sum_{k\ {\rm odd}}|t_k-c_k|.
 \end{aligned}
 \tag{107.8}
\]
For the matching upper bound put \(Z=|L|\). Then \(Z\ge\pm L\), and each original fibre block of \(Z\) has the form \(\left(\begin{smallmatrix}d&b\\b&d\end{smallmatrix}\right)\), with eigenvalues \(E,O\). Thus \(Z_{ff}\le\max(E,O)I_2\), giving a feasible original complete-norm dual majorant. Equivalently, the positive coefficient matrices \(Z\pm L\) give completely positive majorants whose fibre-block bound controls every reference input and its operator-input dilation. Consequently
\[
 F(G,H)=\max\{E,O\}.
 \tag{107.9}
\]
The two densities are realized by the no-reference unit vectors \(8^{-1/2}\sum_{f=0}^3(|f\rangle\pm|f+4\rangle)\). The dual proves that reference systems cannot improve (107.9). This assertion concerns the calibrated pair; the leaking case below uses the tagged-reference bound of RT III §91.

Fourier diagonalization and positive/negative spectral majorants for circulant Schur maps are established techniques; see Regula, Takagi and Gu, *Operational applications of the diamond norm and related measures in quantifying the non-physicality of quantum maps*, equations (70)–(74), [DOI:10.22331/q-2021-08-09-522](https://doi.org/10.22331/q-2021-08-09-522), and the [source note](../../../Library/QuantumChannels/regula2021operational.md). Their scalar Schur-map normalization differs from (107.7); the original two-coordinate fibre normalization and the matching witnesses above are retained here.

### 107.3. The sharp parity-convolution inequality

Introduce four probability distributions on \(\mathbb Z/4\mathbb Z\):
\[
 p_i=2g_{2i},\quad q_i=2g_{2i+1},\quad
 r_i=2h_{2i},\quad s_i=2h_{2i+1},
 \tag{107.10}
\]
and put
\[
 A=\sum_i p_i r_{-i},\qquad
 B=\sum_i q_i s_{-i-1}.
 \tag{107.11}
\]
Then \(c_0=(A+B)/4\). All other even target coefficients vanish, and both even total masses are \(1/2\). It follows that
\[
 E=2-A-B.
 \tag{107.12}
\]
If \(E\ge1/2\), (107.3) is immediate. Suppose \(0\le E<1/2\). Since \(A,B\le1\), both exceed \(1/2\).

For two probability distributions \(x,y\) with inner product \(a>1/2\), each maximum \(m=\max x\), \(n=\max y\) is at least \(a\), and hence unique. Their peaks have the same index. Otherwise, at the peak index \(i\) of \(x\) one has \(y_i\le1-n\), so
\[
 a\le m(1-n)+(1-m)n
   =\tfrac12-2(m-\tfrac12)(n-\tfrac12)<\tfrac12,
 \tag{107.13}
\]
a contradiction. At the common peak the remaining inner product is at most \((1-m)(1-n)\). Therefore
\[
 a\le mn+(1-m)(1-n),\qquad
 m+n\ge1+\sqrt{2a-1}.
 \tag{107.14}
\]
For the second inequality, \(2m-1\) and \(2n-1\) are nonnegative with product at least \(2a-1\), and their arithmetic mean is \(m+n-1\).

Apply this observation to \(p_i,r_{-i}\) and to \(q_i,s_{-i-1}\). There are unique peak indices \(u,v\): the peaks of \(p,r,q,s\) occur at \(u,-u,v,-v-1\), respectively. Writing their maxima as \(m_p,m_r,m_q,m_s\), one obtains
\[
 m_p+m_r\ge1+\sqrt{2A-1},\qquad
 m_q+m_s\ge1+\sqrt{2B-1}.
 \tag{107.15}
\]
The odd coefficients satisfy
\[
 c_{2j+1}=\tfrac14[(p*s)_j+(q*r)_j].
 \tag{107.16}
\]
The two peak contributions occur at \(j_1=u-v-1\) and \(j_2=v-u\). These are distinct modulo four: equality would give \(2(u-v)=1\pmod4\). For \(S=\{j_1,j_2\}\),
\[
 \sum_{j\in S}c_{2j+1}
       \ge\tfrac14(m_p m_s+m_q m_r).
 \tag{107.17}
\]
The odd target has total mass \(1/2\) and mass \(1/4\) on these two indices. Equal total masses imply that the sum of absolute differences is at least twice the signed excess on any subset. Equations (107.8) and (107.17), followed by \(xy\ge x+y-1\) for \(x,y\in[0,1]\), therefore give
\[
 \begin{aligned}
 O&\ge m_p m_s+m_q m_r-1\\
  &\ge m_p+m_s+m_q+m_r-3\\
  &\ge\sqrt{2A-1}+\sqrt{2B-1}-1.
 \end{aligned}
 \tag{107.18}
\]
Put \(X=2A-1\), \(Y=2B-1\). Both lie in \((0,1]\), and \(X+Y=2-2E\). Since \((1-X)(1-Y)\ge0\), one has \(XY\ge X+Y-1\). Squaring nonnegative sides gives
\[
 \sqrt X+\sqrt Y\ge1+\sqrt{X+Y-1},\qquad
 O\ge\sqrt{1-2E}.
 \tag{107.19}
\]
All roots are defined in this branch, including \(E=0\). The minimum of \(\max(E,\sqrt{1-2E})\) on \([0,1/2]\) is its intersection value \(\sqrt2-1\). Equivalently, \(E<\sqrt2-1\) implies \(1-2E>(\sqrt2-1)^2\), forcing \(O>\sqrt2-1\). Equations (107.9) and (107.19) prove the calibrated bound for every rank and every complex phase allowed by the simultaneous-cyclic hypothesis.

### 107.4. Exact physical attainment

Let \(m=1/\sqrt2\) and take
\[
 G_* =\tfrac12 C_0+\tfrac m2 C_1+\tfrac{1-m}{2}C_3,
 \qquad
 H_* =\tfrac12 C_0+\tfrac{1-m}{2}C_5+\tfrac m2 C_7.
 \tag{107.20}
\]
All displayed coefficients are positive and have even/odd totals \(1/2\). These are calibrated rank-three Grams. Unit records with coordinates \(\sqrt{g_k}\zeta^{kj}\) and \(\sqrt{h_k}\zeta^{kj}\) realize them. The maps \(|j\rangle\mapsto|j\bmod4\rangle\otimes a_j\), and similarly for \(b_j\), are Stinespring isometries: records within each fibre are orthogonal, and distinct fibres have orthogonal output labels. Thus (107.20) specifies genuine original CPTP maps with the fixed correlated encodings. Their Kraus ranks equal the record-Gram ranks, namely three.

Here \(A=1\), \(B=m^2+(1-m)^2\), and the odd product coefficients are \((m,1-m,1-m,m)/4\). Hence
\[
 E=2m(1-m)=\sqrt2-1,
 \qquad O=2m-1=\sqrt2-1.
 \tag{107.21}
\]
More explicitly, with \(d=\sqrt2-1\), the eigenvalues of \(L_*=T-G_*\odot H_*\) are
\[
 (\ell_0,\ldots,\ell_7)=(2d,-d,-d,d,0,d,-d,-d).
 \tag{107.22}
\]
Both parity primal witnesses and the majorant \(Z=|L_*|\) in §107.2 match at \(d\), establishing exact complete-norm attainment.

### 107.5. Infima at ranks seven and four or five

Define three auxiliary coefficient distributions. Let \(u\) have weight \(1/6\) at even indices \(0,2,6\), weight \(1/8\) at odd indices \(1,3,5,7\), and zero at \(4\). Let \(v_4\) have weight \(1/4\) at \(0,2,5,7\) and zero elsewhere. Let \(v_5\) have weight \(1/6\) at \(0,2,6\), weight \(1/4\) at \(5,7\), and zero elsewhere. All have even/odd totals \(1/2\).

For \(0<\varepsilon<1\), replace the coefficients of \(G_*\) by \((1-\varepsilon)g_*+\varepsilon u\), and those of \(H_*\) by \((1-\varepsilon)h_*+\varepsilon v_h\), with \(h=4\) or \(5\). The resulting calibrated physical pair has exactly ranks \((7,h)\). The unique first kernel is the Fourier mode \(k=4\), whose eight coordinates are all nonzero. Formula (107.9) is continuous in these finite coefficient arrays, so their complete norms converge to \(d\). The lower bound proves that the infimum in each stated exact-rank class is precisely \(d\). This infimum construction imposes no quotient or common-normer condition on the approximating pairs.

### 107.6. Arbitrary original leakage

Return to arbitrary original channels satisfying §107.1. Define
\[
 \widetilde G=G+\operatorname{blockdiag}_f(I_2-G_{ff}),
 \qquad
 \widetilde H=H+\operatorname{blockdiag}_f(I_2-H_{ff}).
 \tag{107.23}
\]
The added matrices are positive semidefinite, so the completions are calibrated Grams. They remain circulant: a Hermitian circulant \(G\) has common fibre block \(\left(\begin{smallmatrix}d&c\\c&d\end{smallmatrix}\right)\), with \(c\) real, and its added matrix is \((1-d)I-cJ\). The same argument applies to \(H\). The completions may increase rank.

Cross-fibre products are unchanged. On each original fibre, Schur-product positivity gives
\[
 0\le G_{ff}\odot H_{ff}
   \le I_2\odot H_{ff}=\operatorname{diag}(H_{ff})\le I_2.
 \tag{107.24}
\]
Indeed the middle inequality is \((I_2-G_{ff})\odot H_{ff}\ge0\). Thus, for \(L=T-G\odot H\) and \(\widetilde L=T-\widetilde G\odot\widetilde H\), the matrix \(L-\widetilde L\) is positive semidefinite and fibre-block diagonal. Write \(\mathcal D\) for the original fibre-block densities. The leakage-safe adaptive bound of RT III §91 yields
\[
 \begin{aligned}
 \delta(A,B)&\ge\mathcal B(L)
   :=\max_{\rho\in\mathcal D,\ 0\le W\le\rho}2\operatorname{Tr}(LW)\\
 &\ge\mathcal B(\widetilde L)
   =F(\widetilde G,\widetilde H)\ge\sqrt2-1.
 \end{aligned}
 \tag{107.25}
\]
The second inequality uses only \(L-\widetilde L\ge0\) and \(W\ge0\). It does not require a physical transfer of a compressed block, a rank-preserving calibration, or local-minimum preservation. The calibrated attaining pair is also admissible in the larger leaking class, proving sharpness there and completing Theorem 107.1. \(\square\)

### 107.7. One-party symmetry and reciprocal phase gauges

**Corollary 107.2.** Under the original hypotheses of §107.1, it is enough for either correct-output Gram to be circulant. More generally, the conclusion holds if either Gram becomes circulant after a diagonal unitary conjugation and an original-fibre-preserving coordinate permutation. The other original channel may be nonsymmetric and leaking. The sharp minimum is still \(\sqrt2-1\), as are the infima in the calibrated exact-rank classes \((7,4)\) and \((7,5)\) with full-support first kernel.

Here a fibre-preserving permutation sends each original coordinate pair to a coordinate pair; it may permute the four fibres and interchange the two coordinates within any fibre. The corollary assumes that the specified phase gauge and relabeling exist; it does not assert their existence for every Gram.

**Proof.** Let \(P|j\rangle=|j+1\rangle\). It sends \(\{f,f+4\}\) to \(\{f+1,f+5\}\) modulo eight, including the order interchange at the last fibre. Thus conjugation by \(P\) bijects the set \(\mathcal D\) of original fibre-block densities and the complete fixed witness set \(\{(\rho,W):\rho\in\mathcal D,\ 0\le W\le\rho\}\). Also \(PTP^*=T\). Permutation covariance of the Hadamard product and the trace identity therefore give
\[
 \mathcal B(PLP^*)=\mathcal B(L),\qquad
 F(PGP^*,PHP^*)=F(G,H)
 \tag{107.26}
\]
for calibrated Grams. Both identities hold for every power of \(P\). The function \(\mathcal B\) is convex, since its definition is a maximum of linear functionals on this one fixed witness set. Accordingly \(F\) is convex in either Gram with the other fixed.

Suppose first that \(G,H\) are calibrated and \(G\) is circulant. The matrix
\[
 \overline H=\frac18\sum_{r=0}^7P^rH(P^*)^r
 \tag{107.27}
\]
is positive semidefinite with the original \(I_2\) fibre blocks. It commutes with \(P\), and hence is circulant. Every such calibrated Gram has an original Stinespring realization; no shared correlated branch is added. Since \(P^rG(P^*)^r=G\),
\[
 F(G,\overline H)
 \le\frac18\sum_{r=0}^7F(G,P^rH(P^*)^r)=F(G,H).
 \tag{107.28}
\]
This inequality is separate convexity, rather than an exchange of the reference optimization with the average. Theorem 107.1 applies to \((G,\overline H)\), proving the bound. Interchange the parties if \(H\) is circulant. The average may change rank; the lower bound required no rank hypothesis.

For arbitrary leaking original maps, apply the completions (107.23). If \(G\) is circulant, its completion is circulant by the same calculation in §107.6; no symmetry is needed for \(\widetilde H\). The operator order and the first two inequalities in (107.25) remain valid. Applying (107.28) to the completed calibrated pair proves \(\delta\ge\sqrt2-1\). This retains arbitrary nonsymmetric leakage on the other side.

Finally, let \(D\) be diagonal unitary and let \(Q\) be an original-fibre-preserving permutation. Define
\[
 G'=Q^*D^*GDQ,\qquad H'=Q^*DHD^*Q.
 \tag{107.29}
\]
The reciprocal phase factors cancel entrywise, so
\[
 G'\odot H'=Q^*(G\odot H)Q,\qquad Q^*TQ=T.
 \tag{107.30}
\]
The original fibre-block contraction constraints are preserved. These transformations can be implemented by precomposing the two local channels by \(D,D^*\), whose phases cancel on each correlated input, then precomposing both by \(Q\) and undoing its induced output-fibre permutation on both outputs. The target is covariant under the common relabeling, including the within-fibre swaps, and the complete norm is unitarily invariant. Alternatively, the leakage bound, (107.30) and the witness-set covariance prove the same implication directly. Thus, if either transformed Gram is circulant, the preceding argument applies with the unchanged original error bound. These transformations preserve ranks and full support of a one-dimensional kernel.

The attaining pair in §107.4 and both exact-rank families in §107.5 already satisfy simultaneous cyclic symmetry. They therefore establish the minimum and infima for the larger class of this corollary. \(\square\)

The averaging in (107.27) is justified because the other Gram is fixed and invariant. Independent cyclic averaging of two varying Grams need not preserve their product or improve the complete error. No reduction of an arbitrary pair to the class of Corollary 107.2 is asserted. The general residual alternatives of Theorem 106.5 and the unrestricted global quarter optimum remain unresolved.

## 108. Original-channel bounds from one group-translation-invariant Gram

### 108.1. Original group action and statement

Let $\Gamma$ be an abelian group of order eight, written additively, and choose an element $h$ of order two. Label the original eight coordinates by $\Gamma$ so that the original fibres are precisely the pairs $\{x,x+h\}$. Retain the two original local CPTP maps, the fixed correlated encodings and the unhalved arbitrary-reference error $\delta(A,B)$ of §107.1. The target coefficient matrix has diagonal entries one, partner entries zero and entries one half between different original fibres. The correct-output forward Grams $G,H$ satisfy $0\le G_{ff},H_{ff}\le I_2$, including arbitrary original leakage.

For $a\in\Gamma$, write $P_a|x\rangle=|x+a\rangle$. Translation invariance of a Gram means $`P_aGP_a^*=G`$ for every $a\in\Gamma$. The specified action on the original fibres is part of the hypothesis.

**Theorem 108.1.** If either correct-output Gram is translation-invariant, then

$$
 \delta(A,B)\ge\sqrt2-1.
 \tag{108.1}
$$

The same conclusion holds after reciprocal diagonal unitary phases and a common original-fibre-preserving coordinate relabeling. If $\Gamma=(\mathbb Z/2\mathbb Z)^3$, the bound strengthens to $\delta(A,B)\ge1/2$.

The constant $\sqrt2-1$ is sharp over the union of these abelian classes. It is sharp separately for $\Gamma=\mathbb Z/8\mathbb Z$, $h=4$, and for $\Gamma=\mathbb Z/4\mathbb Z\times\mathbb Z/2\mathbb Z$, $h=(2,0)$, with calibrated physical rank-$(3,3)$ attainers. No sharpness assertion is made for the elementary-abelian action or for the action with $h=(0,1)$ in $\mathbb Z/4\mathbb Z\times\mathbb Z/2\mathbb Z$.

### 108.2. Character coordinates and the original complete norm

**Proof.** Begin with two calibrated, translation-invariant Grams. Let $\widehat\Gamma$ be the character group, written additively, and let $0$ denote its trivial character. Define

$$
 (C_\chi)_{xy}=\chi(y-x),\qquad P_\chi=C_\chi/8.
 \tag{108.2}
$$

Character orthogonality makes the $P_\chi$ mutually orthogonal rank-one projections summing to the identity. Translation-invariant matrix entries depend only on $y-x$, so these character vectors diagonalize every such matrix. Consequently a translation-invariant positive semidefinite Gram has a unique expansion $G=\sum_\chi g_\chi C_\chi$ with $g_\chi\ge0$.

The two sets

$$
 E=\{\chi:\chi(h)=1\},\qquad O=\{\chi:\chi(h)=-1\}
 \tag{108.3}
$$

have four elements each, and $O$ is a coset of the subgroup $E$. Calibration is equivalent to

$$
 \sum_{\chi\in E}g_\chi=\sum_{\chi\in O}g_\chi=\tfrac12.
 \tag{108.4}
$$

Indeed the total sum is the diagonal coefficient and the difference of these sums is the partner coefficient. Write the coefficients of $H$ as $b_\chi$. Since $C_\chi\odot C_\psi=C_{\chi+\psi}$, the coefficients of $K=G\odot H$ are the convolution $`c=g*b`$, with total mass one half on each of $E,O$.

Let $J_{\rm all}$ denote the all-ones matrix. The target satisfies $T=(J_{\rm all}+I-P_h)/2$. Its character coefficients are $t_0=1/2$, $t_\chi=0$ for $\chi\in E\setminus\{0\}$, and $t_\chi=1/8$ for $\chi\in O$. Thus the eigenvalues of $L=T-K$ are $\ell_\chi=8(t_\chi-c_\chi)$, with sum zero separately in each parity sector.

The exact original calibrated complete norm is

$$
 \begin{aligned}
 F(G,H)&=\max\{E_0,O_0\},\\
 E_0&=2\sum_{\chi\in E}|t_\chi-c_\chi|,
 &O_0&=2\sum_{\chi\in O}|t_\chi-c_\chi|.
 \end{aligned}
 \tag{108.5}
$$

To verify the normalization, use the complete fibre-block formula (107.7). The original densities $(I+P_h)/8$ and $(I-P_h)/8$ have eigenvalue $1/4$ on their respective character sectors. Taking $W$ equal to one quarter of the corresponding positive spectral projection gives $E_0$ and $O_0$, because each sector's eigenvalue sum is zero. Conversely, $Z=|L|$ dominates $L$ and $-L$. Every original fibre block of $Z$ is $\left(\begin{smallmatrix}d&b\\b&d\end{smallmatrix}\right)$, since character values at $h$ are real signs; its eigenvalues are exactly $E_0,O_0$. Hence $Z_{ff}\le\max(E_0,O_0)I_2$, giving the matching majorant. This proves (108.5) for the original channel norm, including arbitrary references and operator inputs.

### 108.3. Coincident or distinct dominant character locations

Choose $\omega\in O$ and index four probability distributions by $E$:

$$
 p_x=2g_x,\quad q_x=2g_{\omega+x},\quad
 r_x=2b_x,\quad s_x=2b_{-\omega+x}.
 \tag{108.6}
$$

Set $A=\sum_xp_xr_{-x}$ and $B=\sum_xq_xs_{-x}$. Then $c_0=(A+B)/4$, and (108.5) gives $E_0=2-A-B$. If $E_0\ge1/2$, both conclusions follow. Otherwise $A,B>1/2$.

For two probability distributions with inner product $a>1/2$, each unique maximum exceeds one half. Those maxima occur at the same position: if their positions differ and their heights are $m,n$, splitting the sum at the first position bounds it by $m(1-n)+(1-m)n<1/2$. At a common peak, $a\le mn+(1-m)(1-n)$. Therefore $(m+n-1)^2\ge(2m-1)(2n-1)\ge2a-1$, and $m+n\ge1+\sqrt{2a-1}$.

Apply this to $(p_x,r_{-x})$ and $(q_x,s_{-x})$. Their peaks occur at $u,-u,v,-v$, respectively. Writing the four peak heights as $m_p,m_r,m_q,m_s$, we obtain

$$
 m_p+m_r\ge1+\sqrt{2A-1},\qquad
 m_q+m_s\ge1+\sqrt{2B-1}.
 \tag{108.7}
$$

The dominant $`p*s`$ contribution lies at $\chi_1=-\omega+u-v$, and the dominant $`q*r`$ contribution lies at $\chi_2=\omega+v-u=-\chi_1$. Put $S=\{\chi_1,\chi_2\}\subset O$. These locations may coincide; their contributions still add. Hence

$$
 \sum_{\chi\in S}c_\chi\ge\tfrac14(m_pm_s+m_qm_r),
 \qquad O_0\ge m_pm_s+m_qm_r-\tfrac{|S|}{2}.
 \tag{108.8}
$$

For the second inequality, the vectors $(c_\chi)_{\chi\in O}$ and $(1/8)_{\chi\in O}$ have equal total mass. Their $\ell^1$ distance is at least twice the excess on any subset; (108.5) supplies the additional factor two.

Since $|S|\le2$ and $xy\ge x+y-1$ on $[0,1]^2$,

$$
 O_0\ge\sqrt{2A-1}+\sqrt{2B-1}-1
       \ge\sqrt{1-2E_0}.
 \tag{108.9}
$$

For the last step, put $X=2A-1$, $Y=2B-1$. These lie in $(0,1]$, satisfy $X+Y=2-2E_0$ and $XY\ge X+Y-1$, and therefore satisfy $\sqrt X+\sqrt Y\ge1+\sqrt{X+Y-1}$ by squaring nonnegative quantities. The increasing function $E_0$ and decreasing function $\sqrt{1-2E_0}$ meet at $E_0=\sqrt2-1$. This proves (108.1), including $E_0=0$ and the separately treated branch $E_0\ge1/2$.

If $\Gamma=(\mathbb Z/2\mathbb Z)^3$, every character has order at most two. Thus $\chi_1=\chi_2$ and $|S|=1$. The same calculation improves (108.9) to

$$
 O_0\ge\tfrac12+\sqrt{1-2E_0}>\tfrac12
       \quad\text{when }E_0<\tfrac12.
 \tag{108.10}
$$

The other branch already has $E_0\ge1/2$, proving the additional elementary-abelian bound.

### 108.4. One-party invariance, leakage and sharpness

Suppose now that the calibrated Gram $G$ alone is invariant. Each translation permutes the four original fibres, fixes $T$ and bijects the full fixed witness domain in (107.7). Averaging only the other Gram gives

$$
 \overline H=\tfrac18\sum_{a\in\Gamma}P_aHP_a^*,
 \qquad
 F(G,\overline H)\le\tfrac18\sum_{a\in\Gamma}F(G,P_aHP_a^*)=F(G,H).
 \tag{108.11}
$$

The inequality follows from convexity with $G$ fixed, and the equality from its invariance and witness-domain covariance. The average is positive semidefinite, calibrated and translation-invariant. Thus §§108.2–108.3 apply. Interchanging the parties covers the other possibility. The averaging may change rank.

For arbitrary original leakage, complete both Grams by adding their positive semidefinite original fibre-block deficits, as in (107.23). An invariant $G$ has the same block $\left(\begin{smallmatrix}d&c\\c&d\end{smallmatrix}\right)$ on every fibre, with $c$ real. Its completion adds $(1-d)I-cP_h$, which is still invariant. The other completion needs no symmetry. The original product blocks satisfy $G_{ff}\odot H_{ff}\le I_2$, so $L-\widetilde L$ is positive semidefinite and fibre-block diagonal. The original tagged-reference bound of RT III §91 therefore gives $\delta\ge\mathcal B(L)\ge\mathcal B(\widetilde L)=F(\widetilde G,\widetilde H)$. Apply (108.11) to the completed pair. Reciprocal diagonal phases cancel in the full product, while a common fibre-preserving relabeling simultaneously reindexes $K,T$ and the witness domain. The actual original-channel operations in §107.7 prove the optional phase and relabeling statement with the same error.

The cyclic attainer of §107.4 proves the first sharpness assertion. For the second, take $\Gamma=\mathbb Z/4\mathbb Z\times\mathbb Z/2\mathbb Z$, $h=(2,0)$, and identify its characters with pairs $(a,b)$, evaluated by $\chi_{a,b}(x,y)=i^{ax}(-1)^{by}$. Put $\chi=(1,0)$, $\psi=(1,1)$, and $m=1/\sqrt2$. Define

$$
 \begin{aligned}
 G&=\tfrac12C_0+\tfrac m2C_\chi+\tfrac{1-m}{2}C_\psi,\\
 H&=\tfrac12C_0+\tfrac m2C_{-\chi}+\tfrac{1-m}{2}C_{-\psi}.
 \end{aligned}
 \tag{108.12}
$$

The four odd characters $\chi,\psi,-\chi,-\psi$ are distinct. Both Grams are calibrated of rank three. The character records $(\sqrt{g_\eta}\eta(x))_\eta$, together with the correct output-fibre labels, give original Stinespring isometries because partner records are orthogonal. Here $A=1$, $B=m^2+(1-m)^2$, so $E_0=2m(1-m)=\sqrt2-1$. The odd coefficients at $\chi,-\chi$ are $m/4$, and those at $\psi,-\psi$ are $(1-m)/4$. Thus $O_0=2m-1=\sqrt2-1$. Equation (108.5) proves exact original complete-norm attainment. $\square$

The character diagonalization and convex symmetry reduction are standard intermediate tools. The spectral-majorant technique is credited in §107.2 to Regula, Takagi and Gu; the original fibre normalization and probability estimate used here have been proved explicitly. No independent averaging of two varying Grams is justified by (108.11). These translation hypotheses remain substantive, and neither the general residual alternatives of Theorem 106.5 nor the unrestricted global quarter optimum are resolved.

### 108.5. Central partner actions of the two nonabelian groups

Let $\Gamma$ now be the dihedral group $D_8$ of order eight or the quaternion group $Q_8$, and let $z$ be its central involution. Label the original coordinates by $\Gamma$, with original fibres $\{x,xz\}$, and write $P_a|x\rangle=|ax\rangle$. Left-translation invariance means $`P_aGP_a^*=G`$ for all $a$, equivalently $G_{xy}=g(x^{-1}y)$. All channel, encoding, leakage and norm conventions of §108.1 are retained.

**Theorem 108.2.** If either correct-output Gram is left-translation-invariant for either of these central partner actions, then

$$
 \delta(A,B)\ge\tfrac12.
 \tag{108.13}
$$

The conclusion also holds after the reciprocal phase changes and original-fibre-preserving relabelings of §107.7. For each group the bound is sharp, with an explicit calibrated physical rank-$(3,3)$ attainer. Its infimum is also $1/2$ in each corresponding calibrated exact-rank class $(7,4)$ and $(7,5)$ with full-support first kernel.

The central-partner condition is substantive. In particular the theorem does not assert the same bound for $D_8$ when a noncentral reflection defines the original partner operation.

### 108.6. Representation coefficients and a coherent original-input bound

**Proof.** First assume both Grams are calibrated and invariant. Use the following faithful two-dimensional unitary representation $U$. For $Q_8$, take the eight matrices $\{\pm I,\pm iX,\pm iY,\pm iZ\}$, with $X,Y,Z$ the Pauli matrices. For $D_8$, use

$$
 U(r)=\begin{pmatrix}0&-1\\1&0\end{pmatrix},
 \qquad U(s)=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
 \qquad r^4=s^2=e,\quad srs=r^{-1}.
 \tag{108.14}
$$

In both cases $U(z)=-I$. The four one-dimensional characters are the real sign characters of $\Gamma/\{e,z\}\cong(\mathbb Z/2\mathbb Z)^2$; denote their set by $E$. Directly from the eight displayed matrices,

$$
 \sum_{x\in\Gamma}\overline{\chi(x)}\psi(x)=8\delta_{\chi\psi},
 \qquad
 \sum_{x\in\Gamma}\overline{U(x)_{ij}}U(x)_{kl}
       =4\delta_{ik}\delta_{jl}.
 \tag{108.15}
$$

Mixed character/matrix-entry sums vanish: the characters are even under $x\mapsto xz$, and the matrix entries are odd. These eight orthogonal functions span all functions on $\Gamma$, giving the regular representation's decomposition into the four characters and two copies of $U$.

Every invariant positive semidefinite Gram consequently has

$$
 g(x)=\sum_{\chi\in E}a_\chi\chi(x)+\operatorname{Tr}(MU(x)),
 \qquad a_\chi\ge0,\quad M\succeq0.
 \tag{108.16}
$$

Here is a direct positivity justification. Choose records $v_x=G^{1/2}|x\rangle$. Invariance makes left translation unitary on their span and sends $v_e$ to $v_x$. Resolve $v_e$ into the four character spaces and the $U$-multiplicity space from (108.15). The squared norms in the character spaces give $a_\chi$. The partial trace of the odd vector's positive outer product over the multiplicity space is $M$, whose matrix coefficient is the last term of (108.16). Conversely every such expression is a sum of Gram kernels. Equivalently, the normalized character and matrix-entry basis puts $G$ into blocks $8a_\chi$ and two copies of $4M^{\mathsf T}$. Thus

$$
 \operatorname{rank}G=|\{\chi:a_\chi>0\}|+2\operatorname{rank}M,
 \qquad
 \sum_{\chi\in E}a_\chi=\operatorname{Tr}M=\tfrac12.
 \tag{108.17}
$$

The last two equalities are exactly $g(e)=1$, $g(z)=0$. Write the second Gram function as $b(x)=\sum_\chi b_\chi\chi(x)+\operatorname{Tr}(NU(x))$, with the same nonnegativity and half-mass constraints.

The original product coefficient function is $k(x)=g(x)b(x)$. Its trivial-character coefficient is

$$
 c_0=\tfrac18\sum_xg(x)b(x)
     =\sum_\chi a_\chi b_\chi+
           \operatorname{Tr}[(M\otimes N)\Pi],
 \qquad \Pi=\tfrac18\sum_xU(x)\otimes U(x).
 \tag{108.18}
$$

The mixed even/odd terms vanish. The four characters are real and self-inverse, so their pairing in (108.18) has exactly the displayed indices. The tensor term is the ordinary trace identity for the actual Hadamard product.

The group average $\Pi$ is the orthogonal projection onto the invariant vectors of $U\otimes U$. Its trace is one: $\operatorname{Tr}U(x)$ is zero except at $e,z$, where it is $2,-2$, and therefore $\operatorname{Tr}\Pi=(4+4)/8=1$. For $D_8$ its invariant unit vector is $(|00\rangle+|11\rangle)/\sqrt2$, since $U$ is real orthogonal. For $Q_8$ it is $(|01\rangle-|10\rangle)/\sqrt2$, since $U$ is special unitary. Both are maximally entangled.

For any two density matrices $\tau,\sigma$, the expectation of $\Pi$ in $\tau\otimes\sigma$ is at most $1/2$. For pure product vectors this is Cauchy–Schwarz applied to either displayed invariant vector; decomposing the two densities into pure states proves the general case by linearity. Apply this with $\tau=2M$, $\sigma=2N$. Equation (108.18) gives

$$
 c_0\le\Bigl(\sum_\chi a_\chi\Bigr)
             \Bigl(\sum_\chi b_\chi\Bigr)+\tfrac18
       =\tfrac38.
 \tag{108.19}
$$

Let $C_0$ be the all-ones matrix, and let $R_z|x\rangle=|xz\rangle$. The row sums of $K$ and $T$ are $8c_0$ and four, so the uniform vector is an eigenvector of $L=T-K$ with eigenvalue $\lambda_0=4-8c_0\ge1$. The original fibre-block density and witness

$$
 \rho=(I+R_z)/8,\qquad W=C_0/32
 \tag{108.20}
$$

satisfy $\operatorname{Tr}\rho=1$ and $0\le W\le\rho$: $\rho$ has eigenvalue $1/4$ on the $z$-even space, containing the uniform vector. Formula (107.7) now gives

$$
 F(G,H)\ge2\operatorname{Tr}(LW)=\lambda_0/2\ge\tfrac12.
 \tag{108.21}
$$

This has the original unhalved normalization. The density is realized by the no-reference uniform coherent input; the feasible witness extracts a lower bound from that output. No norm formula for a differently normalized irreducibly covariant channel is used.

### 108.7. Physical attainers and exact-rank infima

For $Q_8$, choose $v=|0\rangle$, $w=|1\rangle$. For $D_8$, choose $v=(|0\rangle+i|1\rangle)/\sqrt2$, $w=(|0\rangle-i|1\rangle)/\sqrt2$. In each case $v,w$ are orthonormal. Define records in $\mathbb C\oplus\mathbb C^2$ by

$$
 a_x=\frac{1\oplus U(x)v}{\sqrt2},\qquad
 b_x=\frac{1\oplus U(x)w}{\sqrt2}.
 \tag{108.22}
$$

They are unit vectors and their partner records are orthogonal because $U(z)=-I$. The maps $|x\rangle\mapsto|x\{e,z\}\rangle\otimes a_x$, and similarly for $b_x$, are therefore original Stinespring isometries with the fixed correlated encodings. The record span is three-dimensional: its even constant component is independent of the odd orbit, and the irreducible $U$ orbit spans two dimensions. Both local Kraus ranks are exactly three.

Put $`f_v(x)=v^*U(x)v`$, $`f_w(x)=w^*U(x)w`$. Their sum is $\operatorname{Tr}U(x)$. For $Q_8$, their product is the indicator of $\{\pm I,\pm iZ\}$; for $D_8$, it is the indicator of the rotation subgroup. Consequently a nontrivial even sign character $\chi$ satisfies

$$
 f_v(x)f_w(x)=\frac{1+\chi(x)}2,\qquad
 \operatorname{Tr}U(x)=2\mathbf1_{x=e}-2\mathbf1_{x=z}.
 \tag{108.23}
$$

Since $g=(1+f_v)/2$ and $b=(1+f_w)/2$, direct multiplication gives

$$
 k(x)=\tfrac38+\tfrac18\chi(x)+\tfrac14\operatorname{Tr}U(x),
 \qquad L=\tfrac18(C_0-C_\chi),
 \tag{108.24}
$$

where $(C_\chi)_{xy}=\chi(x^{-1}y)$. The eigenvalues of $L$ are $+1,-1$ and six zeros. Its absolute value $Z=(C_0+C_\chi)/8$ has every original fibre block equal to the all-ones two-by-two matrix divided by four, with eigenvalues $1/2,0$. Thus $Z\succeq\pm L$ and $Z_{ff}\preceq I_2/2$, providing the complete-norm majorant matching (108.21). The physical error is exactly one half.

For the rank infima, choose an auxiliary first Gram in (108.16) with $a_\chi=1/6$ on three even characters including the trivial character, zero on the fourth, and $M=I_2/4$. Mix it with the first attaining Gram using any weight $0<\varepsilon<1$. Equation (108.17) gives rank seven, with the omitted character as its unique full-support kernel. For the auxiliary second Gram, keep $N=|w\rangle\langle w|/2$, and choose either two even weights $1/4$ or three even weights $1/6$, including the trivial character. Mixing with the second attaining Gram gives rank four or five, respectively. All these Grams are calibrated and physically realizable. As $\varepsilon\to0$, continuity of the complete norm gives error tending to $1/2$; (108.21) supplies the matching lower bound. No common-stress or local-minimum property is asserted for the approximants.

### 108.8. Original leakage, one-party symmetry and the remaining boundary

For a calibrated pair with only $G$ invariant, average $H$ over the eight left translations. Each translation permutes the original coset fibres, fixes $T$ and bijects the complete fixed witness domain. The separate-convexity argument of (108.11) is valid without commutativity of the group and yields $F(G,\overline H)\le F(G,H)$. The average is calibrated and invariant, so (108.21) applies. Interchanging the two parties covers the other case.

For leaking original channels, complete their Grams by the fibre deficits. An invariant $G$ has the common block $\left(\begin{smallmatrix}d&c\\c&d\end{smallmatrix}\right)$, with $c$ real because $z=z^{-1}$. Its completion adds $(1-d)I-cR_z$, which commutes with every left translation. No symmetry of the other completion is needed. The product-block inequality (107.24) again gives $L-\widetilde L\succeq0$; the tagged-reference theorem gives $\delta\ge\mathcal B(L)\ge F(\widetilde G,\widetilde H)$. The calibrated average and (108.21) prove (108.13). Reciprocal phases and common original-fibre relabelings are implemented exactly as in §107.7. The calibrated attainers belong to the larger leaking class, proving sharpness there. This completes Theorem 108.2. $\square$

The finite representation decomposition and maximally entangled product overlap are standard intermediate facts, with the exact instances needed here proved above. For finite-group channel context and the explicit quaternion representation and character table, see Mozrzymas, Studziński and Datta, *Structure of irreducibly covariant quantum channels for finite groups*, [arXiv:1610.05657v2](https://arxiv.org/abs/1610.05657v2), §§4 and 8.2, and the [source note](../../../Library/QuantumChannels/mozrzymas2017irreduciblycovariant.md). Their channels are covariant under an irreducible representation, rather than the original regular eight-coordinate product setting here; no differently normalized channel-norm theorem is imported. The spectral-majorant attribution in §107.2 also applies.

In $D_8$, a noncentral reflection can define original coset fibres preserved by left translations, but the parity decomposition used in (108.17) then fails: the two-dimensional representation can itself admit orthogonal partner records. That case is not covered by Theorem 108.2. Neither theorem in this section reduces arbitrary original pairs to a translation-invariant class. The unrestricted residual rank alternatives and the global quarter optimum remain open.

## 109. Noncentral reflection fibres: an original-channel gap and exact subhalf examples

### 109.1. The noncentral action and the lower bound

Let $D_8=\langle r,s\mid r^4=s^2=e,\ srs=r^{-1}\rangle$ label the original eight input coordinates, with original fibres $\{x,xs\}=x\langle s\rangle$. These are left cosets, or equivalently orbits of right multiplication by the noncentral reflection $s$. Keep the original local $\mathbb C^8\to\mathbb C^4$ channels, correlated encoding and unhalved arbitrary-reference diamond error $\delta$.

**Theorem 109.1.** If either correct-output Gram is invariant under all eight left translations, then

$$
\delta\geq\sqrt2-1>\frac14. \tag{109.1}
$$

The other channel may be nonsymmetric, and either channel may leak. The conclusion also holds after an original fibre-preserving coordinate relabeling and reciprocal diagonal unitary phases. No rank or real-phase hypothesis is imposed. Sharpness for this particular action is not asserted.

First suppose both Grams are calibrated and invariant. Use the real representation and sign characters

$$
U(r)=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
U(s)=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
\chi_{\epsilon,\eta}(r^as^b)=\epsilon^a\eta^b.
\tag{109.2}
$$

The orthogonality calculation in §108 gives the unique expansions

$$
\begin{aligned}
g(x)&=\sum_\chi a_\chi\chi(x)+\operatorname{Tr}(MU(x)),
& M&=\begin{pmatrix}p/2&z\\\overline z&q/2\end{pmatrix},\\
b(x)&=\sum_\chi b_\chi\chi(x)+\operatorname{Tr}(NU(x)),
& N&=\begin{pmatrix}p'/2&w\\\overline w&q'/2\end{pmatrix}.
\end{aligned}\tag{109.3}
$$

Here $G_{xy}=g(x^{-1}y)$ and $H_{xy}=b(x^{-1}y)$. Their regular blocks are $8a_\chi,4M^{\mathsf T},4M^{\mathsf T}$ and their second-party counterparts. Thus the scalar coefficients are nonnegative and $M,N\succeq0$. Calibration at $e,s$ gives

$$
\begin{aligned}
\sum_\epsilon a_{\epsilon,+}&=\frac{1-p}{2},&
\sum_\epsilon a_{\epsilon,-}&=\frac{1-q}{2},&
|z|^2&\leq\frac{pq}{4},\\
\sum_\epsilon b_{\epsilon,+}&=\frac{1-p'}{2},&
\sum_\epsilon b_{\epsilon,-}&=\frac{1-q'}{2},&
|w|^2&\leq\frac{p'q'}{4}.
\end{aligned}\tag{109.4}
$$

In particular $p,q,p',q'\in[0,1]$; the complex phases of $z,w$ remain arbitrary.

Write the product coefficient $k(x)=g(x)b(x)$ as $\sum_\chi c_\chi\chi(x)+\operatorname{Tr}(SU(x))$, where $c_\chi\geq0$ and $S\succeq0$. Put $c_0=c_{+,+}$ and $c_-=c_{+,-}+c_{-,-}$. The invariant vector of $U\otimes U$ is $(|00\rangle+|11\rangle)/\sqrt2$, so

$$
c_0=\sum_\chi a_\chi b_\chi+\frac{pp'+qq'}8+\operatorname{Re}(zw).
\tag{109.5}
$$

The tensor contribution is $\tfrac12\operatorname{Tr}(MN^{\mathsf T})$, so no conjugate is inserted into $zw$. Matching nonnegative products within each $\eta$ sector are bounded by the product of the sector masses. Moreover,

$$
\operatorname{Re}(zw)\leq|zw|\leq\frac{\sqrt{pq p'q'}}4
\leq\frac{pp'+qq'}8.
\tag{109.6}
$$

For $c_-$ the scalar characters contribute opposite-$\eta$ products. The sum of the two $\eta=-1$ projectors in $U\otimes U$ is the projector onto $\operatorname{span}\{|01\rangle,|10\rangle\}$, contributing $(pq'+qp')/4$. Consequently, with $P=1-2p$, $Q=1-2q$, $P'=1-2p'$ and $Q'=1-2q'$, all in $[-1,1]$,

$$
\begin{aligned}
c_0&\leq\frac{(1-p)(1-p')+(1-q)(1-q')+pp'+qq'}4
      =\frac14+\frac{PP'+QQ'}8,\\
c_-&=\frac{(1-p)(1-q')+(1-q)(1-p')+pq'+qp'}4
      =\frac14+\frac{PQ'+QP'}8.
\end{aligned}\tag{109.7}
$$

### 109.2. Two original coherent inputs

Let $R_s|x\rangle=|xs\rangle$ and $P_\pm=(I\pm R_s)/2$. The original target is $T=(J_{\rm all}+I-R_s)/2$; in the character order $(++),(-+),(+-),(--)$ its coefficients are $(1/2,0,1/8,1/8)$ and its two-dimensional coefficient is $\operatorname{diag}(0,1/4)$. For $L=T-G\odot H$, the original block-diagonal densities $\rho_\pm=P_\pm/4$ have trace one. RT III §91 gives

$$
F(G,H)\geq E_\pm:=\frac14\|P_\pm L P_\pm\|_1.
\tag{109.8}
$$

No commutation of $L$ with $R_s$ is required. In the regular decomposition, $R_s$ acts by the character signs $\eta$ and the two copies of $U(s)^{\mathsf T}$. The compressions remove the off-diagonal entries of the two-dimensional coefficient. The scalar eigenvalues have multiplicity one and factor eight; the two two-dimensional copies have factor four. Hence

$$
\begin{aligned}
E_+&=2\bigl(|1/2-c_0|+c_{-,+}+S_{11}\bigr),\\
E_-&=2\bigl(|1/8-c_{+,-}|+|1/8-c_{-,-}|+|1/4-S_{22}|\bigr).
\end{aligned}\tag{109.9}
$$

The product calibration gives $c_0+c_{-,+}+S_{11}=1/2$ and $c_-+S_{22}=1/2$. Thus $c_0\leq1/2$, and (109.7) yields

$$
E_+=2-4c_0\geq1-\frac{PP'+QQ'}2,\qquad
E_-\geq4|c_--1/4|=\frac{|PQ'+QP'|}{2}.
\tag{109.10}
$$

Put $e=|PQ'+QP'|/2\in[0,1]$. The exact identity

$$
\begin{split}
(PQ'+QP')^2+4(1-PP'-QQ')
&=(PQ'-QP')^2+4(1-PP')(1-QQ')\\
&\geq0
\end{split}\tag{109.11}
$$

implies $PP'+QQ'\leq1+e^2$. Therefore

$$
F(G,H)\geq\max\left\{e,\frac{1-e^2}{2}\right\}\geq\sqrt2-1.
\tag{109.12}
$$

Indeed $d=\sqrt2-1$ satisfies $(1-d^2)/2=d$; use the first term when $e\geq d$ and the second otherwise. This proof includes all endpoints and singular coefficient matrices without division.

### 109.3. One invariant side and original leakage

For calibrated Grams, fix the invariant $G$ and average only $H$ over the eight original left translations. These permutations preserve the original fibre partition and target. The full original norm $F$ is simultaneously permutation invariant and convex in $H$ with $G$ fixed. Consequently $F(G,H)\geq F(G,\overline H)$, and the two-sided result applies to the invariant calibrated average $\overline H$. Interchanging the channels covers the other fixed side.

For leaking channels form the actual calibrated completions

$$
\widetilde G=G+\bigoplus_f(I_2-G_{ff}),\qquad
\widetilde H=H+\bigoplus_f(I_2-H_{ff}).
\tag{109.13}
$$

The correct-output blocks satisfy $0\preceq G_{ff},H_{ff}\preceq I_2$. The completions are positive semidefinite, physically realizable, and retain every cross-fibre entry. If $G$ is invariant, write $g(e)=d_0$ and $g(s)=c\in\mathbb R$. Its completion increment is $(1-d_0)I-cR_s$, which commutes with every left translation. Thus the fixed side remains invariant.

Set $L=T-G\odot H$ and $\widetilde L=T-\widetilde G\odot\widetilde H$. Their difference is supported on original fibre blocks and satisfies

$$
(L-\widetilde L)_{ff}=I_2-G_{ff}\odot H_{ff}\succeq0,
\qquad G_{ff}\odot H_{ff}\preceq\operatorname{diag}(H_{ff})\preceq I_2.
\tag{109.14}
$$

The tagged-reference consumer of RT III §91, with the same positive witness domain, now gives

$$
\delta\geq\mathcal B(L)\geq\mathcal B(\widetilde L)
 =F(\widetilde G,\widetilde H)\geq\sqrt2-1.
\tag{109.15}
$$

Reciprocal diagonal unitary phases cancel in every original product coefficient. Fibre-preserving relabelings simultaneously reindex that coefficient, the target and the full witness domain. The physical covariance argument of §107 therefore proves the stated gauge extension. This completes Theorem 109.1. Any reflection $r^ks$ can replace $s$ as presentation generator, so the theorem covers every noncentral involution of $D_8$.

### 109.4. An exact family below one half

**Proposition 109.2.** The central half bound of §108 cannot be extended to these noncentral reflection fibres. There are calibrated invariant rank-$(4,4)$ physical pairs with exact original error $23/49<1/2$. An explicit family has minimum $2\sqrt3-3$ within that family. There are also exact-rank-$(7,4)$ and $(7,5)$ examples below one half, with a unique full-support first kernel.

For $0\leq q\leq1$ and real $\theta$, set

$$
(a_{+,+},a_{-,+},a_{+,-},a_{-,-})
 =\left(0,0,\frac{1-q}{4},\frac{1-q}{4}\right),\qquad
M=\frac12\begin{pmatrix}1&\sqrt q e^{i\theta}\\\sqrt q e^{-i\theta}&q\end{pmatrix},
\quad N=\overline M.
\tag{109.16}
$$

Use the same scalar coefficients for $H$. Explicit first-party unit records are

$$
\mathbf a_x=\left(\sqrt{\frac{1-q}{4}}\chi_{+,-}(x),\
\sqrt{\frac{1-q}{4}}\chi_{-,-}(x),\
\frac{U(x)v}{\sqrt2}\right),\qquad
v=\begin{pmatrix}1\\\sqrt q e^{-i\theta}\end{pmatrix},
\tag{109.17}
$$

and second-party records are their complex conjugates. Their partner overlap is $-(1-q)/2+(1-q)/2=0$. Therefore $|x\rangle\mapsto|x\langle s\rangle\rangle\otimes\mathbf a_x$ and the conjugate-record analogue are original Stinespring isometries. For $0<q<1$, two positive scalar blocks and a rank-one two-dimensional coefficient with multiplicity two give both local Kraus ranks four.

Direct multiplication gives

$$
\begin{aligned}
c_{+,+}&=\frac{1+q^2}{4},&c_{-,+}&=\frac{(1-q)^2}{4},\\
c_{+,-}&=\frac{q\sin^2\theta}{2},&c_{-,-}&=\frac{q\cos^2\theta}{2},\\
S&=\operatorname{diag}\left(\frac{q(1-q)}2,\frac{1-q}2\right).
\end{aligned}\tag{109.18}
$$

The error coefficient is diagonal in the parity decomposition, so $L$ commutes with $R_s$. Formula (109.9) becomes

$$
\begin{aligned}
E_+&=1-q^2,\\
E_-&=2\left(\left|\frac18-\frac{q\sin^2\theta}{2}\right|
 +\left|\frac18-\frac{q\cos^2\theta}{2}\right|
 +\left|\frac{2q-1}{4}\right|\right).
\end{aligned}\tag{109.19}
$$

These two values give the exact full norm. For the upper bound take $Z=|L|$. Its original fibre blocks are $\left(\begin{smallmatrix}d_1&c_1\\c_1&d_1\end{smallmatrix}\right)$ with $d_1=\operatorname{Tr}|L|/8$ and $c_1=\operatorname{Tr}(R_s|L|)/8\in\mathbb R$. Their eigenvalues are $E_+,E_-$. Thus $Z\succeq\pm L$ and $Z_{ff}\preceq\max(E_+,E_-)I_2$. The full original majorant from RT III §91, together with (109.8), proves

$$
\delta=\max(E_+,E_-).
\tag{109.20}
$$

At $\theta=\pi/4$ this is $\max(1-q^2,|2q-1|)$. On $[0,1/2]$ the first term dominates and is at least $3/4$. On $[1/2,1]$ the decreasing first term and increasing second term meet at $q=\sqrt3-1$, giving the stated family minimum $2\sqrt3-3$.

For rational Gaussian Gram entries choose

$$
q=\frac{36}{49},\qquad e^{i\theta}=\frac{3+4i}{5},\qquad
M=\begin{pmatrix}1/2&(9+12i)/35\\(9-12i)/35&18/49\end{pmatrix}.
\tag{109.21}
$$

Here $c_{+,-}=288/1225$ and $c_{-,-}=162/1225$ both exceed $1/8$, so

$$
E_+=\frac{1105}{2401}<E_-=\frac{23}{49}<\frac12.
\tag{109.22}
$$

### 109.5. Full-support rank-seven examples and scope

Keep the rational fixture. Define calibrated auxiliary coefficients

$$
\begin{aligned}
a^{\rm aux}&=(1/4,0,1/8,1/8),&M^{\rm aux}&=I_2/4,\\
b^{\rm aux}&=\left(1/4,0,\frac{1-q/2}{4},\frac{1-q/2}{4}\right),
&N^{\rm aux}&=N/2.
\end{aligned}\tag{109.23}
$$

The corresponding Grams have ranks seven and five. Their diagonals equal one and partner entries vanish. With $\varepsilon=1/1000$, mix each separately with its original Gram to obtain $G_\varepsilon,H_\varepsilon$. The first has rank seven and unique kernel $\chi_{-,+}$, all of whose entries are nonzero; the second has rank five. Keeping $H$ instead gives rank pair $(7,4)$.

Every calibrated Gram lies between $0$ and $8I$. Schur multiplication by a correlation Gram contracts the operator norm on Hermitian matrices. A calibrated product-coefficient difference $D$ has zero original fibre blocks and original complete norm at most $\|D\|_{\rm op}$, using the majorant $\|D\|_{\rm op}I$. The triangle inequality and the actual two-Gram product expansion therefore give

$$
\delta(G_\varepsilon,H)\leq\frac{23}{49}+8\varepsilon<\frac12,
\qquad
\delta(G_\varepsilon,H_\varepsilon)\leq\frac{23}{49}+16\varepsilon<\frac12.
\tag{109.24}
$$

For the latter bound use $(G_\varepsilon-G)\odot H_\varepsilon+G\odot(H_\varepsilon-H)$. These are separately realized original physical Grams, without shared randomness between the local channels. Theorem 109.1 also bounds their errors below by $\sqrt2-1>1/4$.

Theorem 109.1 supplies a common lower bound for the noncentral action, while Proposition 109.2 proves that the sharper central conclusion needs its central-partner hypothesis. The interval between $\sqrt2-1$ and $2\sqrt3-3$ is not closed here. None of the examples is asserted to be a local minimum or a common-stress solution. The finite representation and spectral intermediates retain the primary attribution of §§107–108; the original input normalizations are proved above. No unrestricted global-quarter conclusion follows.

### 109.6. A regular-symmetry consumer

**Corollary 109.3.** Suppose a group of eight coordinate permutations acts freely and transitively on the original inputs, preserves the four original fibres, and leaves either correct-output Gram invariant. Then the original unhalved error satisfies $\delta\geq\sqrt2-1$. The same conclusion holds after the physical reciprocal phases and fibre-preserving relabelings already specified.

Identify the eight inputs with the acting group $\Gamma$ by choosing one input as identity. The fibre $B$ containing the identity has size two. If $h$ is its other element, then $hB$ and $B$ intersect, so they are the same block of the preserved partition. Thus $h^2=e$ and $B=\{e,h\}$. All fibres are the left cosets $x\langle h\rangle$, exactly the original group-coordinate setting of §§108–109.

For completeness, an abelian group of order eight has type $C_8$, $C_4\times C_2$ or $C_2^3$. Indeed an element of order eight gives the first type; if the exponent is two it is a three-dimensional vector space over the two-element field; otherwise an element $r$ of order four generates an index-two subgroup. For an outside element $t$, one has $t^2=e$ or $t^2=r^2$; in the latter case $tr^{-1}$ is an outside involution. This yields the second type. These are covered by §108.

If $\Gamma$ is nonabelian, some element $r$ has order four, since a group whose elements all square to the identity is abelian. Its cyclic subgroup has index two and is normal. Every outside element conjugates $r$ to $r^{-1}$, for otherwise it and $r$ generate an abelian group. For an outside element $s$, its square lies in $\langle r\rangle$ and is fixed by inversion, so $s^2=e$ or $s^2=r^2$. These are respectively the presentations of $D_8$ and $Q_8$. In $Q_8$ the only involution is central; in $D_8$ the involutions are the central $r^2$ and the four reflections. The central cases are covered by §108 and the reflection cases by Theorem 109.1. This proves the corollary.

The regular action is a substantive hypothesis. No assertion that an arbitrary transitive symmetry group contains such a subgroup, and no averaging of an arbitrary pair into a regular-symmetric pair, is needed or inferred.

## 110. A sharp obstruction from transitive symmetry of one original Gram

### 110.1. Original hypotheses and the matrix symmetry

Let $\Omega$ be the original eight-coordinate set, partitioned into the four two-element fibres $\Omega_f$. Keep the original local CPTP maps $A,B:\mathbb C^8\to\mathbb C^4$, the fixed correlated input and output encodings, and the target of §107.1. For Stinespring isometries $V_A,V_B$, define the correct-output records and their forward Grams by

$$
\begin{aligned}
a_j&=(\langle f|\otimes I)V_A|j\rangle,&
G_{jk}&=\langle a_j,a_k\rangle,\\
b_j&=(\langle f|\otimes I)V_B|j\rangle,&
H_{jk}&=\langle b_j,b_k\rangle,
\qquad j\in\Omega_f.
\end{aligned}\tag{110.1}
$$

Inner products are conjugate-linear in the first argument. These Grams satisfy $0\preceq G_{ff},H_{ff}\preceq I_2$ even with original output leakage. Write

$$
\delta(A,B)=\|(A\otimes B)\circ J_{\rm in}
                   -J_{\rm out}\circ\mathcal F\|_\diamond
\tag{110.2}
$$

for the unhalved diamond error, with arbitrary reference systems. For any complex matrix $M$ indexed by $\Omega$, define its fibre-preserving permutation symmetry group by

$$
\operatorname{Aut}_{\rm fib}(M)
 =\{\pi\in\operatorname{Sym}(\Omega):
       \pi\text{ preserves the fibre partition},\quad
       M_{\pi(j),\pi(k)}=M_{jk}\text{ for all }j,k\}.
\tag{110.3}
$$

**Theorem 110.1.** If $\operatorname{Aut}_{\rm fib}(G)$ or $\operatorname{Aut}_{\rm fib}(H)$ acts transitively on $\Omega$, then

$$
\delta(A,B)\geq\sqrt2-1>\frac14.
\tag{110.4}
$$

The opposite channel may be arbitrary and both channels may leak. The bound is sharp in this transitive-symmetry class, attained by a calibrated pair of local Kraus ranks $(3,3)$. Its infimum in each calibrated exact-rank class $(7,4)$ and $(7,5)$ with a unique full-support first kernel is also $\sqrt2-1$. The conclusion continues to hold if the stated symmetry appears after an original fibre-preserving relabeling and reciprocal diagonal unitary phases.

The proof will produce a regular subgroup of the same matrix's full fibre-preserving symmetry group. It does not require a regular subgroup of an initially specified transitive subgroup. No positivity or Hermiticity will be needed for this finite matrix step.

### 110.2. The two-group and its four-fibre action

**Proof of Theorem 110.1.** Let $M$ be a complex matrix invariant under a transitive fibre-preserving permutation group $\mathcal A$. Since $\Omega$ is finite, $\mathcal A$ is finite. Choose a Sylow two-subgroup $P\leq\mathcal A$. If $|\mathcal A|=2^v m$ with $m$ odd, the point stabilizer has order $2^{v-3}m$. Thus, for every $x\in\Omega$,

$$
|P\cap\mathcal A_x|\leq 2^{v-3},\qquad
|P\cdot x|=\frac{|P|}{|P\cap\mathcal A_x|}\geq8.
\tag{110.5}
$$

The orbit has exactly eight elements, so $P$ is transitive. This uses the standard Sylow and orbit-stabilizer theorems, without imposing a condition on which Sylow subgroup is chosen.

Label a coordinate by $(f,b)\in\{0,1,2,3\}\times\mathbb F_2$. Every fibre-preserving permutation has the form

$$
(f,b)\longmapsto(\pi(f),b+k_f).
\tag{110.6}
$$

Let $F$ be the image of $P$ on the four fibres and $K$ the kernel. Then $F$ is a transitive two-subgroup of $S_4$, while $K$ is a linear subspace of $\mathbb F_2^4$, acting by within-fibre flips. Conjugation induces the ordinary permutation of the four flip coordinates. The order of $F$ is four or eight. At order four its action is regular and its group is $C_4$ or $C_2^2$. At order eight it is a Sylow two-subgroup of $S_4$, hence conjugate to the square-dihedral group. In particular, $F$ contains a regular subgroup $F_0$ of order four; unless $F=C_2^2$, it contains a four-cycle.

Suppose $K\ne0$. For each fibre let $\ell_f:K\to\mathbb F_2$ be its coordinate functional. Every $\ell_f$ is nonzero: otherwise transitivity of $F$ would make all of them zero and force $K=0$. Equality of two such functionals defines an $F$-invariant equivalence relation on the four fibres. All its classes have the same size, so the number of distinct functionals is one, two or four. The functionals span the dual space $`K^*`$ because the coordinate inclusion of $K$ in $\mathbb F_2^4$ is injective.

Write $c=(1,1,1,1)$ for the global flip. It is central in the entire fibre-preserving permutation group.

### 110.3. Kernels of dimension at most two

If $K=0$, then $|P|=|F|\leq8$. Transitivity forces $|P|=8$, so $P$ itself is regular.

If $\dim K=1$, the four nonzero functionals coincide, so $K=\langle c\rangle$. The inverse image of a regular $F_0\leq F$ has order eight. Its image is transitive on fibres and $c$ interchanges the two coordinates in each fibre. It is therefore transitive and regular on $\Omega$.

Suppose $\dim K=2$. There are only three nonzero functionals on $K$. The number of distinct coordinate functionals can neither be four nor be one, since they span $`K^*`$. Hence two distinct functionals occur, each on two fibres. Call these two fibre pairs $A_0,A_1$. Distinct nonzero functionals over $\mathbb F_2$ are independent. Consequently $K$ consists exactly of the independent simultaneous flips $k_0,k_1$ on $A_0,A_1$, and $c=k_0k_1\in K$. The image $F$ permutes the two pairs transitively.

If $F$ contains a four-cycle, choose a lift $g\in P$. It interchanges $A_0,A_1$, so conjugation by $g$ interchanges $k_0,k_1$. Since $g^4\in K$ commutes with $g$,

$$
g^4\in\{e,c\}.
\tag{110.7}
$$

If $g^4=c$, then $g$ has order eight. Its projected cycle visits all four fibres, and its fourth power flips each fibre, so $\langle g\rangle$ is transitive and regular. If $g^4=e$, then $g$ has order four and $c\notin\langle g\rangle$, since each nonidentity power of $g$ has nonidentity projection. Thus $\langle g,c\rangle$ has order eight and is transitive, hence regular.

It remains to treat $F=C_2^2$. Its nonidentity element $u$ preserving both $A_0,A_1$ swaps the two fibres within each pair. Choose $v\in F$ interchanging the pairs, and choose arbitrary lifts $U,V\in P$. Then $U$ centralizes $K$, while $V$ interchanges $k_0,k_1$. Denote this interchange automorphism of $K$ by $\sigma$.

Both $U^2$ and $V^2$ lie in $K$. Since $V^2$ commutes with $V$, it is fixed by $\sigma$ and lies in $\langle c\rangle$. The abelian quotient gives $VUV^{-1}=Uk$ for some $k\in K$. Squaring and using that $U$ centralizes the exponent-two group $K$ gives

$$
VU^2V^{-1}=(Uk)^2=U^2.
\tag{110.8}
$$

Hence $U^2$ is also fixed by $\sigma$ and lies in $\langle c\rangle$. As $V^2$ is central, conjugation twice yields

$$
U=V^2UV^{-2}=Uk\sigma(k).
\tag{110.9}
$$

Therefore $k=\sigma(k)\in\langle c\rangle$. The squares of $U,V$ and their commutator all belong to the central group $\langle c\rangle$. Every element of $R=\langle U,V,c\rangle$ consequently has a normal form

$$
c^aU^bV^d,\qquad a,b,d\in\{0,1\}.
\tag{110.10}
$$

Thus $|R|\leq8$. Its image in $F$ has order four and its kernel contains the nontrivial $c$, giving $|R|\geq8$. Its image is transitive on the fibres and $c$ flips every fibre, so $R$ is regular. In all cases of this subsection the constructed subgroup is already contained in $P$ and preserves $M$.

### 110.4. Larger kernels and the same matrix's enlarged symmetry

Suppose $\dim K\geq3$. The coordinate functionals span $`K^*`$, so the number of distinct functionals cannot be one or two. All four are distinct. Any two distinct nonzero functionals over $\mathbb F_2$ are independent, and therefore for different fibres $f,g$ the map

$$
K\longrightarrow\mathbb F_2^2,\qquad
k\longmapsto(k_f,k_g)
\tag{110.11}
$$

is onto. Invariance of $M$ under $K$ forces the four entries in every cross-fibre block $M_{fg}$ to be equal: the row and column coordinate can be flipped independently. Each diagonal fibre block is invariant under its within-fibre flip because $\ell_f\ne0$. These diagonal blocks all coincide, by transitivity on the fibres; transporting a flip-invariant block is unaffected by the within-fibre swap in the chosen lift.

It follows that every independent within-fibre flip preserves $M$. Moreover, every pure fibre permutation from $F$, with all flip bits zero, preserves $M$. Indeed choose a lift in $P$ and remove its within-fibre flips, which have just been shown to preserve the same matrix. Equivalently, constant cross-fibre blocks and equal flip-invariant diagonal blocks make this removal immediate. These statements apply to directed complex entries and do not insert any conjugation.

Choose a regular $F_0\leq F$ of order four. Its pure fibre action, together with the global flip, gives

$$
R=F_0\times\langle c\rangle
       \leq\operatorname{Aut}_{\rm fib}(M),\qquad |R|=8.
\tag{110.12}
$$

This group is transitive on the fibres and on both coordinates in each fibre. Hence it acts freely and transitively on $\Omega$. This proves in every case that the full fibre-preserving symmetry of the original matrix contains a regular order-eight subgroup. The construction in (110.12) need not stay inside the originally given $P$ or $\mathcal A$; the invariant matrix itself has not changed.

### 110.5. The original complete norm and sharpness

Apply the finite matrix argument to the transitive correct-output Gram in Theorem 110.1. It supplies a regular order-eight symmetry of that same Gram and of the same original four-fibre partition. Corollary 109.3 now gives (110.4).

In particular, the argument does not replace the original channels by an averaged pair. The calibrated one-party consumer fixes the invariant Gram, and only its opposite is averaged when estimating the convex arbitrary-reference objective. For leaking original channels the completion from §§107–109 is

$$
\mathcal C(G)=G+\bigoplus_f(I_2-G_{ff}),\qquad
\mathcal C(H)=H+\bigoplus_f(I_2-H_{ff}).
\tag{110.13}
$$

This completion preserves every fibre-preserving permutation symmetry of its argument. The tagged-reference lower bound and positive Schur order give the original inequality

$$
\delta(A,B)\geq \mathcal B(T-G\odot H)
                \geq F(\mathcal C(G),\mathcal C(H))
                \geq\sqrt2-1,
\tag{110.14}
$$

with the definitions and original normalization of RT III §91. No rank-preservation assertion about this completion is used. Reciprocal diagonal unitary phases leave the physical product coefficients unchanged, and fibre-preserving relabelings simultaneously reindex the target and product. Thus the stated sufficient gauge condition inherits the same conclusion; it does not assert that arbitrary monomial symmetry actions admit such a gauge.

The calibrated cyclic attainer in Theorem 107.1 has ranks $(3,3)$, belongs to this transitive-symmetry class and attains $\sqrt2-1$. The exact-rank cyclic approximation families in that theorem have ranks $(7,4)$ and $(7,5)$, a unique full-support first kernel, and errors tending to $\sqrt2-1$. They give the upper infima in these subclasses, while (110.4) gives the matching lower bound. These are infima in the union of transitive symmetry classes; they do not assert sharpness of the noncentral dihedral subclass alone.

The assumption that one original Gram has a transitive fibre-preserving symmetry is substantive. No averaging of a generic pair into this class, no common-stress or local-minimum property of the approximation families, and no unrestricted global-quarter conclusion follows. This completes the proof.

## 追加锚（本行以下为增补区）

## 111. Spectral parity in the original monomial-symmetry obstruction

### 111.1. Original channels and monomial symmetry

Retain the original channels, four two-coordinate fibres, correct-output forward Grams $G,H$, fixed correlated encodings and unhalved arbitrary-reference diamond error $\delta(A,B)$ of §110.1. For a permutation $\pi$ of the eight coordinates, use $P_\pi e_j=e_{\pi(j)}$. A monomial unitary has the form

$$
Ue_j=u_j e_{\pi(j)},\qquad |u_j|=1.
\tag{111.1}
$$

It preserves the original fibres when $\pi$ preserves their partition. A group $\mathcal U$ of such matrices is a monomial symmetry group of a Hermitian matrix $M$ when $`U^*MU=M`$ for every $U\in\mathcal U$. Its permutation image is finite even if $\mathcal U$ is infinite.

**Theorem 111.1.** Suppose that one of the actual correct-output Grams $M\in\{G,H\}$ has a fibre-preserving monomial symmetry group with transitive permutation image. If any eigenvalue of $M$ has odd multiplicity, then

$$
\delta(A,B)\geq\sqrt2-1>\frac14.
\tag{111.2}
$$

In particular, the conclusion holds if $\operatorname{rank}M$ is odd, or if $M$ has a simple eigenvalue. The other original channel is arbitrary, and either channel may leak. With leakage, $\operatorname{rank}M$ denotes the rank of the actual correct-output Gram and need not equal the channel's local Kraus rank.

The constant is sharp in this class. It is attained by a calibrated rank-$(3,3)$ pair, and it is the infimum in the calibrated exact-rank classes $(7,4)$ and $(7,5)$ described in §107. Thus a pair in the stated monomial-symmetry class with error below $\sqrt2-1$ must have even multiplicity for every eigenvalue of $M$, including zero.

### 111.2. Connected support and a finite central extension

**Proof of Theorem 111.1.** It suffices to rule out $\delta<\sqrt2-1$. For original coordinates $j,k$ in different fibres, the matrix unit $|j\rangle\langle k|$ has trace norm one. Compressing its full output error to the correct-output entry gives

$$
\left|\frac12-G_{jk}H_{jk}\right|\leq\delta.
\tag{111.3}
$$

The physical coefficient is the conjugate of the forward product, which leaves this modulus unchanged. All wrong-output components remain in the full channel before compression; no calibration is used. Because $\sqrt2-1<1/2$, every cross-fibre entry of $G$ and $H$ is nonzero under the supposed strict inequality. In particular the support graph of $M$, with an edge whenever $j\ne k$ and $M_{jk}\ne0$, is connected.

For a diagonal unitary $Z=\operatorname{diag}(z_j)$ preserving $M$, the entrywise equation $`Z^*MZ=M`$ gives $\overline{z_j}z_k=1$ on every support edge. Connectedness therefore makes $Z$ scalar. This argument permits arbitrary complex entries and uses no positive or real gauge.

Let $F$ be the transitive permutation image of $\mathcal U$, and let $P$ be a Sylow two-subgroup of $F$. For a coordinate $x$, orbit-stabilizer gives

$$
|P\cdot x|
 =\frac{|P|}{|P\cap F_x|}
 \geq\frac{|F|_2}{|F_x|_2}=8,
\tag{111.4}
$$

where $|K|_2$ is the largest power of two dividing $|K|$. The orbit has at most eight elements, so $P$ is transitive. Every element still preserves the original fibres.

Define $E$ to be the group of all monomial unitary symmetries of $M$ whose permutation lies in $P$ and whose determinant is one. This uses the full matrix stabilizer; scalar multiples of the originally supplied lifts are allowed. Every $\pi\in P$ has a lift, and multiplication by a unit scalar can make its determinant one. Two lifts of the same permutation differ by a diagonal symmetry, hence by a scalar. Exactly eight scalar multiples of a fixed lift have determinant one. Consequently

$$
|E|=8|P|,\qquad
\ker(E\longrightarrow P)=\{\zeta I_8:\zeta^8=1\}.
\tag{111.5}
$$

Thus $E$ is a finite two-group. No compatible section of the permutation map, splitting of a projective extension, or finiteness of the original group $\mathcal U$ was assumed.

### 111.3. An odd eigenspace contains a common line

The needed representation-theoretic step is the standard fact that an odd-dimensional complex unitary representation of a finite two-group contains an invariant line. It is a special case of the classical irreducible-degree divisibility theorem; see [Teleman, Theorem 13.6](../../../Library/FiniteGroups/teleman2005representation.md). The following elementary argument supplies the exact step within this proof.

Induct on group order to show that an odd-dimensional irreducible unitary representation has dimension one. The trivial group is immediate. A nontrivial finite two-group has a normal subgroup $N$ of index two. This elementary maximal-subgroup property also follows by induction through a central subgroup of order two. Restrict an odd-dimensional irreducible representation $V$ to $N$ and decompose it orthogonally into $N$-isotypic components. An element $g$ outside $N$ permutes these components. Since $g^2\in N$, its orbits have size one or two. The sum over each orbit is invariant under $N$ and $g$, hence under the whole group. Irreducibility leaves exactly one orbit. A two-element orbit would consist of equal-dimensional components and make $\dim V$ even. Thus $V$ is a single $N$-isotypic component, a sum of copies of an irreducible $N$-module $W$.

Since $\dim V$ is odd, $\dim W$ is odd. Induction gives $\dim W=1$, so $N$ acts by scalars on $V$. Any eigenvector of the unitary representing $g$ then spans a line invariant under $N$ and $g$. Irreducibility forces $\dim V=1$. Finally, an arbitrary odd-dimensional unitary representation decomposes into irreducible orthogonal summands; at least one has odd dimension and is therefore a line. This proves the required step without a classification of the two-group.

Let $\lambda$ be an eigenvalue of $M$ with odd multiplicity. Every element of $E$ commutes with $M$, so its $\lambda$ eigenspace is an odd-dimensional unitary representation of $E$. Choose a nonzero vector $a$ on a common invariant line. For every $U\in E$ there is a unit scalar $\chi(U)$ with

$$
Ua=\chi(U)a,\qquad
u_j a_j=\chi(U)a_{\pi(j)},
\quad Ue_j=u_j e_{\pi(j)}.
\tag{111.6}
$$

Transitivity of $P$ forces all coordinate moduli to equal a single $r>0$. In particular, none is zero. Set

$$
D=\operatorname{diag}(a_j/r).
\tag{111.7}
$$

This is one diagonal unitary, independent of the lift or permutation. Equation (111.6) yields

$$
D^*UD=\chi(U)P_\pi,\qquad
P_\pi^*(D^*MD)P_\pi=D^*MD.
\tag{111.8}
$$

Thus the gauged matrix has a transitive pure-permutation symmetry group preserving the original fibres. Only the subgroup with image $P$ is asserted to have this common gauge; it need not remove the phases of every element of $\mathcal U$.

When the eigenvalue is simple, the same argument is shorter and works for the entire supplied group: every $U\in\mathcal U$ preserves its unique eigenline, so (111.6)–(111.8) hold directly for all of $\mathcal U$. In particular, rank seven gives a unique kernel line, and transitivity forces that kernel vector to have equal nonzero coordinate moduli. Full kernel support is then a conclusion, rather than an additional hypothesis.

### 111.4. The complete physical gauge and sharpness

Assume first that $M=G$. Precompose the original channels by reciprocal diagonal phases:

$$
A'=A\circ\operatorname{Ad}_D,\qquad
B'=B\circ\operatorname{Ad}_{\overline D},\qquad
G'=D^*GD,\qquad H'=D^T H\overline D.
\tag{111.9}
$$

Every Stinespring column is phased, including every wrong-output component. On each logical matrix unit $|j\rangle\langle k|$, the complete local outputs acquire factors $d_j\overline{d_k}$ and $\overline{d_j}d_k$, whose product is one. Equivalently,

$$
(D\otimes\overline D)V_{\rm in}=V_{\rm in}.
\tag{111.10}
$$

The entire encoded physical product channel, and hence its arbitrary-reference diamond error, is unchanged. If $M=H$, exchange the two phase assignments. Theorem 110.1 now applies to the gauged pair and gives (111.2), contradicting the supposed smaller error. If $\operatorname{rank}M$ is odd, the sum of the multiplicities of its nonzero eigenvalues is odd, so at least one such multiplicity is odd. This proves the rank assertion.

For sharpness, the cyclic attainer of §107.4 has first-Gram Fourier weights $1/2,m/2,(1-m)/2$, where $m=1/\sqrt2$, on modes $0,1,3$. Its three positive eigenvalues are

$$
4,\qquad 2\sqrt2,\qquad 4-2\sqrt2,
\tag{111.11}
$$

all simple, and its original error is $\sqrt2-1$. Its pure-permutation symmetry is a special case of monomial symmetry. The calibrated approximating families of §107.5 have exact first rank seven, unique full-support Fourier kernel and exact opposite ranks four or five. Their errors converge to the same constant. This establishes the claimed sharp value and rank-class infima, without asserting attainment or local minimality for those approximating families. $\square$

### 111.5. An exact even-multiplicity boundary at quarter error

**Proposition 111.2.** There are original calibrated channels of local Kraus ranks $(4,2)$ and exact error $1/4$ for which the second Gram has a transitive fibre-preserving monomial symmetry group. That Gram has spectrum $4$ with multiplicity two and $0$ with multiplicity six. Consequently the odd-multiplicity condition in Theorem 111.1 cannot be discarded.

**Proof.** Let $X,Y,Z$ be the Pauli matrices and set

$$
\begin{aligned}
n_0&=(1,1,1)/\sqrt3,&n_1&=(1,-1,-1)/\sqrt3,\\
n_2&=(-1,1,-1)/\sqrt3,&n_3&=(-1,-1,1)/\sqrt3.
\end{aligned}\tag{111.12}
$$

Choose an orthonormal qubit basis $(b_{f0},b_{f1})$ whose rank-one projectors are

$$
|b_{fi}\rangle\langle b_{fi}|
 =\frac{I_2+(-1)^i n_f\cdot(X,Y,Z)}2.
\tag{111.13}
$$

Use the tetrahedral marker construction of [RT II §82](ARITHMETIC_HOLOGRAPHIC_RT_II.md#82-quarter-error-rigidity-minimal-kraus-product-and-the-complete-rank-two-party-family):

$$
m_i=\sqrt{\frac78}e_0+(-1)^i\sqrt{\frac18}e_1,
\qquad a_{fi}=\overline{b_{fi}}\otimes m_i,
\qquad\langle m_0,m_1\rangle=\frac34.
\tag{111.14}
$$

The assignments $|f,i\rangle\mapsto|f\rangle\otimes a_{fi}$ and $|f,i\rangle\mapsto|f\rangle\otimes b_{fi}$ are full original Stinespring isometries. The second record span has dimension two. The two marker vectors are independent, and for either fixed bit the four qubit vectors span $\mathbb C^2$. Their tensor subspaces with $m_0$ and $m_1$ are independent, so the first record span has dimension four. These are the stated local Kraus ranks.

If $B_0$ is the $2\times8$ matrix of second-party records, then

$$
B_0B_0^*=\sum_{f,i}|b_{fi}\rangle\langle b_{fi}|=4I_2.
\tag{111.15}
$$

Thus its Gram $`H=B_0^*B_0`$ has exactly the asserted repeated spectrum.

To retain the original complete-norm normalization, put $R_{fg}=n_f\cdot n_g$. Its Klein-character eigenvalues are $0,4/3,4/3,4/3$. The product coefficients are

$$
K_{fi,gj}=|\langle b_{fi},b_{gj}\rangle|^2\langle m_i,m_j\rangle.
\tag{111.16}
$$

The product-minus-target difference in the logical plus/minus bit sectors has the two real Schur kernels

$$
D_+=\frac{R-J_4}{8},\qquad
D_-=\frac{J_4+7R}{8}-I_4,
\tag{111.17}
$$

and zero cross-sector terms. Each kernel has eigenvalues $-1/2,1/6,1/6,1/6$. For a Hermitian Klein-circulant kernel $D$, expansion in its real characters gives a signed sum of diagonal unitary conjugations and hence the arbitrary-reference upper bound $\|\operatorname{Schur}_D\|_\diamond\leq\|D\|_1/4$. The uniform pure input attains equality. The two positive input principal blocks have traces summing to one, so the full original norm is the larger sector norm. Therefore

$$
\delta(A,B)=\max\left\{\frac{\|D_+\|_1}{4},
                             \frac{\|D_-\|_1}{4}\right\}
             =\frac14.
\tag{111.18}
$$

It remains to verify the monomial symmetry, rather than infer it from the eigenvalue multiplicities. The Pauli $X,Z$ and the Hadamard $Q=(X+Z)/\sqrt2$ act on Bloch vectors respectively by

$$
(x,y,z)\mapsto(x,-y,-z),\quad
(x,y,z)\mapsto(-x,-y,z),\quad
(x,y,z)\mapsto(z,-y,x).
\tag{111.19}
$$

These transformations permute the eight cube vertices $\{(-1)^i n_f\}$ and preserve their original antipodal pairs. The first two act transitively on each sign-product class, and the last exchanges the two classes. The generated permutation group is therefore transitive on all eight original coordinates.

For every word $V$ in these qubit unitaries, distinctness of the eight record rays gives a permutation $\pi$ and unit scalars $\zeta_j$ such that $Vb_j=\zeta_jb_{\pi(j)}$. Define $U_Ve_j=\zeta_je_{\pi(j)}$. Then

$$
B_0U_V=VB_0,\qquad U_V^*HU_V=H.
\tag{111.20}
$$

Composition of words gives composition of these monomial matrices, so they form the required group. Changing the individual record phases only diagonally conjugates it. Thus the same actual quarter-error product has transitive monomial symmetry and only even spectral multiplicities. By Theorem 110.1, this $H$ cannot have any diagonal gauge with transitive fibre-preserving pure-permutation symmetry. $\square$

Theorem 111.1 constrains a symmetry class of actual original Grams. It does not assert such symmetry for arbitrary channels or calibrated minima, and Proposition 111.2 is not a subquarter example. The unrestricted global quarter optimum remains open.

## 追加锚（本行以下为增补区）

## 112. Full-kernel curvature exclusions beyond the symmetry classes

### 112.1. Original local minima and one fixed quadratic

Use the original eight logical coordinates, four two-coordinate fibres, local channels from $\mathbb C^8$ to $\mathbb C^4$, and fixed correlated encoding. In this section the channels are calibrated, and their forward Grams belong to

$$
\mathcal E=\{M=M^*\succeq0:M_{ff}=I_2\text{ for every original fibre }f\}.
\tag{112.1}
$$

The target has $T_{ff}=I_2$ and $T_{fg}=J_2/2$ for $f\ne g$. The exact unhalved error, including arbitrary reference inputs, is the block-density norm of [RT III §91](ARITHMETIC_HOLOGRAPHIC_RT_III.md#91-adaptive-original-channel-witnesses-and-an-obstruction-to-all-two-fibre-tests):

$$
\begin{aligned}
F(G,H)&=\max 2\operatorname{Tr}[(T-G\odot H)W],\\
\rho&=\bigoplus_f\rho_f\succeq0,\qquad
\operatorname{Tr}\rho=1,\qquad0\preceq W\preceq\rho.
\end{aligned}
\tag{112.2}
$$

Local minimality always means the full domain $\mathcal E\times\mathcal E$, including nearby competitors of different ranks. Suppose $\operatorname{rank}G=7$, $\ker G=\mathbb Ca$ with every $a_i\ne0$, and $0<F(G,H)<1/2$. The common-stress and full-kernel results of RT III §§92 and 95.3 give

$$
\begin{aligned}
P_A&=\alpha aa^*,&
P&=\alpha\operatorname{diag}(a)R\operatorname{diag}(\bar a),\\
\alpha&>0,&R&\succeq0,\quad R_{ii}=1,\\
G&=H\odot\bar R,&PH&=0.
\end{aligned}
\tag{112.3}
$$

Every cross-fibre entry of $G,H,R,P$ is nonzero. Indeed the original matrix-unit bound $|1/2-G_{ij}H_{ij}|\leq F<1/2$ first gives this for $G,H$, and (112.3) gives it for $R,P$. Also $P_{ii}=\alpha|a_i|^2>0$.

Let $U$ have full row rank and $`\operatorname{range}U^*=\ker H`$. Define

$$
\mathcal V_H=\{D=D^*:D_{ff}=0\text{ for all }f,\ DU^*=0\}.
\tag{112.4}
$$

The necessary quadratic on this entire-kernel face is

$$
Q_P(D)=-\sum_{\substack{i,j\text{ in distinct}\\\text{original fibres}}}
 \frac{\overline{P_{ij}}}{H_{ij}}D_{ij}^{2}\geq0
 \qquad(D\in\mathcal V_H).
\tag{112.5}
$$

The sum is over ordered pairs, and the square is a complex entrywise square. To retain the exact scope of the delivered argument, the paired direction is $D_G=-\bar R\odot D$. It has zero entire fibre blocks, annihilates $a$, and satisfies $D_G\odot H+G\odot D=0$. Both fixed-kernel face paths are feasible for sufficiently small real parameters of either sign. Their coefficient expansion is

$$
T-(G+sD_G)\odot(H+sD)
 =T-G\odot H+s^2\bar R\odot D\odot D.
\tag{112.6}
$$

For each fixed direction, the common-witness drift argument supplies a nonnegative quadratic value. All common witnesses at these same $G,H,a$ give positive scalar multiples of the same form, because their cross-fibre $R$ entries are fixed. Thus one obtains (112.5) for all directions with the same chosen $P$. No exchange of a quadratic direction variable with a witness maximum is used. Annihilating only the complementary-stress range instead of the entire $\ker H$ would not justify these face paths.

### 112.2. Two rank-one full-kernel projections are impossible

**Theorem 112.1.** Under the local-minimum hypotheses of §112.1, at most one original fibre can satisfy $\operatorname{rank}U_f=1$. There is no restriction on the opposite rank beyond the original Gram constraints.

**Proof.** Suppose two distinct fibres $f,g$ have rank-one blocks, and let $C$ be their four-coordinate complement. Every column of $U$ is nonzero, because $P_{ii}>0$ and $`\operatorname{range}P\subseteq\operatorname{range}U^*`$. Choose nonzero vectors $n,m$, supported on $f,g$ respectively, with $Un=Um=0$. Both original coordinates of each are nonzero.

First suppose $\operatorname{rank}U_C=\operatorname{rank}U$. For $v\in\ker U$ with $v_f=0$ and $z\in\mathbb C$, the matrix

$$
S_f(z,v)=znv^*+\bar z vn^*
\tag{112.7}
$$

belongs to $\mathcal V_H$. Substitution in (112.5) gives $Q_P(S_f(z,v))=-2\operatorname{Re}(z^2A(v))$ for a fixed complex number $A(v)$. All phases of $z$ force $A(v)=0$. A zero vector of a nonnegative real quadratic lies in its radical: applying the quadratic to $S+uD$ for both signs of real $u$ makes its linear term vanish. Consequently all stars (112.7), and their counterparts at $g$, are radical vectors.

For arbitrary vectors $p$ on $f$ and $r$ on $g$, surjectivity of $U_C$ supplies $v,w\in\ker U$ with $v_f=0,v_g=r,w_g=0,w_f=p$. The two stars share only the block $f\times g$ and its adjoint. Their zero polarization gives

$$
\operatorname{Re}\left[
 z\bar y\sum_{i\in f,j\in g}
 \frac{\overline{P_{ij}}}{H_{ij}}
 n_i p_i\bar r_j\bar m_j\right]=0
 \qquad(z,y\in\mathbb C).
\tag{112.8}
$$

Varying the phase and taking $p,r$ to be individual coordinate vectors contradicts the nonzero entries of $P,n,m$.

It remains to treat $\operatorname{rank}U_C<\operatorname{rank}U$. Choose a nonzero $\ell$ orthogonal to the columns of $U_C$. Then

$$
w=U^*\ell\ne0,\qquad w_C=0,\qquad Hw=0.
\tag{112.9}
$$

Choose unit vectors $m_f,m_g$ spanning $`\operatorname{range}U_f^*,\operatorname{range}U_g^*`$, and unit orthogonal vectors $n_f,n_g$ in their original fibres. The latter lie in $\operatorname{range}H$. Write $w_f=\eta_fm_f,w_g=\eta_gm_g$. Both coefficients are nonzero: a kernel vector supported in just one fibre would contradict $H_{ff}=I_2$. The two block rows of $Hw=0$ give

$$
H_{fg}m_g=-\frac{\eta_f}{\eta_g}m_f,
\qquad
H_{fg}^*m_f=-\frac{\eta_g}{\eta_f}m_g.
\tag{112.10}
$$

Taking their adjoint scalar pairings shows $|\eta_f/\eta_g|=1$. Hence this is a singular pair of singular value one. The mixed entries in these orthonormal bases vanish, so

$$
H_{fg}=b\,n_fn_g^*+\lambda m_fm_g^*,
\qquad |\lambda|=1,\quad |b|\leq1.
\tag{112.11}
$$

In fact $|b|<1$. If $|b|=1$, $H_{fg}$ is unitary and the four-coordinate principal block with diagonal blocks $I_2$ has a two-dimensional kernel whose projection onto $f$ spans $\mathbb C^2$. Every principal null vector of a positive matrix extends by zero to a full null vector: its full quadratic value is zero, so the positive square root annihilates it. This would give a two-dimensional projection of $\ker H$ onto $f$, contradicting $\operatorname{rank}U_f=1$.

Absorb $\lambda$ into the choice of $m_g$. Since $P$ is supported on the full kernel, its cross block is

$$
H_{fg}=b\,n_fn_g^*+m_fm_g^*,\qquad
P_{fg}=\zeta m_fm_g^*,\qquad
|b|<1,\quad\zeta\ne0.
\tag{112.12}
$$

Both coordinates of $m_f,m_g$ are nonzero by the positive diagonal of $P$. Simultaneous diagonal unitary congruence $`H\mapsto E^*HE`$, $`P\mapsto E^*PE`$, $`D\mapsto E^*DE`$ preserves each summand in (112.5). The reciprocal first-Gram transformation $`G\mapsto EGE^*`$ preserves every entry of $G\odot H$ and all original identity fibre blocks, so these phases also preserve the original physical objective. Use them to write

$$
m_f=(c,s)^{\mathsf T},\quad n_f=(-s,c)^{\mathsf T},\qquad
m_g=(d,e)^{\mathsf T},\quad n_g=(-e,d)^{\mathsf T},
\tag{112.13}
$$

where $c,s,d,e>0$, $c^2+s^2=d^2+e^2=1$. The phases of the orthogonal vectors are analytical choices, absorbed into the possibly complex coefficient $b$. No arbitrary fibre-unitary symmetry of the physical encoding, or real gauge for the Grams, is assumed.

The star $`D(z)=zn_fn_g^*+\bar z n_gn_f^*`$ lies in $\mathcal V_H$. Put $t=s/c>0,u=e/d>0$. Direct substitution gives

$$
\begin{aligned}
Q_P(D(z))&=-2\operatorname{Re}\bigl(z^2\bar\zeta\,K(b;t,u)\bigr),\\
K(b;t,u)&=\sum_{i,j=0}^1
\frac{(m_f)_i(m_g)_j(n_f)_i^2(n_g)_j^2}
 {b(n_f)_i(n_g)_j+(m_f)_i(m_g)_j}\\
&=\frac{t^2u^2(b^2-1)}
 {(b+tu)(bt-u)(t-bu)(btu+1)}.
\end{aligned}
\tag{112.14}
$$

For the last identity, the ratios $n_i/m_i$ are $(-t,1/t)$ and $(-u,1/u)$, with weights $n_i^2=(t^2,1)/(1+t^2)$ and $(u^2,1)/(1+u^2)$. Taking the common denominator of their four terms proves the identity for arbitrary complex $b$. The opposite ordered block supplies the conjugate term, so no conjugation is inserted into $b$ itself.

All four denominator factors are nonzero because they are the four actual cross entries of $H_{fg}$ divided by nonzero factors. The numerator is nonzero since $|b|<1$ and $t,u>0$. All phases of $z$ in (112.14) therefore contradict (112.5) and $\zeta\ne0$. This completes both branches. ∎

### 112.3. A partition-radical criterion at opposite rank five

Assume now that $H\in\mathcal E$ has rank five and all cross-fibre entries nonzero. Take $U$ with three rows and $`\operatorname{range}U^*=\ker H`$. Fix the two unions of original fibres

$$
A=\{0,1,2,3\},\qquad B=\{4,5,6,7\}.
\tag{112.15}
$$

Suppose $U_A,U_B$ have rank three. Choose nonzero supported vectors $n,m$ with $n_B=m_A=0$ and $Un=Um=0$. Define $`S(z)=znm^*+\bar z mn^*`$. These matrices lie in $\mathcal V_H$, because their only edges join distinct sets of original fibres.

For any Hermitian $P$ supported on $\ker H$, define $Q_P$ by the expression in (112.5), without assuming its positivity, and let

$$
\mathcal B_P(D,E)=-\operatorname{Re}\sum_{\mathrm{cross}}
 \frac{\overline{P_{ij}}}{H_{ij}}D_{ij}E_{ij}.
\tag{112.16}
$$

Its restriction to the star plane is

$$
Q_P(S(z))=-2\operatorname{Re}\left[
 z^2\sum_{i\in A,j\in B}
 \frac{\overline{P_{ij}}}{H_{ij}}n_i^2\bar m_j^{2}\right].
\tag{112.17}
$$

Thus, if $Q_P$ is nonnegative on $\mathcal V_H$, both $S(1)$ and $S(i)$ belong to its radical. Every such $P$ is uniquely $`P=U^*XU`$ with $X\in\operatorname{Herm}(3)$. Introduce the real linear map

$$
\begin{aligned}
\mathcal L_H:\operatorname{Herm}(3)&\longrightarrow
 \mathcal V_H^*\oplus\mathcal V_H^*,\\
X&\longmapsto
 \bigl(\mathcal B_{U^*XU}(S(1),\cdot),
       \mathcal B_{U^*XU}(S(i),\cdot)\bigr).
\end{aligned}
\tag{112.18}
$$

Injectivity does not depend on the basis $U$, on the nonzero choices of $n,m$, or on a real basis of $\mathcal V_H$. Changing $U$ gives an invertible congruence on $X$. Rescaling $n,m$ gives an invertible real change of the two star generators.

**Proposition 112.2.** If $\mathcal L_H$ is injective, $H$ cannot occur as the opposite Gram of a local minimum satisfying §112.1.

**Proof.** Its nonzero common stress $`P=U^*XU`$ would satisfy (112.5). Equation (112.17) puts both star generators in its radical, giving $\mathcal L_H(X)=0$. Injectivity forces $P=0$, contradicting its positive diagonal. The same fixed quadratic is used in both equations. ∎

### 112.4. A rational rank-nine certificate

**Proposition 112.3.** There is a rational calibrated rank-five Gram $H_0$ with nonzero cross-fibre entries, all four $U_f$ of rank two, $\dim_{\mathbb R}\mathcal V_{H_0}=9$, and injective $\mathcal L_{H_0}$. It also admits a calibrated rank-seven partner $G_0$ with a full-support kernel and a rank-two correlation quotient $R_0$ satisfying $G_0=H_0\odot R_0$.

**Proof.** The following construction gives all these properties. For a nonzero real five-vector set $Q(v)=I_5-2vv^{\mathsf T}/(v^{\mathsf T}v)$, and take

$$
\begin{aligned}
v_0&=(1,2,3,1,2)^{\mathsf T},&
v_1&=(2,1,1,3,-1)^{\mathsf T},\\
v_2&=(1,3,-2,1,2)^{\mathsf T},&
v_3&=(3,-1,2,2,1)^{\mathsf T}.
\end{aligned}
\tag{112.19}
$$

Form the real $5\times8$ matrix $B_0$ from columns $(0,1)$ of $Q(v_0)$, $(1,2)$ of $Q(v_1)$, $(2,3)$ of $Q(v_2)$ and $(3,4)$ of $Q(v_3)$, in that order. Each original pair is orthonormal. Hence $H_0=B_0^{\mathsf T}B_0\in\mathcal E$. Every cross-fibre entry is nonzero, and

$$
\det(H_0)_{\{0,1,2,3,4\}}=\frac{5929}{130321}>0.
\tag{112.20}
$$

It has rank five. A full kernel matrix is

$$
U=\begin{bmatrix}
\dfrac57&-\dfrac{771}{616}&\dfrac{1327}{616}&\dfrac{81}{616}&-\dfrac{661}{616}&1&0&0\\[4pt]
\dfrac{135}{133}&-\dfrac{10975}{11704}&\dfrac{11595}{11704}&\dfrac{6709}{11704}&-\dfrac{243}{616}&0&1&0\\[4pt]
\dfrac{39}{133}&\dfrac{2979}{1064}&-\dfrac{2823}{1064}&\dfrac{1223}{1064}&\dfrac{71}{56}&0&0&1
\end{bmatrix}.
\tag{112.21}
$$

Direct multiplication gives $UH_0=0$. Every original $U_f$ has rank two, while $U_A,U_B$ have rank three. Choose the supported vectors by

$$
n_A=\left(-\frac{2824}{3249},-\frac{1256}{5415},\frac{79}{855},1\right)^{\mathsf T},
\qquad
m_B=\left(-\frac{56}{71},-\frac{661}{781},-\frac{243}{781},1\right)^{\mathsf T}.
\tag{112.22}
$$

The following conventions specify the entire finite rational certificate. For $\operatorname{Herm}(k)$ use, in order, the diagonal matrix units, then $E_{ij}+E_{ji}$ for $i<j$ in lexicographic order, then $i(E_{ij}-E_{ji})$ in the same order. For $k=5$ call these $25$ matrices $A_\ell$ and put $D_\ell=B_0^{\mathsf T}A_\ell B_0$. Build the real $16\times25$ constraint matrix $C$ by first evaluating, for $f=0,1,2,3$ in order,

$$
\operatorname{Re}D_{2f,2f},\quad
\operatorname{Re}D_{2f+1,2f+1},\quad
\operatorname{Re}D_{2f,2f+1},
\tag{112.23}
$$

and then $\operatorname{Im}D_{2f,2f+1}$ for the four fibres. Its reduced-row-echelon pivot columns, starting from zero, are

$$
(0,1,2,3,4,5,6,7,8,9,10,11,15,16,17,18).
\tag{112.24}
$$

For each free column in increasing order, set that free coordinate to one and all other free coordinates to zero, solve $Cx=0$, and form $\sum_\ell x_\ell D_\ell$. This gives an ordered basis $D^{(0)},\ldots,D^{(8)}$ of the entire $\mathcal V_{H_0}$; its real dimension is nine. Let $X_t$ be the ordered basis of $\operatorname{Herm}(3)$ specified above, and set

$$
L_{9b+j,t}=\mathcal B_{U^*X_tU}(S(z_b),D^{(j)}),
\qquad z_0=1,\ z_1=i,\quad0\leq j\leq8.
\tag{112.25}
$$

Select rows $(0,1,2,3,4,5,12,13,14)$, in that order, to obtain a rational $9\times9$ matrix $M$. Its denominators are nonzero modulo the prime $1009$, and its reduction is

$$
\begin{bmatrix}
363&544&663&131&866&321&0&0&0\\
167&5&413&16&578&245&0&0&0\\
780&81&103&116&751&976&0&0&0\\
0&0&0&0&0&0&383&17&773\\
0&0&0&0&0&0&576&983&167\\
0&0&0&0&0&0&902&167&785\\
360&972&495&857&423&769&0&0&0\\
603&856&757&474&813&43&0&0&0\\
633&253&1000&387&611&963&0&0&0
\end{bmatrix},
\qquad \det M\equiv71\pmod{1009}.
\tag{112.26}
$$

Thus $\det M\ne0$ over the rationals and $\mathcal L_{H_0}$ is injective. Equations (112.19)–(112.26) specify every rational entry and operation in this certificate, and the modular determinant proves nonvanishing over the rationals.

The same $H_0$ is compatible with actual full-support rank-$(7,5)$ quotient data. Put

$$
\begin{aligned}
V&=\begin{bmatrix}1&1&2\\3&5&8\end{bmatrix}U,&P_0&=V^{\mathsf T}V,&
A_0&=\operatorname{diag}\sqrt{(P_0)_{ii}},\\
R_0&=A_0^{-1}P_0A_0^{-1},&&
G_0&=A_0^{-1}(H_0\odot P_0)A_0^{-1}.
\end{aligned}
\tag{112.27}
$$

Every diagonal $(P_0)_{ii}$ is positive and every cross-fibre $(P_0)_{ij}$ is nonzero, $P_0H_0=0$, $\operatorname{rank}P_0=2$, and $H_0\odot P_0$ annihilates $\mathbf1$. Its leading seven-coordinate principal minor is

$$
\det(H_0\odot P_0)_{\{0,\ldots,6\}}
 =\frac{7112294794815105630926273211887500169505}
 {2088963297980603103510407339950336}>0.
\tag{112.28}
$$

Thus $\operatorname{rank}(H_0\odot P_0)=7$, and $G_0,R_0$ are correlation Grams, $(G_0)_{ff}=I_2$, $G_0=H_0\odot R_0$, and $\ker G_0=\mathbb C A_0\mathbf1$ has full support. Tensoring the $H_0$ records with conjugated $R_0$ records gives the original calibrated Stinespring realization. This establishes geometric nonvacuity; no small-error or local-minimum property is asserted for this example. ∎

### 112.5. Open density on the complete complex rank-five stratum

Let $\mathcal M=V_2(\mathbb C^5)^4$ be the product of four complex Stiefel manifolds of ordered orthonormal two-frames, viewed as $5\times8$ record matrices. It is a connected real-analytic manifold: each factor is $U(5)/U(3)$. Let $\mathcal M_5$ be its open full-row-rank subset. The Gram map is onto

$$
\mathcal E_5=\{H\in\mathcal E:\operatorname{rank}H=5\}.
\tag{112.29}
$$

The fibres of this map are the free left $U(5)$ orbits. The compact group action is proper, so $\mathcal E_5$ is the corresponding real-analytic quotient. Its topology is the usual Gram-matrix topology: where a five-coordinate principal block $H_{JJ}$ is positive definite, the local section $B(H)=H_{JJ}^{-1/2}H_{J,:}$ is real analytic and satisfies $`B(H)^*B(H)=H`$ by the rank-five Schur complement. Its original two-frame constraints follow from $H_{ff}=I_2$.

**Theorem 112.4.** There is an open dense subset $\Omega\subseteq\mathcal E_5$ such that no $H\in\Omega$ can be the opposite Gram of a full-domain calibrated local minimum with $\operatorname{rank}G=7$, full-support $\ker G$, and $0<F(G,H)<1/2$. One may take $\Omega$ to consist of the Grams with nonzero cross-fibre entries, $\operatorname{rank}U_A=\operatorname{rank}U_B=3$, $\dim_{\mathbb R}\mathcal V_H=9$, and injective $\mathcal L_H$.

**Proof.** All four conditions are open. Maximal-rank minors persist, and, on those open sets, continuous kernel and face bases make injectivity a full-column-rank condition. Their meanings are independent of the bases.

For density work on the connected ambient manifold $\mathcal M$, rather than assuming that its open full-rank subset is connected. Near $B_0$, use its first five columns as the invertible pivot block when solving $`BU^*=0`$. Solve $U_An_A=0$ and $U_Bm_B=0$ with the last coordinate of each vector equal to one. Use the same $16$ pivot columns (112.24) to define the face directions, now with $`D_\ell=B^*A_\ell B`$. The selected determinant in (112.25) is a rational function of the real and imaginary entries of $B$. All its denominators and the chosen pivot determinants are nonzero at $B_0$.

Complex divisions, including division by actual $H_{ij}$, can be rationalized using squared moduli. Clear the finitely many denominators and include all pivot and cross-entry nonvanishing factors in a real polynomial $p$ in $\operatorname{Re}B,\operatorname{Im}B$. By (112.26), $p(B_0)\ne0$. Its restriction to the connected real-analytic manifold $\mathcal M$ is therefore not identically zero. Such a function cannot vanish on a nonempty open set: the power-series identity theorem proves this in a coordinate ball, and overlapping balls continue the identity along paths. Hence $\{p\ne0\}$ is dense in $\mathcal M$ and in every open subset $\mathcal M_5$. Every point with $p\ne0$ has the specified admissible charts and injective determinant, so its Gram lies in $\Omega$.

If a nonempty open subset of $\mathcal E_5$ were disjoint from $\Omega$, its open, nonempty inverse image in $\mathcal M_5$ would be disjoint from $\{p\ne0\}$, a contradiction. Thus $\Omega$ is dense. Proposition 112.2 gives the exclusion on it. The density argument takes place on the complete complex frame manifold, not just the real-record slice containing $B_0$. ∎

### 112.6. Remaining local and global boundary

Theorem 112.1 leaves at most one rank-one full-kernel fibre projection at a positive subhalf rank-seven minimum. Theorem 112.4 additionally confines every remaining full-support rank-$(7,5)$ minimum to an exceptional locus whose lift is contained in the zero set of a nontrivial real polynomial. A minimum may lie on that locus. Density does not allow perturbing a minimum while retaining minimality, and gives no uniform quantitative gap.

These are restrictions on calibrated full-domain local minima with a full-support rank-seven kernel. The calibrated representative reduction of [RT II §72](ARITHMETIC_HOLOGRAPHIC_RT_II.md#72-exact-physical-calibration-reduction-for-collapsed-fibre-channels) preserves the unrestricted optimum, not arbitrary leaking ranks or local-minimum hypotheses. The residual opposite-rank-four cases, exceptional rank-five cases, both-ranks-at-most-six representatives and the global quarter-optimum question remain open.

## 追加锚（本行以下为增补区）

## 113. Curved radicals exclude a single rank-one fibre and the full rank-(7,5) class

### 113.1. The original domain and the full curved quadratic

Retain the eight original coordinates, their four two-coordinate fibres, the local channels from $\mathbb C^8$ to $\mathbb C^4$, and the fixed correlated encoding. For calibrated channels let

$$
\mathcal E=\{M=M^*\succeq0:M_{ff}=I_2\text{ for every original fibre }f\}.
\tag{113.1}
$$

Write $T_{ff}=I_2$ and $T_{fg}=J_2/2$ for $f\ne g$. The exact unhalved arbitrary-reference error is

$$
\begin{aligned}
F(G,H)&=\max 2\operatorname{Tr}[(T-G\odot H)W],\\
\rho&=\bigoplus_f\rho_f\succeq0,\qquad
\operatorname{Tr}\rho=1,\qquad0\preceq W\preceq\rho.
\end{aligned}
\tag{113.2}
$$

Throughout the exclusion arguments, assume that $(G,H)$ is a local minimum on the full domain $\mathcal E\times\mathcal E$, including nearby competitors of different ranks. Also assume

$$
\operatorname{rank}G=7,\qquad
\ker G=\mathbb Ca,\quad a_i\ne0\text{ for every }i,\qquad
0<F(G,H)<\frac12.
\tag{113.3}
$$

The common-stress and quotient results of RT III §§92 and 95.3 give a fixed common complementary stress

$$
\begin{aligned}
P_A&=\alpha aa^*,&
P&=\alpha\operatorname{diag}(a)R\operatorname{diag}(\bar a),\\
\alpha&>0,& R&\succeq0,\quad R_{ii}=1,\\
G&=H\odot\bar R,&PH&=0.
\end{aligned}
\tag{113.4}
$$

Every cross-fibre entry of $G,H,R,P$ is nonzero: the original matrix-unit bound $|1/2-G_{ij}H_{ij}|\leq F<1/2$ gives this first for $G,H$, and (113.4) gives it for $R,P$. Also $P_{ii}=\alpha|a_i|^2>0$.

Let $N$ be the orthogonal projection onto the entire $\ker H$, and let $U$ have full row rank with $`\operatorname{range}U^*=\ker H`$. The complete curved tangent space and its paired first-Gram direction are

$$
\begin{aligned}
\mathcal T_H&=\{D=D^*:D_{ff}=0\text{ for every }f,\ NDN=0\},\\
D_A&=-\bar R\odot D.
\end{aligned}
\tag{113.5}
$$

The zero fibre blocks make the definition of $D_A$ independent of the unused within-fibre ratios. By [RT III §98](ARITHMETIC_HOLOGRAPHIC_RT_III.md#98-curved-common-stress-tests-and-finite-principal-quotients), this gives an admissible paired tangent with zero full original product derivative. For the same fixed $G,H,a,P$, its necessary real quadratic is

$$
\begin{aligned}
Q_{\mathrm{curv}}(D)
 &=Q_P(D)+\alpha a^*D_AG^+D_Aa
        +\operatorname{Tr}(PDH^+D)\geq0,\\
Q_P(D)&=-\sum_{\substack{i,j\text{ in distinct}\\\text{original fibres}}}
 \frac{\overline{P_{ij}}}{H_{ij}}D_{ij}^{2}.
\end{aligned}
\tag{113.6}
$$

The sum is ordered, the squares are complex entrywise squares, and the pseudoinverses are those of the full original Grams. The delivered curved theorem selects a common normer for each fixed direction and then proves that the whole form, including both costs, is a positive scalar multiple of one fixed normalized form. Thus (113.6) holds on all of $\mathcal T_H$ with the same $P$. No exchange of quadratic direction and witness maxima is used.

### 113.2. Entire-kernel stars are radicals on the whole curved domain

**Lemma 113.1.** Under (113.3), let nonzero $n,m\in\operatorname{range}H$ be supported on disjoint unions of original fibres. For every $z\in\mathbb C$, put

$$
S(z)=z\,nm^*+\bar z\,mn^*.
\tag{113.7}
$$

Then the Hermitian matrix

$$
\mathcal A(S)_{ij}=
 \frac{P_{ij}\overline{S_{ij}}}{\overline{H_{ij}}}
 \quad\text{on cross-fibre entries},\qquad
\mathcal A(S)_{ff}=0
\tag{113.8}
$$

belongs to the real Hilbert–Schmidt annihilator of $\mathcal T_H$. Consequently, for each $z$ there are Hermitian matrices $\Lambda_z,Y_z$, with $\Lambda_z$ original-fibre-block diagonal, such that

$$
\mathcal A(S(z))=\Lambda_z+U^*Y_zU.
\tag{113.9}
$$

**Proof.** Each star has zero entire original fibre blocks and annihilates $\ker H$. For any Hermitian $S$ with these two properties, $SP=PS=0$ and

$$
(D_A(S)a)_i
 =-\frac{\sum_j\overline{P_{ij}}S_{ij}}{\alpha\bar a_i}
 =-\frac{(SP)_{ii}}{\alpha\bar a_i}=0.
\tag{113.10}
$$

The sum may include all $j$, since the original fibre-block entries of $S$ vanish. Both positive curvature costs in (113.6) are squared norms of real-linear maps. These maps vanish at $S$, so both costs and both their polarizations against every $D\in\mathcal T_H$ vanish.

For the stars (113.7), $Q_P(S(z))=-2\operatorname{Re}(z^2c)$ for a fixed complex number $c$. Nonnegativity for all phases of $z$ forces $c=0$. A zero vector $S$ of a nonnegative real quadratic lies in its radical: applying the quadratic to $S+tD$ for both signs of real $t$ forces its polarization to vanish. Removing the two cost polarizations therefore gives

$$
B_P(S,D)
 =-\operatorname{Re}\sum_{\substack{i,j\text{ in distinct}\\\text{original fibres}}}
 \frac{\overline{P_{ij}}S_{ij}D_{ij}}{H_{ij}}
 =-\operatorname{Tr}(\mathcal A(S)D)=0
 \quad(D\in\mathcal T_H).
\tag{113.11}
$$

The annihilator of the intersection of two finite-dimensional real linear kernels is the sum of the adjoint ranges. Applying this to the maps taking original fibre blocks and the compression $NDN$ gives

$$
\mathcal T_H^\perp
 =\{\Lambda+Z:\Lambda=\Lambda^*\text{ original-fibre-block diagonal},\quad
 Z=Z^*=NZN\}.
\tag{113.12}
$$

Every Hermitian $Z$ supported on $\ker H$ is $`U^*YU`$ for a Hermitian $Y$. This proves (113.9). No independence of the constraints or uniqueness of the decomposition is required. The same $P$ is retained for every star. ∎

### 113.3. One rank-one full-kernel fibre already gives a contradiction

**Theorem 113.2.** Under (113.3), every original two-column block $U_f$ has rank two, for every opposite rank $\operatorname{rank}H$.

**Proof.** Since $P$ is supported on $\ker H$ and $P_{ii}>0$, no $U_f$ has rank zero. Suppose $\operatorname{rank}U_f=1$. Choose unit vectors $m,n\in\mathbb C^2$ with $`\operatorname{range}U_f^*=\mathbb Cm`$ and $n\perp m$. Embedded on $f$, the vector $n$ satisfies $Un=0$ and therefore belongs to $\operatorname{range}H$. Both coordinates of $m$ are nonzero, because both diagonal entries of $P_{ff}$ are positive.

Diagonal reciprocal phases allow the normalization

$$
m=(c,s)^T,\qquad n=(-s,c)^T,\qquad
c,s>0,\quad c^2+s^2=1.
\tag{113.13}
$$

Explicitly, for a diagonal unitary $E$ the transformations are $`H'=E^*HE`$, $`P'=E^*PE`$, $`G'=EGE^*`$, and $`a'=Ea`$. They preserve the full original product, identity fibre blocks, norm and quadratic summands. The irrelevant phase of $n$ is then chosen as in (113.13). No arbitrary unitary change inside a physical fibre is used.

Let $C=f^c$. There is a vector $p$ on $C$ such that

$$
P_{fC}=mp^*,\qquad p_j\ne0\quad(j\in C).
\tag{113.14}
$$

Indeed the range of the $f$ rows of the kernel-supported $P$ lies in $\mathbb Cm$, and its cross entries are nonzero. Set $x=H_{Cf}m$ and $y=H_{Cf}n$. Label the two coordinates of $f$ by $0,1$. Then

$$
H_{0j}=c\bar x_j-s\bar y_j,\qquad
H_{1j}=s\bar x_j+c\bar y_j
\quad(j\in C).
\tag{113.15}
$$

For every $v\in\operatorname{range}H$ with $v_f=0$, use the star $`S=nv^*+vn^*`$. By Lemma 113.1, $\mathcal A(S)=\Lambda+Z$ with $Z=NZN$. Since $n\in\operatorname{range}H$, $Zn=0$, while $\Lambda n$ is supported on $f$. Thus $(\mathcal A(S)n)_j=0$ outside $f$. Directly from (113.8), this equation is

$$
0=\bar v_jp_j\sum_{i\in f}\frac{m_i n_i^2}{H_{ij}}
 =\bar v_jp_j\frac{cs\bar x_j}{H_{0j}H_{1j}}.
\tag{113.16}
$$

The identity used here is

$$
\frac{cs^2}{cX-sY}+\frac{sc^2}{sX+cY}
 =\frac{csX}{(cX-sY)(sX+cY)}
 \qquad(c^2+s^2=1),
\tag{113.17}
$$

valid for arbitrary complex $X,Y$ with nonzero denominators. Those denominators and $p_j$ are nonzero here. Consequently,

$$
\exists v\in\operatorname{range}H:\ v_f=0,\ v_j\ne0
 \quad\Longrightarrow\quad x_j=0.
\tag{113.18}
$$

Take a full-row-rank record factor $`H=B^*B`$, with unit columns $h_j$. Let $\mathcal F=\operatorname{span}(h_0,h_1)$ and $\mathcal W=\operatorname{span}\{h_j:j\in C\}$. The projection of $\ker B$ onto the $f$ coordinates is precisely

$$
\{w\in\mathbb C^2:B_fw\in\mathcal W\}.
\tag{113.19}
$$

Since $B_f$ is an isometry and that projection is $\mathbb Cm$, one obtains

$$
\mathcal F\cap\mathcal W=\mathbb Cu,\qquad
u=B_fm,\quad\|u\|=1,\quad u\in\mathcal W.
\tag{113.20}
$$

Every vector in $\operatorname{range}H$ is $`v=B^*w`$, and $v_f=0$ exactly when $w\perp\mathcal F$. Hence an outside record $h_j$ admits no such $v$ with $v_j\ne0$ exactly when $h_j\in\mathcal F$. Since $h_j\in\mathcal W$, this is equivalent to $h_j\in\mathbb Cu$. Otherwise (113.18) gives $`x_j=h_j^*u=0`$. Thus every outside record satisfies

$$
h_j\in\mathbb Cu\quad\text{or}\quad h_j\perp u.
\tag{113.21}
$$

They cannot all be orthogonal to $u$, since their span contains $u$. Choose an outside record $h_j$ parallel to $u$, in a fibre $g\ne f$. A third original fibre $k\ne f,g$ has both records with nonzero inner product with $h_j$. By (113.21), both records of $k$ must therefore be parallel to $u$. This contradicts their original orthonormality $H_{kk}=I_2$. Hence rank one is impossible, and every $U_f$ has rank two. ∎

### 113.4. Opposite orientations force a full kernel-normal matrix to vanish

**Lemma 113.3.** Under (113.3), let $k=\dim\ker H<4$. Suppose a partition $A,B$ into two pairs of original fibres satisfies $\operatorname{rank}U_A=\operatorname{rank}U_B=k$. Then no such local minimum exists.

**Proof.** Each $k\times4$ block has a nonzero null vector. Choose $n,m$ supported on $A,B$ respectively with $Un=Um=0$. They belong to $\operatorname{range}H$, so Lemma 113.1 applies. Combine its two equations for $z=1,i$:

$$
\begin{aligned}
Z&=\mathcal A(S(1))+i\mathcal A(S(i))
   =\Lambda+U^*YU,\\
\Lambda&=\Lambda_1+i\Lambda_i,\qquad Y=Y_1+iY_i.
\end{aligned}
\tag{113.22}
$$

Here $Y$ need not be Hermitian. Conjugation in (113.8) gives exactly

$$
Z_{AB}=2C,\qquad Z_{BA}=0,\qquad
C_{ij}=\frac{P_{ij}\bar n_i m_j}{\overline{H_{ij}}}
\quad(i\in A,j\in B).
\tag{113.23}
$$

All blocks inside $A\times A$ and $B\times B$ also vanish. Since $\Lambda$ is original-fibre-block diagonal, the reverse block of (113.22) yields $`U_B^*YU_A=0`$. Choose right inverses $R_A,R_B$ of the full-row-rank blocks. Then

$$
Y=R_B^*(U_B^*YU_A)R_A=0.
\tag{113.24}
$$

Thus $Z=\Lambda$ has zero $A\times B$ block. But $n,m$ are nonzero, and every $P_{ij},H_{ij}$ across that partition is nonzero, so at least one entry of $C$ in (113.23) is nonzero. This is a contradiction.

The two normal decompositions may differ, but both come from the same fixed $P$ and the same nonnegative curved quadratic. No independently selected witnesses are combined, and no positivity is asserted for the non-Hermitian $Y$. ∎

### 113.5. Complete exclusion of the full-support rank-(7,5) local class

**Theorem 113.4.** There is no local minimum of (113.2) on the full calibrated domain satisfying (113.3) and $\operatorname{rank}H=5$.

**Proof.** Now $U$ has three rows. By Theorem 113.2, each $L_f=\operatorname{range}U_f$ is a two-dimensional complex plane in $\mathbb C^3$.

Deleting any one original fibre leaves a full-row-rank kernel block:

$$
\operatorname{rank}U_{f^c}=3\qquad\text{for every }f.
\tag{113.25}
$$

Otherwise there is a nonzero $w$ with $`U_{f^c}^*w=0`$. Since $`U^*`$ is injective, $`x=U^*w`$ is a nonzero kernel vector of $H$ supported on $f$. But

$$
x^*Hx=x_f^*H_{ff}x_f=\|x_f\|^2>0,
\tag{113.26}
$$

contradicting $Hx=0$.

Two distinct planes in $\mathbb C^3$ span the whole space. Thus a pair of fibre blocks has rank three exactly when its two planes differ. The four planes can be paired into two unequal pairs unless one plane occurs at least three times. Indeed the other equality-multiplicity patterns are $(1,1,1,1)$, $(2,1,1)$ and $(2,2)$. For four distinct planes take any pairing; for $(2,1,1)$ pair each copy of the repeated plane with a singleton; for $(2,2)$ pair across the two classes.

Three equal planes contradict (113.25) on deleting the fourth fibre. Four equal planes contradict the full row rank of $U$. Hence one of the three admissible patterns applies and yields a partition $A,B$ with both ranks three. Lemma 113.3, with $k=3<4$, gives the contradiction. ∎

Theorem 113.4 includes the exceptional locus left by Theorem 112.4 through a direct kernel-plane argument. It does not infer exclusion from density or perturb a minimum while assuming its minimality survives. The conclusion concerns positive subhalf local minima, not a half lower bound for arbitrary rank-$(7,5)$ competitors.

### 113.6. A sharper attained-global-representative alternative

**Corollary 113.5.** For the original unrestricted one-product channel problem, with the fixed correlated encoding and unhalved arbitrary-reference error, a hypothetical optimum below $1/4$ has a calibrated minimizing representative in at least one of these two classes:

1. Both full Gram ranks are at most six.
2. One full Gram has rank seven and an everywhere-nonzero spanning kernel vector, while the opposite full rank is at most four.

**Proof.** The exact physical calibration reduction of [RT II §72](ARITHMETIC_HOLOGRAPHIC_RT_II.md#72-exact-physical-calibration-reduction-for-collapsed-fibre-channels), as applied in Corollary 106.6, identifies the unrestricted physical infimum with the attained calibrated minimum. The established lower bound $\sqrt3-3/2>0$ makes the hypothetical subquarter value positive. Theorem 106.5 supplies a minimizing representative with both ranks at most six, or with one full-support rank-seven Gram and opposite rank at most five. In the latter case the global minimizer is also a full-domain local minimum, and its value lies in $(0,1/2)$. Theorem 113.4 excludes opposite rank five, proving the stated alternative. ∎

Theorem 113.2 applies to every opposite rank but leaves the all-rank-two projection cases at other ranks unresolved. Neither class of Corollary 113.5 is excluded here. The representative conclusion does not preserve the ranks or local minimality of an arbitrary given leaking optimizer; it is an existence assertion after the exact physical reduction and rank descent. The unrestricted global interval remains $[\sqrt3-3/2,1/4]$, and the quarter-optimum question remains open.

## 追加锚（本行以下为增补区）

## 114. Original-fibre stress positivity and two-fibre rank saturation

### 114.1. Original domain and the common curved quadratic

Let the four original fibres have two coordinates each. Write $\mathcal E$ for the positive semidefinite Hermitian $8\times8$ matrices whose four diagonal fibre blocks are $I_2$. The calibrated channels have Stinespring records

$$
 |f,i\rangle\longmapsto |f\rangle\otimes a_{fi},
 \qquad
 |f,i\rangle\longmapsto |f\rangle\otimes b_{fi},
 \qquad G,H\in\mathcal E.
 \tag{114.1}
$$

The logical input is encoded as $|f,i\rangle\mapsto|f,i\rangle\otimes|f,i\rangle$, and the output as $|f\rangle\mapsto|f\rangle\otimes|f\rangle$. With the target coefficient matrix $T_{ff}=I_2$ and $T_{fg}=J_2/2$ for $f\ne g$, the original unhalved diamond error, allowing arbitrary references, equals

$$
 F(G,H)=\max\left\{2\operatorname{Tr}[(T-G\odot H)W]:
 \rho\ge0,\quad \rho=\bigoplus_f\rho_f,\quad
 \operatorname{Tr}\rho=1,\quad0\le W\le\rho\right\}.
 \tag{114.2}
$$

Throughout the exclusion arguments, $(G,H)$ is assumed to be a local minimum of $F$ on the full domain $\mathcal E\times\mathcal E$, including competitors of different ranks, and

$$
 \operatorname{rank}G=7,\qquad
 \ker G=\mathbb C a,\qquad a_i\ne0\ \text{for every }i,
 \qquad 0<F(G,H)<\tfrac12.
 \tag{114.3}
$$

The common-stress results of [RT III §§92,95,98](ARITHMETIC_HOLOGRAPHIC_RT_III.md#98-curved-common-stress-tests-and-finite-principal-quotients), in the form used in §113.1, give

$$
 \begin{aligned}
 P_A&=\alpha aa^*,&
 P&=\alpha\operatorname{diag}(a)R\operatorname{diag}(\bar a)\ge0,\\
 \alpha&>0,&R&\ge0,\quad R_{ii}=1,\quad
 G=H\odot\bar R,\quad PH=0.
 \end{aligned}
 \tag{114.4}
$$

All cross-fibre entries of $G,H,R,P$ are nonzero: the matrix-unit test gives $|1/2-G_{ij}H_{ij}|\le F(G,H)<1/2$. Also $P_{ii}=\alpha|a_i|^2>0$.

Let $h=\operatorname{rank}H$, let $N$ be the orthogonal projection onto the entire kernel of $H$, and choose a full-row-rank matrix $U$ with $`\operatorname{range}U^*=\ker H`$. The same normalized stress gives one nonnegative real quadratic on the whole curved tangent space:

$$
 \begin{aligned}
 \mathcal T_H&=\{D=D^*:D_{ff}=0,\ NDN=0\},
 &D_A&=-\bar R\odot D,\\
 Q(D)&=-\sum_{f(i)\ne f(j)}
      \frac{\bar P_{ij}D_{ij}^{\,2}}{H_{ij}}
      +\alpha a^*D_AG^+D_Aa+\operatorname{Tr}(PDH^+D)
      \ge0.
 \end{aligned}
 \tag{114.5}
$$

The sum is ordered and uses complex squares. The superscript $+$ denotes the Moore–Penrose inverse. The common-witness positive-scaling argument in the cited result fixes the same $P$ for every direction in (114.5); the nonnegativity is not obtained by choosing a different norming witness for each direction.

### 114.2. Partition stars and oriented normal matrices

**Lemma 114.1 (original partition stars).** Under (114.3)–(114.5), partition the coordinates into complementary unions $A,B$ of original fibres. Suppose $n$ is supported on $A$, $m$ is supported on $B$, $Pn=Pm=0$, and at least one of $n,m$ belongs to $\operatorname{range}H$. Then the matrix

$$
 Z(n,m)_{ij}=
 \begin{cases}
 P_{ij}\bar n_i m_j/\bar H_{ij},&i\in A,\ j\in B,\\
 0,&\text{otherwise}
 \end{cases}
 \tag{114.6}
$$

satisfies $HZ=ZH=0$. In particular its columns belong to $\ker H\cap\mathbb C^A$ and the columns of $`Z^*`$ belong to $\ker H\cap\mathbb C^B$.

**Proof.** For every $z\in\mathbb C$, put

$$
 S(z)=z\,nm^*+\bar z\,mn^*.
 \tag{114.7}
$$

The disjoint unions of fibres give $S(z)_{ff}=0$. Since one of $Nn,Nm$ is zero, $NS(z)N=0$. Also $S(z)P=PS(z)=0$. The exact product-cancellation identity is

$$
 \bigl(D_A(S(z))a\bigr)_i
   =-\frac{(S(z)P)_{ii}}{\alpha\bar a_i}=0.
 \tag{114.8}
$$

Both nonnegative curvature costs in (114.5) therefore vanish, as do their real polarizations against every $D\in\mathcal T_H$. The mixed term on (114.7) has the form $-2\operatorname{Re}(z^2c)$. Nonnegativity for every complex $z$ forces $c=0$. Thus $S(1)$ and $S(i)$ are radical vectors of the same nonnegative quadratic on the whole space $\mathcal T_H$.

For either such $S$, define the Hermitian matrix

$$
 \mathcal A(S)_{ij}
   =\frac{P_{ij}\bar S_{ij}}{\bar H_{ij}}\quad(f(i)\ne f(j)),
 \qquad \mathcal A(S)_{ff}=0.
 \tag{114.9}
$$

Its negative real Hilbert–Schmidt pairing with $D$ is the mixed-term polarization. Hence it annihilates $\mathcal T_H$. The normal space of the intersection of the two linear kernels defining $\mathcal T_H$ is the sum of their normal spaces, so

$$
 \mathcal A(S(1))=\Lambda_1+U^*Y_1U,
 \qquad
 \mathcal A(S(i))=\Lambda_i+U^*Y_iU,
 \tag{114.10}
$$

where each $\Lambda$ is original-fibre-block diagonal and each $Y$ is Hermitian. The normal multipliers may vary; the stress $P$ does not. Taking half the first equation plus $i/2$ times the second gives exactly (114.6), with

$$
 Z=\Lambda+U^*YU,
 \qquad HZ=H\Lambda,\qquad ZH=\Lambda H.
 \tag{114.11}
$$

The combined $\Lambda,Y$ need not be Hermitian. For a fibre $f\subset A$, the columns of $Z$ on $f$ vanish, so $(HZ)_{ff}=0$ and $H_{ff}=I_2$ imply $\Lambda_{ff}=0$. For a fibre $g\subset B$, the rows of $Z$ on $g$ vanish, so $(ZH)_{gg}=0$ similarly implies $\Lambda_{gg}=0$. Therefore $\Lambda=0$ and $HZ=ZH=0$. The stated support properties follow. ∎

### 114.3. Every stress fibre has rank two when the opposite rank exceeds two

**Theorem 114.2 (positive stress fibre blocks).** Under (114.3), if $h>2$, every original block $P_{ff}$ is positive definite. Equivalently every $R_{ff}$ is positive definite.

**Proof.** If some $P_{ff}$ is singular, choose a nonzero vector $n$ supported on $f$ with $P_{ff}n_f=0$. Positivity of $P$ implies $Pn=0$. Factor $`H=B_0^*B_0`$ with $B_0$ an $h\times8$ full-row-rank record matrix. Its two columns on $f$ are orthonormal. Since $h>2$, choose a nonzero $x$ perpendicular to their span and put $`m=B_0^*x`$. Then $m\ne0$, $m_f=0$, and $m\in\operatorname{range}H$, so $Pm=0$.

Apply Lemma 114.1 with $A=f$. Every column of its $Z$ lies in $\ker H\cap\mathbb C^f=\{0\}$, because $H_{ff}=I_2$. Hence $Z=0$. But a nonzero coordinate of $n$ and a nonzero coordinate of $m$ give a nonzero entry in (114.6), since every cross-fibre coefficient is nonzero. This contradiction proves $P_{ff}>0$. The nonsingular diagonal congruence in (114.4) proves the equivalent assertion about $R_{ff}$. ∎

The hypothesis $h>2$ supplies the supported range vector $m$. At $h=2$, the two records in one fibre already span the environment, and this argument supplies no such vector. The theorem concerns the actual common stress, rather than only the projection of the full kernel of $H$.

### 114.4. Singular two-fibre Grams force stress-rank saturation

**Theorem 114.3 (two-fibre rank saturation).** Under (114.3), assume $h=4$. Let $A,B$ each consist of two original fibres and put

$$
 r_A=\operatorname{rank}H_{AA},\qquad
 r_B=\operatorname{rank}H_{BB},\qquad
 p_B=\operatorname{rank}P_{BB}.
 \tag{114.12}
$$

If $r_B<4$, then $p_B=r_A$. The assertion with $A,B$ interchanged also holds.

**Proof.** Consider the complex vector spaces

$$
 V_A=\operatorname{range}H\cap\mathbb C^A,
 \qquad M_B=\ker P\cap\mathbb C^B.
 \tag{114.13}
$$

An injective record map $`B_0^*:\mathbb C^4\to\mathbb C^8`$ identifies $V_A$ with the kernel of its $B$-coordinate restriction. Positivity identifies $M_B$ with the kernel of its principal block. Thus

$$
 \dim_{\mathbb C}V_A=4-r_B,
 \qquad \dim_{\mathbb C}M_B=4-p_B.
 \tag{114.14}
$$

Every $n\in V_A$, $m\in M_B$ satisfies the hypotheses of Lemma 114.1. The matrices $\bar n_A m_B^{\mathsf T}$ span a tensor-product matrix space of complex dimension $(4-r_B)(4-p_B)$. Entrywise multiplication by $(P_{ij}/\bar H_{ij})_{i\in A,j\in B}$ is invertible on all $4\times4$ matrices, because each entry is nonzero. Consequently the span of the matrices $Z(n,m)$ has the same dimension.

On the other hand, their column spaces lie in the kernel of $H$ supported on $A$, of dimension $4-r_A$, and their adjoint column spaces lie in the corresponding space on $B$, of dimension $4-r_B$. Therefore

$$
 (4-r_B)(4-p_B)\le(4-r_A)(4-r_B).
 \tag{114.15}
$$

The assumption $r_B<4$ permits cancellation, giving $p_B\ge r_A$.

For the reverse inequality, $\operatorname{range}P\subset\ker H$. The coordinate projection of this kernel onto $B$ has dimension $\operatorname{rank}U_B$. The kernel of $`U_B^*`$ corresponds, through the injective $`U^*`$, to the kernel of $H$ supported on $A$, which has dimension $4-r_A$. Since $U$ has four rows,

$$
 p_B\le\operatorname{rank}U_B
       =4-(4-r_A)=r_A.
 \tag{114.16}
$$

This proves equality. ∎

**Corollary 114.4 (rank-deficient stress consumers).** Under the hypotheses of Theorem 114.3, if $\operatorname{rank}P\le3$, complementary two-fibre principal Grams of $H$ cannot have exactly one positive-definite member. If $\operatorname{rank}P=\operatorname{rank}R=2$, every two-fibre principal Gram of $H$ is positive definite.

**Proof.** The first assertion follows from $p_B=r_A=4$, which would contradict $p_B\le\operatorname{rank}P\le3$.

For the second, suppose $H_{BB}$ is singular. Theorem 114.3 gives $r_A=p_B\le2$. Each two-fibre principal Gram contains $I_2$, so $r_A=2$. Interchanging $A,B$ gives $r_B=2$. Since $\operatorname{rank}H=4$, the spans of the $H$-records on the two halves form a direct sum.

Write $H_{ij}=\langle h_i,h_j\rangle$ and $R_{ij}=\langle r_i,r_j\rangle$. The product records $h_i\otimes\bar r_i$ have Gram $G$, and hence

$$
 \sum_i a_i h_i\otimes\bar r_i=0.
 \tag{114.17}
$$

Project the first tensor factor onto the $A$-record span along the complementary $B$-record span. This gives a nontrivial relation supported only on $A$. It is impossible because every proper principal Gram of $G$ is positive definite: a null vector of such a principal Gram extends by zero to a null vector of $G$, whereas every nonzero vector in $\ker G$ has full support.

This last direct-sum argument is the elementary connected-factor implication of [Lovitz–Petrov, arXiv:2103.15633v2, Proposition 5](https://arxiv.org/html/2103.15633v2#S4), recorded in the [Library note](../../../Library/Factorization/lovitzpetrov2023kruskal.md). Its role here is the product-circuit step after the new stress-rank equality; no new general connectedness theorem is asserted. ∎

### 114.5. A physical rank-two quotient with two singular half Grams

**Proposition 114.5 (nonvacuity outside the one-full-block and spectral subclasses).** There are calibrated physical Grams with ranks $(\operatorname{rank}G,\operatorname{rank}H)=(7,4)$, a full-support kernel of $G$, and a positive semidefinite factor $P$ satisfying the algebraic identities (114.4), such that $\operatorname{rank}P=2$, every $P_{ff}>0$, both complementary half Grams have rank three, all cross-fibre entries are nonzero, and $\lambda_{\max}(H)>3$. The quadratic expression on the right of (114.5) has an explicit negative zero-cost direction.

**Proof.** Use zero-based ambient coordinates $0,1,2,3$. Let $J$ contain the first two columns of $I_4$, let $R_{ij}(c,s)$ be $I_4$ with the $i,j$ block $\left(\begin{smallmatrix}c&-s\\s&c\end{smallmatrix}\right)$, and let $r(c,s)$ be that two-by-two rotation. Define

$$
 \begin{aligned}
 B_0&=Jr(3/5,4/5),\\
 B_1&=R_{02}(99/101,20/101)Jr(5/13,12/13),\\
 B_2&=R_{03}(35/37,12/37)Jr(8/17,15/17),\\
 B_3&=R_{03}(35/37,12/37)R_{12}(63/65,16/65)Jr(7/25,24/25),\\
 B_\circ&=[B_0\ B_1\ B_2\ B_3],\qquad H=B_\circ^{\mathsf T}B_\circ.
 \end{aligned}
 \tag{114.18}
$$

Each original fibre is an orthonormal pair. A rational kernel basis is

$$
 U=\begin{pmatrix}
 -52/25&-39/25&12/5&1&0&0&0&0\\
 -17/10&-51/40&0&0&15/8&1&0&0\\
 83397/31250&876483/1625000&-9696/3125&0&-119/200&0&1&0\\
 -12252/15625&-206082/203125&-2828/3125&0&51/25&0&0&1
 \end{pmatrix},
 \tag{114.19}
$$

so $`UB_\circ^{\mathsf T}=0`$. Put

$$
 \begin{aligned}
 V&=\begin{pmatrix}1&3&7&11\\2&-1&5&13\end{pmatrix}U,
 &P&=V^{\mathsf T}V,&G_0&=H\odot P,\\
 a_i&=\sqrt{P_{ii}},&
 R&=\operatorname{diag}(a)^{-1}P\operatorname{diag}(a)^{-1},&
 G&=H\odot R.
 \end{aligned}
 \tag{114.20}
$$

These are positive semidefinite Grams; the positive diagonal congruence gives (114.4) with $\alpha=1$. The original Grams $G,H$ have fibre blocks $I_2$ because the off-diagonal entry of each $H_{ff}$ vanishes.

The following residues modulo $1009$ provide exact nonzero rank and cross-entry certificates; all displayed rational denominators are invertible modulo $1009$. Coordinate subsets here use the order $0,\ldots,7$ of (114.18):

$$
 \begin{aligned}
 \det(B_{\circ,\{0,1,2,4\}})&\equiv626,&
 \det(H_{\{0,1,2\}})&\equiv299,&
 \det(H_{\{4,5,6\}})&\equiv30,\\
 (\det V_0,\det V_1,\det V_2,\det V_3)
    &\equiv(321,456,910,36),&&&\\
 \det((G_0)_{\{0,\ldots,6\}})&\equiv811,&&&\\
 \prod_{\substack{i<j\\f(i)\ne f(j)}}H_{ij}&\equiv671,&
 \prod_{\substack{i<j\\f(i)\ne f(j)}}P_{ij}&\equiv601.
 \end{aligned}
 \tag{114.21}
$$

They follow by substitution into (114.18)–(114.20). The first two fibres span a three-dimensional space; the last two also span a three-dimensional space, as their rotation formulas show. The nonzero three-coordinate minors prove the exact half ranks. The four nonzero $\det V_f$ prove $P_{ff}>0$ and $\operatorname{rank}P=2$. Moreover $PH=0$ gives $G_0\mathbf1=0$ term by term. Its seven-coordinate minor therefore proves rank seven and the full-support kernel $\ker G=\mathbb C a$. The two cross products certify every original cross entry is nonzero. Finally

$$
 \lambda_{\max}(H)\ge(B_\circ B_\circ^{\mathsf T})_{00}
   =\frac{52375188}{13965169}>3.
 \tag{114.22}
$$

For the partition into the first and last four coordinates, set

$$
 \begin{aligned}
 n_A&=(-1313/1980,\ 1313/1485,\ -5/12,\ 1)^{\mathsf T},&n_B&=0,\\
 m_A&=0,&m_B&=(-2200/8891,\ -3219/8891,\ 1,\ 0)^{\mathsf T},\\
 D&=i(nm^{\mathsf T}-mn^{\mathsf T}).
 \end{aligned}
 \tag{114.23}
$$

Direct multiplication gives $Un=0$, $Pn=Pm=0$, $D_{ff}=0$, $`UDU^*=0`$ and $DP=0$. Both costs in (114.5) vanish, and its mixed term is

$$
 Q(D)=-\frac{
 325333932610778388092304109579748666754408132364187198677}{
 395150328355529340430401159343798921639721694765543750}<0.
 \tag{114.24}
$$

Thus the stated geometric class is nonempty and is excluded by the common curved criterion. No norming witness or subquarter error is asserted for this fixture. ∎

### 114.6. Remaining scope

Theorem 114.2 excludes a singular original stress-fibre block for every opposite rank greater than two. Theorem 114.3 and Corollary 114.4 impose additional two-fibre restrictions at opposite rank four. They leave the class with all six two-fibre $H$ principal Grams positive definite unresolved, and the rank count alone does not exclude stress rank three with two complementary rank-three $H$ blocks. The existential global-rank alternative in Corollary 113.5 is therefore not reduced to a lower maximum rank by this section. No arbitrary leaking optimizer is asserted to preserve its ranks under calibration, and the unrestricted quarter optimum remains open.

## 追加锚（本行以下为增补区）

## 115. Quantitative quotient coherence and the common-line rank-four exclusion

### 115.1. A rational two-fibre comparison

Use the original fixed correlated input and output encodings, the original channels $A,B:\mathcal L(\mathbb C^8)\to\mathcal L(\mathbb C^4)$, and their unhalved arbitrary-reference diamond error $\delta$. Their actual correct-output forward Grams are denoted by $G,H$, including when the channels leak outside the correct output fibre. Put $K=G\odot H$ and let $T$ have blocks $T_{ff}=I_2$ and $T_{fg}=J_2/2$ for $f\ne g$. The original tagged-reference argument in [RT III §91.5](ARITHMETIC_HOLOGRAPHIC_RT_III.md#915-uniform-reference-and-complete-two-fibre-tests) gives

$$
 \delta\ge\|T_{fg}-K_{fg}\|_{\rm op}\qquad(f\ne g).
 \tag{115.1}
$$

Each correct-output record map on an original fibre is a contraction. In particular $H_{fg}$ is a $2\times2$ contraction. These statements use the actual correct-output Grams and retain output leakage.

**Lemma 115.1 (rational entrywise-power comparison).** Let $C$ be a complex $2\times2$ matrix, and suppose $0\le d\le51/200$ and $\|J_2/2-C\|_{\rm op}\le d$. Then

$$
 \sum_{i,j=1}^2|C_{ij}|^{2/3}
   >\frac{12}{7}(1-d)+\frac{181}{250}.
 \tag{115.2}
$$

Consequently $\sum|C_{ij}|^{2/3}\le2$ implies $\|J_2/2-C\|_{\rm op}>51/200$.

**Proof.** Every $x_{ij}=|C_{ij}|$ belongs to $[49/200,151/200]$. With $\mathbf1=(1,1)^T$, the operator-norm bound also gives

$$
 \sum_{i,j}x_{ij}\ge|\mathbf1^*C\mathbf1|
 \ge2-2d.
 \tag{115.3}
$$

The concavity of $x^{2/3}$ and the following exact positive endpoint differences prove a strict affine lower bound throughout this closed interval:

$$
 \begin{aligned}
 \left(\frac{49}{200}\right)^2
  -\left(\frac{391}{1000}\right)^3
   &=\frac{248529}{1000000000}>0,\\
 \left(\frac{151}{200}\right)^2
  -\left(\frac{5797}{7000}\right)^3
   &=\frac{709178427}{343000000000}>0,\\
 x^{2/3}&>\frac67x+\frac{181}{1000}
   \quad\left(\frac{49}{200}\le x\le\frac{151}{200}\right).
 \end{aligned}
 \tag{115.4}
$$

Indeed the affine function has endpoint values $391/1000$ and $5797/7000$. Its graph lies strictly below the chord of $x^{2/3}$, which lies below the concave graph. Summing (115.4) and applying (115.3) proves (115.2). At $d=51/200$, its right side is $1751/875>2$, proving the last assertion. ∎

### 115.2. An actual quotient must have coherent fibre blocks

**Theorem 115.2 (quantitative quotient-fibre obstruction).** Suppose the actual correct-output Grams of the original channels satisfy

$$
 G=H\odot\bar R,\qquad R\ge0,\qquad R_{ii}=1.
 \tag{115.5}
$$

Write $r_f=|R_{f0,f1}|\in[0,1]$. If $\delta\le51/200$, then for every pair of distinct original fibres,

$$
 r_fr_g>
 \left[\frac67(1-\delta)+\frac{181}{500}\right]^3-1>0.
 \tag{115.6}
$$

In particular a single block $R_{ff}=I_2$ forces $\delta>51/200$. If $\delta\le1/4$, then

$$
 r_fr_g>\kappa,\qquad r_f>\kappa,\qquad
 \kappa=\left(\frac{3517}{3500}\right)^3-1
       =\frac{627789413}{42875000000}.
 \tag{115.7}
$$

**Proof.** Factor $R$ by unit records, and let $F_f$ consist of its two columns on fibre $f$. The frame operator $`A_f=F_fF_f^*`$ has possibly nonzero eigenvalues $1+r_f$ and $1-r_f$. If $u_f$ is a top unit eigenvector, write

$$
 A_f=(1-r_f)\Pi_f+2r_fu_fu_f^*.
 \tag{115.8}
$$

For $r_f<1$, $\Pi_f$ is the orthogonal projection onto its two-dimensional range. For $r_f=1$, that term vanishes and any projection containing the range suffices. Thus the singular endpoint requires no inverse. Since $\operatorname{Tr}A_g=2$ and $\|A_g\|_{\rm op}=1+r_g$,

$$
 \begin{aligned}
 \|R_{fg}\|_F^2
 &=\operatorname{Tr}(A_fA_g)\\
 &\le(1-r_f)\operatorname{Tr}A_g
      +2r_f\|A_g\|_{\rm op}
 =2(1+r_fr_g).
 \end{aligned}
 \tag{115.9}
$$

The case $r_f=0$ is included, with $A_f=\Pi_f$. The actual block $H_{fg}$ is a contraction, so $\|H_{fg}\|_F^2\le2$. On this cross block, (115.5) gives $K_{ij}=H_{ij}^2\bar R_{ij}$. Hölder's inequality, with exponents $3/2$ and $3$, gives

$$
 \begin{aligned}
 \sum_{i\in f,j\in g}|K_{ij}|^{2/3}
 &=\sum_{i\in f,j\in g}
    (|H_{ij}|^2)^{2/3}(|R_{ij}|^2)^{1/3}\\
 &\le\left(\sum|H_{ij}|^2\right)^{2/3}
       \left(\sum|R_{ij}|^2\right)^{1/3}
 \le2(1+r_fr_g)^{1/3}.
 \end{aligned}
 \tag{115.10}
$$

Zero entries cause no difficulty. Applying Lemma 115.1 with $C=K_{fg}$ and $d=\delta$, justified by (115.1), proves

$$
 2(1+r_fr_g)^{1/3}
 >\frac{12}{7}(1-\delta)+\frac{181}{250}.
 \tag{115.11}
$$

Divide by two and cube positive quantities. This yields (115.6); its right side is positive because the bracket is at least $1751/1750>1$. If $r_f=0$, (115.6) is impossible for any other fibre. At $\delta\le1/4$, the bracket is at least $3517/3500$, proving the product bound in (115.7). Since $r_g\le1$, it also gives $r_f>\kappa$. ∎

The theorem is a lower bound for original leaking channels through the exact identity (115.5). It does not replace their diamond norm by a calibrated upper formula, nor assert that an arbitrary Gram representative preserves a leaking channel.

**Corollary 115.3 (phased-cube obstruction).** Suppose, on one pair of distinct original fibres,

$$
 K_{fg}=D_1(H_{fg}\odot H_{fg}\odot H_{fg})D_2,
 \tag{115.12}
$$

where $D_1,D_2$ are diagonal unitaries. Then $\delta>51/200$. In particular this holds if $`G=E^*(H\odot H)E`$ for a diagonal unitary $E$.

**Proof.** For the block $C$ in (115.12), phases do not change entry magnitudes, so

$$
 \sum|C_{ij}|^{2/3}=\|H_{fg}\|_F^2\le2.
 \tag{115.13}
$$

Lemma 115.1 and (115.1) prove the bound. The displayed global identity implies (115.12) with $`D_1=E_f^*`$ and $D_2=E_g$. The argument retains arbitrary phases and output leakage. ∎

### 115.3. All singular two-fibre blocks determine the full stress

For this subsection assume explicitly that $(G,H)$ is a local minimum on the full calibrated domain $\mathcal E\times\mathcal E$, including different-rank competitors, and

$$
 \operatorname{rank}G=7,\qquad\ker G=\mathbb Ca,\qquad
 a_i\ne0\ \text{for every }i,\qquad
 \operatorname{rank}H=4,\qquad 0<F(G,H)<\tfrac12.
 \tag{115.14}
$$

Fix the same common normalized stress from (114.4),

$$
 P=\alpha\operatorname{diag}(a)R\operatorname{diag}(\bar a),\qquad
 \alpha>0,\quad R\ge0,\quad R_{ii}=1,\quad
 G=H\odot\bar R,\quad PH=0.
 \tag{115.15}
$$

Every original cross-fibre entry of $H,P$ is nonzero. Theorem 114.2 gives $P_{ff}>0$. Lemma 114.1 supplies its oriented normal matrix for every partition star, with this same $P$ throughout.

**Theorem 115.4 (common-line stress and quantitative exclusion).** Under (115.14), suppose every principal block of $H$ on two original fibres is singular. Then there are an invertible diagonal $D$ and a diagonal unitary $E$ such that

$$
 \begin{aligned}
 P&=D\bar H D^*,&\operatorname{rank}P&=\operatorname{rank}R=4,\\
 P_{ff}&\text{ is diagonal},&R_{ff}&=I_2\quad\text{for every }f,\\
 R&=E\bar H E^*,&G&=E^*(H\odot H)E.
 \end{aligned}
 \tag{115.16}
$$

Moreover $F(G,H)>51/200$. In particular no subquarter local minimum in (115.14) has all six two-fibre $H$ blocks singular.

**Proof.** Factor $`H=B_0^*B_0`$ with a full-row-rank $4\times8$ record matrix. Its original fibre ranges $L_f\subset\mathbb C^4$ are two-planes, span $\mathbb C^4$, and meet pairwise because every two-fibre block is singular. They have a common line. To see this including repeated planes, choose distinct $L_0,L_1$, put $\ell=L_0\cap L_1$ and $M=L_0+L_1$. If a third plane $L_2$ does not contain $\ell$, its distinct intersection lines with $L_0,L_1$ span it inside $M$. Any remaining plane outside $M$ meets $M$ in one line, which would have to belong to $L_0\cap L_1\cap L_2=0$. This is impossible. Then every plane would lie in the three-space $M$, contradicting total rank four. Thus all planes contain $\ell$.

Choose a unit vector $e\in\ell$ and unit vectors $v_f\in\ell^\perp$ with $L_f=\operatorname{span}(e,v_f)$. Using algebraic coordinates in each fibre, not a physical within-fibre symmetry, and ordering the common-line coordinates first, gives

$$
 \widetilde H=J_4\oplus Z,\qquad
 Z_{fg}=\langle v_f,v_g\rangle,\qquad
 Z_{ff}=1,\quad\operatorname{rank}Z=3,\quad\ker Z=\mathbb Ck.
 \tag{115.17}
$$

The full kernel is $\mathbf1^\perp\oplus\mathbb Ck$. If $k_f=0$, the projection of this kernel to fibre $f$ has dimension one. Since $\operatorname{range}P\subset\ker H$, this would imply $\operatorname{rank}P_{ff}\le1$, contrary to $P_{ff}>0$. Thus every $k_f\ne0$. Every proper principal Gram of $Z$ is consequently positive definite: a null vector on a proper subset would extend by zero to a kernel vector of $Z$, contradicting full support of $k$. All six two-fibre $H$ blocks therefore have rank exactly three.

Write the actual physical records on fibre $f$ as $b_{fi}=u_{fi}e+w_{fi}v_f$. The coefficient vectors $u_f,w_f$ form an orthonormal basis of $\mathbb C^2$. Reciprocal diagonal physical phases can make $u_f=(c_f,s_f)$ real and nonnegative; a phase choice of $v_f$ then gives $w_f=(-s_f,c_f)$. Initially $c_f$ or $s_f$ may vanish. The actual reciprocal transformation is

$$
 H'=E_0^*HE_0,\quad P'=E_0^*PE_0,\quad
 G'=E_0GE_0^*,\quad a'=E_0a,\qquad
 G'\odot H'=G\odot H.
 \tag{115.18}
$$

It preserves the original norm and full-domain local-minimum hypothesis. No arbitrary $U(2)$ transformation inside an original physical fibre is used.

For any complementary two-fibre partition $A=\{f,g\}$, $B=\{h,l\}$, the kernel supported on $A$ is spanned by $x_A=(u_f,-u_g)$. The range vectors supported on $A$ have zero common-line coordinates and the form

$$
 n_f=\nu_fw_f,\qquad n_g=\nu_gw_g,\qquad
 \bar k_f\nu_f+\bar k_g\nu_g=0.
 \tag{115.19}
$$

Choose such an $n\ne0$ and, analogously, an $m\ne0$ supported on $B$. Every one of their four fibre coefficients is nonzero. Both vectors belong to $\operatorname{range}H\subset\ker P$. Lemma 114.1 gives an oriented matrix, here denoted by $\mathcal Z$ to distinguish it from (115.17), with

$$
 \mathcal Z_{ij}=P_{ij}\bar n_i m_j/\bar H_{ij}
 \quad(i\in A,j\in B),\qquad
 \mathcal Z=\lambda x_Ay_B^*,\quad
 y_B=(u_h,-u_l).
 \tag{115.20}
$$

Its scalar $\lambda$ is nonzero, since some $n_i,m_j$ are nonzero and every cross ratio is nonzero. Entrywise multiplication by these ratios preserves the row and column supports of $\bar n m^T$. Thus $\operatorname{supp}x_A=\operatorname{supp}n$ and $\operatorname{supp}y_B=\operatorname{supp}m$. On each fibre $u_f,w_f$ have the same support. Two orthogonal unit vectors in $\mathbb C^2$ can have the same support only if both coordinates are nonzero. Hence $c_f,s_f>0$ for every $f$, before any division below.

Define

$$
 \eta_f=\frac{s_f^2-c_f^2}{c_fs_f},\qquad
 T_f=\operatorname{diag}(u_{fi}/w_{fi}).
 \tag{115.21}
$$

Every pair of distinct fibres is separated by some two-half partition. Equation (115.20), including its one-dimensional supported kernel spaces, therefore gives scalars $c_{fg}\ne0$ with

$$
 \begin{aligned}
 P_{fg}&=c_{fg}T_f\bar H_{fg}T_g,\qquad c_{gf}=\bar c_{fg},\\
 H_{fg}&=u_fu_g^T+Z_{fg}w_fw_g^T,\\
 T_fw_f&=u_f,\qquad T_fu_f=w_f+\eta_fu_f.
 \end{aligned}
 \tag{115.22}
$$

In the algebraic orthonormal bases $(u_f,w_f)$, the cross block is consequently

$$
 c_{fg}\begin{bmatrix}
 \eta_f\eta_g+\bar Z_{fg}&\eta_f\\
 \eta_g&1
 \end{bmatrix}.
 \tag{115.23}
$$

Reorder all common-line coordinates first and write

$$
 \widetilde P=\begin{bmatrix}A&C\\C^*&D_0\end{bmatrix}.
 \tag{115.24}
$$

Complementarity with (115.17) gives $A\mathbf1=0$, $`C^*\mathbf1=0`$, $CZ=0$ and $D_0Z=0$. Positivity gives $`D_0=\beta kk^*`$ for $\beta\ge0$, and $P_{ff}>0$ forces $\beta>0$. The bottom-right cross entries in (115.23) give $c_{fg}=\beta k_f\bar k_g$. Also $CZ=0$ gives $`C=\gamma k^*`$. Its cross entries determine $\gamma_f=\beta\eta_fk_f$, including the diagonal of $C$. With $d=\operatorname{diag}(\eta)k$, it follows that

$$
 C=\beta dk^*,\qquad\sum_f\eta_fk_f=0.
 \tag{115.25}
$$

Put $`A_0=A-\beta dd^*`$. Its off-diagonal entries are $\beta k_f\bar k_g\bar Z_{fg}$, and $A_0\mathbf1=0$. The relation $\bar Z\bar k=0$ fixes its diagonal as well, so

$$
 \begin{aligned}
 A_0&=\beta\operatorname{diag}(k)\bar Z\operatorname{diag}(\bar k),\\
 \widetilde P
 &=\begin{bmatrix}A_0&0\\0&0\end{bmatrix}
   +\beta\begin{bmatrix}d\\k\end{bmatrix}
          \begin{bmatrix}d\\k\end{bmatrix}^*.
 \end{aligned}
 \tag{115.26}
$$

The first summand is positive semidefinite of rank three, and the added vector has a nonzero bottom component outside its range. Thus $\operatorname{rank}P=4$. Returning to the physical coordinates using (115.22) gives

$$
 \begin{aligned}
 P&=D\bar H D^*,\qquad
 D_{fi}=\sqrt\beta\,k_f\frac{u_{fi}}{w_{fi}},\\
 P_{ff}&=\beta|k_f|^2
  \operatorname{diag}\left(\frac{c_f^2}{s_f^2},
                           \frac{s_f^2}{c_f^2}\right).
 \end{aligned}
 \tag{115.27}
$$

Undoing (115.18) preserves the diagonal property and changes $D$ to another invertible diagonal matrix. In the original coordinates, $P_{ii}=\alpha|a_i|^2$ and $H_{ii}=1$ imply that $E_i=D_i/(\sqrt\alpha a_i)$ has modulus one. Substitution in (115.15) gives all identities in (115.16), including $R_{ff}=I_2$. Theorem 115.2, or alternatively Corollary 115.3, now yields $F(G,H)>51/200$. This proves the quantitative exclusion for the entire stated class. ∎

### 115.4. Original stress coherence and the remaining rank-four configurations

**Corollary 115.5 (subquarter necessary geometry).** At a full-domain calibrated local minimum with a full-support rank-seven first Gram and $0<F(G,H)\le1/4$, the same common normalized stress satisfies

$$
 r_f=\frac{|P_{f0,f1}|}
 {\sqrt{P_{f0,f0}P_{f1,f1}}},\qquad
 r_fr_g>\kappa\quad(f\ne g),\qquad r_f>\kappa,
 \tag{115.28}
$$

where $\kappa$ is the exact constant in (115.7), regardless of the opposite rank. If the opposite rank is four, at least one two-fibre principal block of $H$ is positive definite. If in addition $\operatorname{rank}P=3$, some partition into two complementary pairs of original fibres has both $H$ blocks positive definite.

**Proof.** The common-stress identities give $P_{ii}=\alpha|a_i|^2>0$, so the normalized quantity in (115.28) equals $|R_{f0,f1}|$. Theorem 115.2 proves its bounds. At opposite rank four, Theorem 115.4 excludes all six two-fibre blocks being singular. Choose a positive-definite one, on $A$, and let $B$ be its complementary pair. If $\operatorname{rank}P=3$ and $H_{BB}$ were singular, Theorem 114.3 would give $\operatorname{rank}P_{BB}=\operatorname{rank}H_{AA}=4$, impossible. Thus the complement is positive definite as well. ∎

The rank-four conclusion excludes the common-line record geometry, including its full-rank stress boundary. It does not exclude the all-six-positive-definite configuration or every mixed-rank partition. The fully coherent common-stress class, smaller first ranks and the unrestricted global quarter optimum remain open. The calibrated local-minimum statements do not assert rank preservation for an arbitrary given leaking optimizer.

## 追加锚（本行以下为增补区）

## 116. Three-fibre quotient products require an intrinsic complex phase

### 116.1. The original-channel principal quotient

Retain the four prescribed two-coordinate fibres of $\mathbb C^8$, and write $f(i)$ for the fibre of coordinate $i$. The target channel $\mathcal F:\mathcal L(\mathbb C^8)\to\mathcal L(\mathbb C^4)$ and its forward coefficient matrix $T$ are

$$
 \mathcal F(|i\rangle\langle j|)
   =T_{ij}|f(i)\rangle\langle f(j)|,\qquad
 T_{ff}=I_2,\qquad T_{fg}=\tfrac12J_2\quad(f\ne g).
 \tag{116.1}
$$

For arbitrary original CPTP maps $A,B:\mathcal L(\mathbb C^8)\to\mathcal L(\mathbb C^4)$, use the fixed isometries $V_{\rm in}|i\rangle=|i,i\rangle$ and $V_{\rm out}|f\rangle=|f,f\rangle$, with their encoding channels $\mathcal J_{\rm in},\mathcal J_{\rm out}$. The error is the unhalved arbitrary-reference diamond norm

$$
 \delta=\|(A\otimes B)\circ\mathcal J_{\rm in}
                  -\mathcal J_{\rm out}\circ\mathcal F\|_\diamond.
 \tag{116.2}
$$

For Stinespring isometries $V_A,V_B$, define the actual correct-output records $u_i=(\langle f(i)|\otimes I)V_A|i\rangle$ and $v_i=(\langle f(i)|\otimes I)V_B|i\rangle$. Their forward Grams are $G_{ij}=\langle u_i,u_j\rangle$ and $H_{ij}=\langle v_i,v_j\rangle$, with inner products conjugate-linear in the first argument. Thus

$$
 G,H\ge0,\qquad G_{ff},H_{ff}\le I_2,\qquad K=G\odot H.
 \tag{116.3}
$$

The fibre inequalities follow because each correct-output projection of a Stinespring isometry is a contraction. They retain arbitrary output leakage.

Let $S$ be the union of any three complete original fibres. A principal correlation quotient means a matrix $R$ defined only on $S$ such that

$$
 R\ge0,\qquad R_{ii}=1\ (i\in S),\qquad
 G_S=H_S\odot\bar R.
 \tag{116.4}
$$

This is an assumption on the actual physical Grams. It imposes no quotient outside $S$, no rank bound, and no reality assumption on $G$ or $R$.

**Theorem 116.1 (intrinsic phase obstruction).** Under (116.4), if $\delta<1/4$, then at least one of the eight triangles obtained by taking one coordinate from each of the three fibres in $S$ satisfies

$$
 \operatorname{Im}(H_{ij}H_{jk}H_{ki})\ne0.
 \tag{116.5}
$$

Consequently, if $H_S$ is real after a diagonal unitary conjugation, then $\delta\ge1/4$. Both conclusions also hold after an original-fibre-preserving relabeling.

**Proof.** The original matrix-unit witness has the exact normalization

$$
 \delta\ge\left|\tfrac12-K_{ij}\right|
 \qquad(f(i)\ne f(j)).
 \tag{116.6}
$$

Indeed the logical input $|i\rangle\langle j|$ has trace norm one. The actual composite output entry from $|f(i),f(i)\rangle$ to $|f(j),f(j)\rangle$ is $\bar K_{ij}$, whereas the target entry is $1/2$. An output trace norm bounds the absolute value of any entry, and the diamond norm bounds the no-reference induced trace norm. This proves (116.6) directly for the original channels, without discarding leakage or halving the norm. It is also the matrix-unit specialization of [RT III §91](ARITHMETIC_HOLOGRAPHIC_RT_III.md#91-adaptive-original-channel-witnesses-and-an-obstruction-to-all-two-fibre-tests).

Positivity and unit diagonal of $R$ give $|R_{ij}|\le1$, including singular $R$. Hence on $S$,

$$
 |K_{ij}|=|H_{ij}|^2|R_{ij}|\le|H_{ij}|^2.
 \tag{116.7}
$$

If $\delta<1/4$, every cross-fibre entry used below is therefore nonzero and obeys

$$
 |H_{ij}|^2\ge|K_{ij}|\ge\tfrac12-\delta>\tfrac14.
 \tag{116.8}
$$

Complete the actual second Gram by adding only its positive fibre defects:

$$
 \widehat H=H+\bigoplus_{f=1}^4(I_2-H_{ff})\ge0,
 \qquad \widehat H_{ff}=I_2.
 \tag{116.9}
$$

All cross-fibre entries are unchanged. This is a PSD comparison, with no assertion of rank preservation or local-minimum transfer for a leaking pair. Its two-fibre principal matrices give

$$
 \begin{bmatrix}I_2&H_{fg}\\H_{gf}&I_2\end{bmatrix}\ge0,
 \qquad \|H_{fg}\|_{\rm op}\le1.
 \tag{116.10}
$$

Its three-coordinate principal matrices, one coordinate from each selected fibre, are correlation matrices. Suppose, contrary to (116.5), that all eight cyclic products are real. Their moduli are positive by (116.8). A negative cyclic product, with edge magnitudes $x,y,z>1/2$, would make the corresponding principal determinant

$$
 1-x^2-y^2-z^2-2xyz
   <1-\tfrac34-\tfrac14=0,
 \tag{116.11}
$$

contradicting positivity. Thus all eight products are positive real.

Fix a coordinate $k$ in the third fibre. For $i$ in the first fibre and $j$ in the second, write $H_{ik}=r_i e^{\mathrm i\theta_i}$ and $H_{kj}=s_j e^{\mathrm i\phi_j}$ with $r_i,s_j>0$. Since $H_{jk}=\bar H_{kj}$ and $H_{ki}=\bar H_{ik}$, positivity of the cyclic product gives

$$
 \arg H_{ij}=\theta_i+\phi_j\pmod{2\pi}.
 \tag{116.12}
$$

Separate diagonal unitary changes on the rows and columns of the $2\times2$ block $H_{fg}$ turn that entire block into its entrywise absolute value, without changing its operator norm. With $w=(1,1)^T/\sqrt2$, (116.8) then gives

$$
 \|H_{fg}\|_{\rm op}
   =\|(|H_{ij}|)_{i\in f,j\in g}\|_{\rm op}
   \ge w^T(|H_{ij}|)_{i\in f,j\in g}w
   =\tfrac12\sum_{i\in f,j\in g}|H_{ij}|>1.
 \tag{116.13}
$$

This contradicts (116.10), proving (116.5). Each cyclic product is unchanged by a diagonal unitary conjugation of $H_S$. If that conjugation makes $H_S$ real, every such product is real, so the already proved implication forces $\delta\ge1/4$.

For completeness, these magnitude and cycle arguments do not require changing the physical pair. If a reciprocal diagonal gauge is used, let $E_S$ extend by arbitrary unit diagonal phases outside $S$ to a full eight-coordinate diagonal unitary $E$. The exact transformations are

$$
 \begin{aligned}
 H'&=E^*HE,&G'&=EGE^*,&R'&=(E_S^*)^2R E_S^2,\\
 (G')_S&=(H')_S\odot\overline{R'},&&
 G'\odot H'=G\odot H.
 \end{aligned}
 \tag{116.14}
$$

Here $R'$ is still defined only on $S$ and remains a correlation matrix. Opposite input phases on the two original channels implement the transformations of $G,H$; they cancel under $V_{\rm in}$, preserving the full original composite channel and its error. In particular the labelled coefficients $K_{ij}$, the target $1/2$, and (116.6) are unchanged. A common fibre-preserving permutation instead reindexes both $K$ and the target, preserving the same problem. This proves the relabeling statement as well. ∎

### 116.2. The full-support rank-seven local-minimum consumer

Define the full calibrated Gram domain and its exact original complete-norm objective by

$$
 \begin{aligned}
 \mathcal E&=\{M\in\operatorname{Herm}(8):M\ge0,\ M_{ff}=I_2\},\\
 F(G,H)&=\max_{\substack{\rho=\bigoplus_f\rho_f\ge0\\
                               \operatorname{Tr}\rho=1}}
     \|\sqrt\rho\,(T-G\odot H)\sqrt\rho\|_1.
 \end{aligned}
 \tag{116.15}
$$

For Gram records of any pair in $\mathcal E\times\mathcal E$, the maps $|i\rangle\mapsto|f(i)\rangle\otimes u_i$ and $|i\rangle\mapsto|f(i)\rangle\otimes v_i$ are isometries because the records within each fibre are orthonormal. They give calibrated original channels. By [RT III Theorem 91.1](ARITHMETIC_HOLOGRAPHIC_RT_III.md#911-original-channels-forward-grams-and-the-adaptive-theorem), $F$ is their unhalved diamond error. Local minimality below is on this entire domain, allowing arbitrary nearby ranks.

**Corollary 116.2 (a nonreal triangle on every fibre triple).** Suppose $(G,H)$ is a local minimum on $\mathcal E\times\mathcal E$ and

$$
 \operatorname{rank}G=7,\qquad \ker G=\mathbb C a,
 \qquad a_i\ne0\ (1\le i\le8),\qquad
 0<F(G,H)<\tfrac14.
 \tag{116.16}
$$

For each of the four choices of three original fibres, some triangle using one coordinate from each has $\operatorname{Im}(H_{ij}H_{jk}H_{ki})\ne0$. In particular no diagonal unitary can make any of these three-fibre principal Grams real. There is no assumption on the rank of $H$.

**Proof.** The full-domain same-common-witness quotient in [RT III Lemma 95.2](ARITHMETIC_HOLOGRAPHIC_RT_III.md#952-one-rank-seven-side-gives-a-supported-psd-quotient) applies because $0<F<1/2$. It supplies a scalar $\alpha>0$, a complementary second stress $P\ge0$, and a correlation matrix $R$ on the support of $a$. Since that support is all eight coordinates, its identities are

$$
 P=\alpha\operatorname{diag}(a)R\operatorname{diag}(\bar a),
 \qquad PH=0,\qquad G=H\odot\bar R.
 \tag{116.17}
$$

In particular the same global correlation quotient restricts to (116.4) on every selected triple. Apply Theorem 116.1 to any calibrated realization of this pair and use $\delta=F(G,H)$. This proves every assertion. The quotient comes from one common norming witness for the original complete-norm problem; no independently selected one-party witnesses are combined. ∎

The strict inequality in (116.16) is used to obtain (116.8). At equality $F=1/4$ the strict determinant and contraction contradictions need not hold. The conclusions provide neither a uniform positive lower bound on the imaginary part as the error approaches $1/4$ nor an exclusion of all genuinely complex configurations. The principal identity (116.4) is not asserted for arbitrary physical channel pairs, and reality of the first Gram alone is not a hypothesis of this result. The calibrated local-minimum consumer does not assert rank preservation for an arbitrary given leaking optimizer. The remaining complex rank classes and the unrestricted global quarter optimum remain open.

## 追加锚（本行以下为增补区）

## 117. Coherent spectral concentration and the exact quarter boundary

### 117.1. Original channels and a tagged pure target

Retain the four prescribed two-coordinate fibres of $`\mathbb C^8`$, the target $`\mathcal F`$ and the fixed correlated encodings. Explicitly, with $`f(i)`$ the fibre of coordinate $`i`$,

$$
 \mathcal F(|i\rangle\langle j|)
   =T_{ij}|f(i)\rangle\langle f(j)|,\qquad
 T_{ff}=I_2,\qquad T_{fg}=\tfrac12J_2\quad(f\ne g).
 \tag{117.1}
$$

For arbitrary original CPTP maps $`A,B:\mathcal L(\mathbb C^8)\to\mathcal L(\mathbb C^4)`$, let $`V_{\rm in}|i\rangle=|i,i\rangle`$ and $`V_{\rm out}|f\rangle=|f,f\rangle`$, with encoding channels $`\mathcal J_{\rm in},\mathcal J_{\rm out}`$. Define

$$
 \delta=\|(A\otimes B)\circ\mathcal J_{\rm in}
                  -\mathcal J_{\rm out}\circ\mathcal F\|_\diamond.
 \tag{117.2}
$$

The diamond norm is unhalved and permits arbitrary references. For Stinespring isometries, let $`a_i,b_i`$ be the actual correct-output environment records, and use forward Grams $`G_{ij}=\langle a_i,a_j\rangle`$, $`H_{ij}=\langle b_i,b_j\rangle`$, with inner products conjugate-linear in the first argument. Thus

$$
 G,H\ge0,\qquad G_{ff},H_{ff}\le I_2,\qquad K=G\odot H.
 \tag{117.3}
$$

These are actual correct-output Grams, without a calibrated replacement. Their ranks need not equal the channels' Kraus ranks when leakage is present. For a PSD matrix $`X`$ of size at least two, let $`\lambda_1(X)\ge\lambda_2(X)\ge\cdots`$ be its ordered eigenvalues and put $`\kappa_2(X)=\lambda_1(X)+\lambda_2(X)`$.

**Theorem 117.1 (coherent spectral lower bounds).** Let $`S`$ be the union of any nonempty collection of $`m`$ complete original fibres. For either ordering of the two parties,

$$
 \begin{aligned}
 \delta&\ge 2-\frac{\boldsymbol1^*K_S\boldsymbol1}{m^2},\\
 \delta&\ge 2-\frac{\lambda_1(G_S)\operatorname{Tr}H_S}{m^2}
          \ge 2-\frac{2\lambda_1(G_S)}m,\\
 \delta&\ge 2-\frac{\kappa_2(G_S)}m.
 \end{aligned}
 \tag{117.4}
$$

Consequently, $`\delta<1/4`$ implies $`\kappa_2(G_S),\kappa_2(H_S)>7m/4`$ and $`\lambda_1(G_S),\lambda_1(H_S)>7m/8`$. In particular,

$$
 \delta\ge 2-\tfrac14\min\{\kappa_2(G),\kappa_2(H)\},
 \qquad
 \delta<\tfrac14\ \Longrightarrow\
 \kappa_2(G),\kappa_2(H)>7.
 \tag{117.5}
$$

**Proof.** In the sums below, $`f\in S`$ means that the whole fibre $`f`$ belongs to $`S`$. Use the normalized logical/reference input and target vector

$$
 \begin{aligned}
 |\Psi_S\rangle
   &=\frac1{\sqrt m}\sum_{f\in S}|f\rangle_R\otimes|f,+\rangle,
 &|f,+\rangle&=\frac{|f,0\rangle+|f,1\rangle}{\sqrt2},\\
 |\Omega_S\rangle
   &=\frac1{\sqrt m}\sum_{f\in S}|f\rangle_R\otimes|f,f\rangle.
 \end{aligned}
 \tag{117.6}
$$

Since $`\mathcal F(|f,+\rangle\langle g,+|)=|f\rangle\langle g|`$ for equal and unequal fibres, the target output is the pure state $`|\Omega_S\rangle\langle\Omega_S|`$. Let $`\sigma_S`$ be the full physical product output. It is positive of trace one. The reference tags force the entries contributing to its overlap with $`\Omega_S`$ to be the actual correct-output entries of the corresponding input fibres. The compression $`C`$ onto the span of $`|f\rangle_R\otimes|f,f\rangle`$ therefore satisfies

$$
 C_{fg}=\frac1{2m}\sum_{i,j=0}^1\overline{K_{fi,gj}},
 \qquad
 \langle\Omega_S|\sigma_S|\Omega_S\rangle
     =\frac{\boldsymbol1^*K_S\boldsymbol1}{2m^2}.
 \tag{117.7}
$$

The sum is real because $`K_S`$ is Hermitian. The conjugation in the first formula follows from the forward-Gram convention and disappears only in this scalar sum. The full-output observable $`2|\Omega_S\rangle\langle\Omega_S|-I`$ is a Hermitian contraction. Hence trace-norm duality gives

$$
 \delta\ge
 \||\Omega_S\rangle\langle\Omega_S|-\sigma_S\|_1
 \ge 2\bigl(1-\langle\Omega_S|\sigma_S|\Omega_S\rangle\bigr).
 \tag{117.8}
$$

This proves the first line of (117.4), including the entire output leakage. An untagged input cannot replace (117.6) in this argument: wrong-output records from different input fibres could then enter the overlap.

Each correct-output record block is a contraction. Its environment-frame operator is at most the identity. Summing the $`m`$ blocks, and using equality of the nonzero Gram and frame spectra, proves

$$
 0\le G_S,H_S\le mI,\qquad
 \operatorname{Tr}G_S,\operatorname{Tr}H_S\le2m.
 \tag{117.9}
$$

The PSD Schur-product order $`(\lambda_1(G_S)I-G_S)\odot H_S\ge0`$ implies $`\boldsymbol1^*K_S\boldsymbol1\le\lambda_1(G_S)\operatorname{Tr}H_S`$, proving the second line of (117.4).

For the stronger top-two bound, diagonalize $`G_S`$, with eigenvalues $`\lambda_i`$, and let $`h_i`$ be the diagonal entries of $`\overline{H_S}`$ in that eigenbasis. Equation (117.9) gives $`0\le h_i\le m`$ and $`\sum_i h_i\le2m`$. Thus

$$
 \begin{aligned}
 \boldsymbol1^*K_S\boldsymbol1
  &=\operatorname{Tr}(G_S\overline{H_S})
    =\sum_i\lambda_i h_i\\
  &\le\lambda_1h_1+\lambda_2\sum_{i\ge2}h_i
   \le2m\lambda_2+(\lambda_1-\lambda_2)h_1
   \le m(\lambda_1+\lambda_2).
 \end{aligned}
 \tag{117.10}
$$

The trace identity uses Hermiticity: $`\operatorname{Tr}(G_S\overline{H_S})=\sum_{i,j}(G_S)_{ij}(H_S)_{ij}`$. These inequalities include zero eigenvalues and all multiplicities. Substitution in (117.8), and exchange of $`G,H`$, proves the theorem. Trace-norm duality and PSD spectral order are standard; the channel-norm conventions are as in [Watrous, Chapters 1--3](https://cs.uwaterloo.ca/~watrous/TQI/). The different transversal input in [RT II §83](ARITHMETIC_HOLOGRAPHIC_RT_II.md#83-transversal-frame-certificates-and-bilateral-stability-at-quarter-error) uses the same full-output witness principle but does not have this pure coherent target. $`\square`$

For a calibrated party, the two-fibre matrix is $`\bigl[\begin{smallmatrix}I_2&G_{fg}\\G_{gf}&I_2\end{smallmatrix}\bigr]`$, whose top-two eigenvalue sum is $`2+\|G_{fg}\|_1`$ by singular-value decomposition. Thus subquarter error requires $`\|G_{fg}\|_1>3/2`$ for every pair of fibres on each calibrated side.

### 117.2. Exact rigidity at the spectral quarter boundary

**Theorem 117.2 (spectral boundary classification).** Suppose the original product satisfies $`\delta=1/4`$. Then the following conditions are equivalent:

1. At least one party has minimal Kraus rank two.
2. At least one actual correct-output Gram has top-two eigenvalue sum seven.
3. At least one actual correct-output Gram has largest eigenvalue $`7/2`$.

These pairs are exactly the classified marker family of [RT II §82](ARITHMETIC_HOLOGRAPHIC_RT_II.md#82-quarter-error-rigidity-minimal-kraus-product-and-the-complete-rank-two-party-family), including its permitted disphenoids. Both channels are calibrated, and their ranks are $`(4,2)`$ or $`(2,4)`$.

**Proof.** Suppose $`\kappa_2(G)=7`$. Equality holds throughout the relevant bounds (117.8)--(117.10), so $`\operatorname{Tr}(G\bar H)=28`$. Also

$$
 \lambda_1(G)\le4,\qquad
 \lambda_2(G)\ge3,\qquad
 \lambda_3(G)\le1.
 \tag{117.11}
$$

The top-two eigenspace is uniquely defined. In the eigenbasis used in (117.10), the exact deficit identity is

$$
 \begin{split}
 4(\lambda_1+\lambda_2)-\sum_i\lambda_i h_i
  ={}&\lambda_2\left(8-\sum_i h_i\right)
       +(\lambda_1-\lambda_2)(4-h_1)\\
    &+\sum_{i\ge3}(\lambda_2-\lambda_i)h_i.
 \end{split}
 \tag{117.12}
$$

All terms are nonnegative, and the left side is zero. Equation (117.11) makes $`\lambda_2>0`$ and every $`\lambda_2-\lambda_i>0`$ for $`i\ge3`$. Hence $`\operatorname{Tr}H=8`$ and all $`h_i=0`$ for $`i\ge3`$. Since $`h_1,h_2\le4`$, both equal four. Positivity of $`\bar H`$ eliminates the rows outside the top-two space, and positivity of $`4I-\bar H`$ eliminates off-diagonal entries in the two remaining rows. If $`\Pi`$ denotes the top-two spectral projection of $`G`$, this proves

$$
 \bar H=4\Pi.
 \tag{117.13}
$$

The positive defects $`I_2-H_{ff}`$ have total trace zero, so every $`H_{ff}=I_2`$. Each original basis input has correct-output record of norm one; all its wrong-output Stinespring components vanish. Thus the actual $`B`$ is calibrated. Only now may its minimal Kraus rank be identified with $`\operatorname{rank}H=2`$. The original-channel theorem of RT II §82 applies without a rank or leakage assumption on $`A`$, and proves its calibration, rank four and the complete family. Exchanging the parties covers the other case of condition 2.

After the environment isometries and simultaneous within-fibre bit swaps of that classification, the family has

$$
 a_{fi}=\overline{b_{fi}}\otimes m_i,\qquad
 m_i=\sqrt{\tfrac78}\,e_0+(-1)^i\sqrt{\tfrac18}\,e_1.
 \tag{117.14}
$$

Each pair $`(b_{f0},b_{f1})`$ is an orthonormal qubit basis. Its four Bloch axes are balanced and have the Gram of

$$
 \begin{gathered}
 (x,y,z),\ (x,-y,-z),\ (-x,y,-z),\ (-x,-y,z),\\
 x^2+y^2+z^2=1,\quad x^2,y^2,z^2\ge\tfrac27.
 \end{gathered}
 \tag{117.15}
$$

The full arbitrary-reference norm of this family is exactly $`1/4`$ by RT II §82.11. Balance implies $`\sum_f|b_{fi}\rangle\langle b_{fi}|=2I_2`$ for each $`i`$. The environment-frame operators are consequently

$$
 \sum_{f,i}|b_{fi}\rangle\langle b_{fi}|=4I_2,\qquad
 \sum_{f,i}|a_{fi}\rangle\langle a_{fi}|
     =I_2\otimes\operatorname{diag}(\tfrac72,\tfrac12).
 \tag{117.16}
$$

Their nonzero eigenvalues are the nonzero Gram eigenvalues. Thus every classified pair has, in one party ordering,

$$
 \operatorname{spec}G=(\tfrac72,\tfrac72,\tfrac12,\tfrac12,0,0,0,0),
 \qquad
 \operatorname{spec}H=(4,4,0,0,0,0,0,0).
 \tag{117.17}
$$

This proves that condition 1 implies both 2 and 3, and proves sharpness at quarter error. Finally condition 3 implies $`\kappa_2\le7`$, whereas (117.5) at $`\delta=1/4`$ gives $`\kappa_2\ge7`$. Hence condition 3 implies 2. $`\square`$

### 117.3. Dominant two-dimensional record spaces

**Proposition 117.3 (full-record concentration and a calibrated polar chart).** If $`\delta<1/4`$, each party's actual correct-output record-frame operator has a unique top-two environment subspace $`E`$. For the first party, write its correct-output record blocks as $`A_f`$, and let $`\Pi_E`$ project onto $`E`$. Then

$$
 \lambda_2(G)>3,\qquad \lambda_3(G)<1,\qquad
 d_A:=\sum_f\bigl(2-\operatorname{Tr}(A_f^*\Pi_E A_f)\bigr)
       =8-\kappa_2(G)\le4\delta<1,
 \tag{117.18}
$$

and

$$
 A_f^*\Pi_E A_f\ge(1-d_A)I_2>0
 \quad\hbox{for every original fibre }f.
 \tag{117.19}
$$

Here $`d_A`$ is the total squared norm of all original wrong-output records together with that of correct-output records perpendicular to $`E`$. The same statements hold for $`B`$.

If the party is calibrated, in environment coordinates $`E\oplus E^\perp`$ its exact record blocks can be written

$$
 \begin{aligned}
 A_f&=\begin{bmatrix}C_f\\R_f\end{bmatrix},&
 C_f&=U_f\sqrt{I_2-R_f^*R_f},\qquad U_f\in U(2),\\
 \sum_f\|R_f\|_F^2&=d_A<1,&
 \sum_f C_fR_f^*&=0.
 \end{aligned}
 \tag{117.20}
$$

This representation retains the full extra environment and the same original channel.

**Proof.** Theorem 117.1 gives $`\kappa_2(G)\ge8-4\delta>7`$. Together with $`\lambda_1(G)\le4`$ and $`\operatorname{Tr}G\le8`$, this gives the first two inequalities in (117.18), and hence a strict top-two frame gap. Tracing that frame operator on $`E`$ proves the formula for $`d_A`$. The full Stinespring isometry has total squared norm eight on the eight input basis states. Splitting this sum into the three indicated record parts proves the physical interpretation of $`d_A`$.

Each defect $`I_2-A_f^*\Pi_E A_f`$ is PSD and has trace at most $`d_A`$. Its largest eigenvalue is at most its trace, proving (117.19). Under calibration, $`C_f^*C_f+R_f^*R_f=I_2`$, and (117.19) makes $`C_f`$ invertible. Its right polar decomposition gives $`U_f`$. The last equation of (117.20) expresses the fact that the spectral subspace $`E`$ reduces the environment-frame operator. No projection followed by renormalization of the physical channel has been performed. $`\square`$

### 117.4. A uniform but nonnumerical separation

**Theorem 117.4 (uniform spectral separation).** There exists $`\varepsilon>0`$, depending only on the fixed target and the fixed finite channel spaces, such that every original product with $`\delta<1/4`$ satisfies

$$
 \kappa_2(G),\kappa_2(H)\ge7+\varepsilon,\qquad
 \lambda_1(G),\lambda_1(H)\ge\tfrac72+\tfrac\varepsilon2.
 \tag{117.21}
$$

Thus the dominant-plane projections of Proposition 117.3 have uniform bounds $`d_A,d_B\le1-\varepsilon`$ and $`A_f^*\Pi_EA_f\ge\varepsilon I_2`$, and similarly for $`B`$. No value of $`\varepsilon`$ is specified; the assertion is vacuous if no subquarter product exists.

**Proof.** The original CPTP space is compact in its Choi representation: $`J\ge0`$, $`\operatorname{Tr}_{\rm out}J=I_8`$, and $`\operatorname{Tr}J=8`$. The product of the two fixed channel spaces is compact. With $`J_A=\sum_{i,j}|i\rangle\langle j|\otimes A(|i\rangle\langle j|)`$ and the fixed isometry $`Q|i\rangle=|i\rangle\otimes|f(i)\rangle`$,

$$
 G(A)=\overline{Q^*J_AQ}.
 \tag{117.22}
$$

This proves representation-independent continuity of the actual Gram, including at Kraus-rank changes. Ordered eigenvalues and their top-two sum are continuous. The original error is also continuous, since

$$
 |\delta(A,B)-\delta(A',B')|
    \le\|A-A'\|_\diamond+\|B-B'\|_\diamond.
 \tag{117.23}
$$

This follows from the tensor-product triangle inequality and the diamond norm one of channels and encoding channels.

If the first pair of inequalities in (117.21) failed, choose subquarter pairs with the smaller top-two sum tending to seven. Compactness gives a convergent subsequence. At its limit, one actual Gram has top-two sum seven, and continuity gives $`\delta\le1/4`$. Theorem 117.1 forces $`\delta\ge1/4`$, so equality holds. Theorem 117.2 identifies the limit as an actual section-82 marker center.

[RT III §89](ARITHMETIC_HOLOGRAPHIC_RT_III.md#89-an-unrestricted-local-quarter-minimum-from-analytic-descent-at-the-scalar-cone) provides a neighborhood of every such center in the full original channel space on which $`\delta\ge1/4`$. Its statement includes arbitrary ranks and leakage, exchanged parties and all boundary disphenoids. Its original-channel topology is justified there by continuous canonical Choi-square-root lifts, not by a fixed-rank or calibrated restriction. The convergent subsequence eventually lies in that neighborhood, contradicting its strict subquarter errors. This proves the first pair in (117.21). The largest-eigenvalue bounds follow from $`\kappa_2\le2\lambda_1`$, and the remaining bounds follow from Proposition 117.3. $`\square`$

The limit proof does not assume that the strict subquarter set is closed. The quantitative inequalities, the exact quarter-boundary classification and the nonconstructive positive separation have distinct content. None removes all possible genuinely complex or lower-rank competitors. The unrestricted global quarter-optimum problem remains open.

## 追加锚（本行以下为增补区）

## 118. Feasible-chord polarization and full-rank opposite stresses

### 118.1. Original domain and common-stress hypotheses

Keep the original local channels $\mathbb C^8\to\mathbb C^4$, their four prescribed two-coordinate fibres, the fixed correlated encoding, an arbitrary reference, and the unhalved diamond error. On the full calibrated domain this error is

$$
\begin{aligned}
\mathcal E&=\{K=K^*\succeq0:K_{ff}=I_2\},\\
F(G,H)&=\max_{(\rho,W)\in\mathcal C}
                 2\operatorname{Tr}[(T-G\odot H)W],\\
\mathcal C&=\{(\rho,W):\rho\succeq0,\ \rho\text{ is fibre-block diagonal},
                  \ \operatorname{Tr}\rho=1,\ 0\preceq W\preceq\rho\},\\
T_{ff}&=I_2,\qquad T_{fg}=\tfrac12J_2\quad(f\ne g).
\end{aligned}
\tag{118.1}
$$

Throughout the exclusion arguments, assume that $(G,H)$ is a local minimum on the entire $\mathcal E^2$, including nearby competitors of different ranks, and that

$$
\operatorname{rank}G=7,\qquad
\ker G=\mathbb C a,\qquad a_i\ne0\ (1\le i\le8),
\qquad 0<F(G,H)<\tfrac12.
\tag{118.2}
$$

The original common-stress and quotient results of [RT III §§95 and 98](ARITHMETIC_HOLOGRAPHIC_RT_III.md#98-curved-common-stress-tests-and-finite-principal-quotients) give

$$
\begin{aligned}
P&=\alpha\operatorname{diag}(a)R\operatorname{diag}(\bar a)\succeq0,
       &\alpha&>0,\\
R&\succeq0,\qquad R_{ii}=1,
       &G&=H\odot\bar R,\qquad PH=0.
\end{aligned}
\tag{118.3}
$$

All cross-fibre entries of $H$ and $P$ are nonzero. Fix $a$ and one normalization $(\alpha,P)$ in (118.3). Every canonical common normer has first stress $`\alpha_Waa^*`$ and second stress $(\alpha_W/\alpha)P$, with $\alpha_W>0$. The canonical subset is the complete set of normers whose original first-order drift is nonnegative against every feasible pair. These statements concern the original full-domain minimum, rather than an independently chosen witness for each block.

For a positive semidefinite $K$, let $N_K$ be the orthogonal projection onto $\ker K$ and $K^+$ its Moore–Penrose inverse. Set

$$
\begin{aligned}
\mathcal T_H&=\{D=D^*:D_{ff}=0,\ N_HDN_H=0\},\\
E(D)&=-\bar R\odot D,\\
m(D)&=-\sum_{\substack{i,j\\f(i)\ne f(j)}}
                  \frac{\overline{P_{ij}}}{H_{ij}}D_{ij}^{\,2},\\
Q(D)&=m(D)+\alpha a^*E(D)G^+E(D)a
                      +\operatorname{Tr}(PDH^+D).
\end{aligned}
\tag{118.4}
$$

The sum is ordered and uses complex squares. It is real for Hermitian $D$. The formula for $m$ is also defined on zero-fibre Hermitian matrices outside $\mathcal T_H$. The full curved criterion gives $Q(D)\ge0$ for every $D\in\mathcal T_H$, with the same fixed $P$.

### 118.2. Exact curved paths and a feasible chord

**Lemma 118.1 (full-domain chord polarization).** Under (118.1)–(118.4), let $`D_0=D_0^*`$ have zero original fibre blocks, $D_0P=0$, and $m(D_0)=0$. Suppose $H+sD_0\in\mathcal E$ for all sufficiently small $s\ge0$. Then the real polarization $B_m(D_0,D)$ of $m$ vanishes for every $D\in\mathcal T_H$. Equivalently, the Hermitian matrix

$$
A(D_0)_{ij}=
\frac{P_{ij}\overline{(D_0)_{ij}}}{\overline{H_{ij}}}
\quad(f(i)\ne f(j)),\qquad A(D_0)_{ff}=0
\tag{118.5}
$$

annihilates the whole $\mathcal T_H$ for the real trace pairing.

**Proof.** Put $E_0=-\bar R\odot D_0$. The original stress identity gives, coordinate by coordinate,

$$
(E_0a)_i=-\frac{(D_0P)_{ii}}{\alpha\bar a_i}=0.
\tag{118.6}
$$

Therefore $G+sE_0$ is feasible for both signs near zero: it preserves the entire kernel $\mathbb C a$, and its positive restriction to the orthogonal complement remains positive. Choose fixed $c_G,c_H>0$ large enough that

$$
G_1=G+E_0/c_G\in\mathcal E,
\qquad H_1=H+D_0/c_H\in\mathcal E.
\tag{118.7}
$$

Fix any $D\in\mathcal T_H$. Corollary 98.3 gives $N_GE(D)N_G=0$ and complete first-order product cancellation. The exact curved realization of Lemma 98.1 supplies smooth two-sided feasible paths

$$
\begin{aligned}
g_D(t)&=G+tE(D)+t^2C_G+O(t^3),\\
h_D(t)&=H+tD+t^2C_H+O(t^3),
\end{aligned}
\qquad (C_G)_{ff}=(C_H)_{ff}=0,
\tag{118.8}
$$

whose second coefficients satisfy

$$
\alpha\operatorname{Tr}(aa^*C_G)
 =\alpha a^*E(D)G^+E(D)a,
\qquad
\operatorname{Tr}(PC_H)=\operatorname{Tr}(PDH^+D).
\tag{118.9}
$$

These paths retain the original fibre constraints and may move the kernels. Explicitly, for $`K=V^*V`$ and a tangent $D_K$, the construction is

$$
\begin{aligned}
X&=VK^+D_K\bigl((I-N_K)/2+N_K\bigr),\\
V_f(t)&=(V_f+tX_f)(I_2+t^2X_f^*X_f)^{-1/2},\\
C_K&=X^*X-\tfrac12(MK+KM),
\qquad M=\operatorname{blockdiag}_f(X_f^*X_f).
\end{aligned}
\tag{118.10}
$$

The fibre columns are orthonormal for both signs of $t$. For every complementary stress $ZK=0$, the $M$ terms disappear under the trace and $\operatorname{Tr}(ZC_K)=\operatorname{Tr}(ZD_KK^+D_K)$, proving (118.9).

Fix any real $\varepsilon$. For sufficiently small positive $s$ form the exact convex mixtures

$$
\begin{aligned}
G_s&=(1-c_Gs)g_D\!\left(\frac{\varepsilon s}{1-c_Gs}\right)+c_GsG_1,\\
H_s&=(1-c_Hs)h_D\!\left(\frac{\varepsilon s}{1-c_Hs}\right)+c_HsH_1.
\end{aligned}
\tag{118.11}
$$

Both matrices are feasible. Negative $\varepsilon$ is allowed because (118.8) is two-sided; the weights remain nonnegative for small positive $s$. The constants $c_G,c_H$ need not be equal. Expansion gives

$$
\begin{aligned}
G_s&=G+s(E_0+\varepsilon E(D))+\varepsilon^2s^2C_G+O(s^3),\\
H_s&=H+s(D_0+\varepsilon D)+\varepsilon^2s^2C_H+O(s^3).
\end{aligned}
\tag{118.12}
$$

Indeed the weight cancels the denominator in every linear term, while the quadratic coefficient is $\varepsilon^2s^2/(1-c_Ks)=\varepsilon^2s^2+O(s^3)$. With $L=T-G\odot H$, full original first-order cancellation therefore yields

$$
\begin{aligned}
T-G_s\odot H_s&=L+s^2K_\varepsilon+O(s^3),\\
K_\varepsilon&=\bar R\odot(D_0+\varepsilon D)\odot(D_0+\varepsilon D)
 -\varepsilon^2(C_G\odot H+G\odot C_H).
\end{aligned}
\tag{118.13}
$$

For completeness, common-witness selection applies at this fixed $D,\varepsilon$. Let $\mathcal A$ be the full compact convex set of normers at $L$ and let $\mathcal A_0$ be its complete canonical common subset. For any $M>0$, mix the feasible paths (118.11) with arbitrary $G',H'\in\mathcal E$ at weight $Ms^2$. The compact maximum derivative formula and local minimality imply

$$
\begin{aligned}
\max_{(\rho,W)\in\mathcal A}
 \{2\operatorname{Tr}(K_\varepsilon W)+Mb(W;G',H')\}&\ge0,\\
b(W;G',H')&=-2\operatorname{Tr}
 [((G'-G)\odot H+G\odot(H'-H))W].
\end{aligned}
\tag{118.14}
$$

For each fixed $M$, finite affine separation gives one normer satisfying all inequalities inside this maximum simultaneously. Otherwise compactness gives a finite inconsistent family, and nonnegative separating weights produce an averaged feasible drift contradicting (118.14). The zero drift gives $2\operatorname{Tr}(K_\varepsilon W)\ge0$. A convergent subsequence as $M\to\infty$ lies in the complete $\mathcal A_0$ and retains this inequality.

The common stress trace identities, (118.9), and the positive factor $\alpha_W/\alpha$ turn the last inequality into

$$
m(D_0+\varepsilon D)+\varepsilon^2
 \bigl[\alpha a^*E(D)G^+E(D)a+\operatorname{Tr}(PDH^+D)\bigr]\ge0.
\tag{118.15}
$$

Witness selection was made only for the fixed $D,\varepsilon$; proportionality of all common stresses gives the same scalar form. Since $m(D_0)=0$, (118.15) is

$$
2\varepsilon B_m(D_0,D)+\varepsilon^2Q(D)\ge0
\qquad(\varepsilon\in\mathbb R).
\tag{118.16}
$$

Both signs of arbitrarily small $\varepsilon$ force $B_m(D_0,D)=0$. Reversing trace indices gives $B_m(D_0,D)=-\operatorname{Tr}(A(D_0)D)$, proving the lemma. Each fixed $\varepsilon$ uses its own sufficiently small positive $s$; no uniform interval over unbounded $\varepsilon$ is required. ∎

### 118.3. Rank-raising half stars

**Theorem 118.2 (deficient stress excludes two full halves).** Under (118.1)–(118.4), suppose $\operatorname{rank}H=4$ and $\operatorname{rank}P\le3$. No partition $A,B$ into two unions of two original fibres can have both $H_{AA}\succ0$ and $H_{BB}\succ0$.

**Proof.** Factor $`H=B_\circ^*B_\circ`$ with $B_\circ$ a full-row-rank $4\times8$ matrix, and $`P=V^*V`$ with $V$ having at most three rows. Complementarity gives $`VB_\circ^*=0`$. The square restrictions $B_A,B_B$ are invertible. Choose nonzero $m_B\in\ker V_B$ and put

$$
\begin{aligned}
m_A&=0,\qquad n_B=0,\qquad
n_A=-B_A^*(B_B^*)^{-1}m_B,\\
w&=n-m=B_\circ^*\eta,\qquad
\eta=-(B_B^*)^{-1}m_B.
\end{aligned}
\tag{118.17}
$$

Then $Pn=Pm=0$, because $V_An_A=V_Bm_B=0$. Both vectors are nonzero. With $N=N_H$, one has $Nn=Nm=u\ne0$: otherwise $m\in\operatorname{range}H$ supported on $B$ would force $`B_A^*\eta'=0`$ for its representing vector $\eta'$, and hence $m=0$.

For real $y$ define

$$
\begin{aligned}
D_y&=(1+iy)nm^*+(1-iy)mn^*,\\
v_y&=\tfrac12(n+m+iy(n-m)),\\
D_y&=2v_yv_y^*-\tfrac12(1+y^2)ww^*.
\end{aligned}
\tag{118.18}
$$

Since $w\in\operatorname{range}H$, the last identity proves $H+sD_y\succeq0$ for sufficiently small $s\ge0$. For example it suffices that $`s(1+y^2)w^*H^+w/2\le1`$. The fibre blocks remain $I_2$, and $D_yP=0$. The paired direction $-\bar R\odot D_y$ annihilates $a$ by (118.6), so its $G$ line is feasible for both signs near zero. The entire original first-order coefficient cancels.

The fixed-direction common-normer selection used in (118.14), applied to these two affine paths with positive $s$, gives $m(D_y)\ge0$ for every real $y$. Here

$$
\begin{aligned}
m(D_y)&=-2\operatorname{Re}((1+iy)^2c),\\
c&=\sum_{i\in A,j\in B}
       \frac{\overline{P_{ij}}}{H_{ij}}n_i^2\bar m_j^{\,2}.
\end{aligned}
\tag{118.19}
$$

The constant and quadratic coefficients have opposite signs, so $\operatorname{Re}c=0$; the remaining linear coefficient then gives $\operatorname{Im}c=0$. Consequently

$$
D_0=nm^*+mn^*,\qquad D_i=i(nm^*-mn^*),
\qquad m(D_0)=m(D_i)=0.
\tag{118.20}
$$

Lemma 118.1 shows that $A(D_0)$ annihilates all of $\mathcal T_H$. Also $D_i\in\mathcal T_H$, since $Nn=Nm$. Its two curvature costs vanish because $D_iP=0$ and $E(D_i)a=0$. Thus $Q(D_i)=0$, and nonnegativity of $Q$ on the entire $\mathcal T_H$ makes $D_i$ a radical vector there. The cost polarizations vanish as well, so $A(D_i)$ annihilates the same whole space.

The normal space of $\mathcal T_H$ is the sum of the original fibre-block-diagonal matrices and the matrices supported on $\ker H$. If $`\operatorname{range}U^*=\ker H`$, this gives

$$
A(D_0)=\Lambda_0+U^*Y_0U,
\qquad A(D_i)=\Lambda_i+U^*Y_iU,
\tag{118.21}
$$

with Hermitian $\Lambda_0,\Lambda_i$ fibre-block diagonal and Hermitian $Y_0,Y_i$. This is the finite-dimensional orthogonal-complement identity for an intersection of two real linear spaces. Half the first identity plus $i/2$ times the second produces a matrix $Z$ supported only on $A\times B$:

$$
\begin{aligned}
Z_{ij}&=\frac{P_{ij}\bar n_i m_j}{\overline{H_{ij}}}
       \quad(i\in A,j\in B),\\
Z&=\Lambda+U^*YU,
\qquad HZ=H\Lambda,\qquad ZH=\Lambda H.
\end{aligned}
\tag{118.22}
$$

The combined multipliers need not be Hermitian. For each original fibre $f\subset A$, the $f$ columns of $Z$ vanish, so $(HZ)_{ff}=0$ and $H_{ff}=I_2$ force $\Lambda_{ff}=0$. For $g\subset B$, the $g$ rows vanish, and $(ZH)_{gg}=0$ similarly gives $\Lambda_{gg}=0$. Hence $\Lambda=0$ and $HZ=ZH=0$.

Every column of $Z$ belongs to $\ker H$ and is supported on $A$. Since $H_{AA}\succ0$, each column is zero. This contradicts (118.22): some $n_i,m_j$ are nonzero, and every cross-fibre coefficient $P_{ij}/H_{ij}$ is nonzero. ∎

### 118.4. Subquarter strict complementarity

**Corollary 118.3 (full opposite stress at rank four).** Under (118.1)–(118.4), if $\operatorname{rank}H=4$ and $F(G,H)<1/4$, then

$$
\operatorname{rank}P=\operatorname{rank}R=4,
\qquad \operatorname{range}P=\ker H,
\qquad P|_{\ker H}\succ0.
\tag{118.23}
$$

**Proof.** Complementarity gives $\operatorname{rank}P\le4$. Suppose it is at most three. Theorem 114.3 forbids a complementary pair of two-fibre principal Grams from having exactly one positive-definite member. Theorem 118.2 forbids two positive-definite members. Therefore all six two-fibre principal Grams are singular, contrary to the subquarter exclusion in §115. Thus $\operatorname{rank}P=4$. The nonsingular diagonal congruence in (118.3) gives $\operatorname{rank}R=4$. A rank-four positive semidefinite matrix with range contained in the four-dimensional $\ker H$ has exactly that range and is positive definite there. ∎

The corollary is a necessary restriction on the remaining full-support rank-$(7,4)$ calibrated local minima. It does not exclude the full-rank-stress class, the lower opposite ranks, or the global representative classes retained in Corollary 113.5. The unrestricted quarter optimum remains open. The original-channel reduction does not assert that an arbitrary leaking local minimum preserves these ranks or hypotheses under calibration.

## 追加锚（本行以下为增补区）

## 119. Coherent-input bounds for diffuse and isotropic quotient stresses

### 119.1. Actual channels and the full quotient hypothesis

Keep the original channels $`A,B:\mathcal L(\mathbb C^8)\to\mathcal L(\mathbb C^4)`$, the four prescribed two-coordinate fibres, the fixed correlated encodings, and the unhalved arbitrary-reference diamond error $`\delta`$ of [RT III §91.1](ARITHMETIC_HOLOGRAPHIC_RT_III.md#911-original-channels-forward-grams-and-the-adaptive-theorem). Let $`G,H`$ be their actual correct-output forward Grams, with inner products conjugate-linear in the first argument. Thus $`G_{ff},H_{ff}\preceq I_2`$, and the encoded product coefficients use the transpose of $`K=G\odot H`$. Put

$$
L=T-K,\qquad T_{ff}=I_2,\qquad T_{fg}=\tfrac12J_2\quad(f\ne g).
\tag{119.1}
$$

The hypotheses in this section are the full eight-coordinate identities

$$
\begin{aligned}
R&\succeq0,\qquad R_{ii}=1,\qquad a_i\ne0,\qquad\alpha>0,\\
G&=H\odot\bar R,\qquad
P=\alpha\operatorname{diag}(a)R\operatorname{diag}(\bar a)\succeq0,
\qquad PH=0.
\end{aligned}
\tag{119.2}
$$

They are imposed on the actual correct-output Grams; no quotient is inferred for arbitrary leaking channel pairs. Write

$$
\lambda=\|P\|_{\mathrm{op}}>0,\qquad
p_i=P_{ii}>0,\qquad r=\frac{\operatorname{Tr}P}{\lambda},
\qquad m=\frac{\max_i p_i}{\lambda}.
\tag{119.3}
$$

### 119.2. One original coherent-reference witness

**Lemma 119.1 (weighted tagged input).** Under (119.1)–(119.2), a reciprocal diagonal unitary change makes $`a`$ positive while preserving the entire original encoded product channel. In that gauge, set

$$
\begin{aligned}
b_i&=\sqrt{p_i},& t&=\sum_i b_i^2=\operatorname{Tr}P,&
\beta_f&=\|b_f\|_2,\\
S&=\sum_f\beta_f,& c&=S^2,&
A_0&=\sum_i b_i,\qquad s_f=\sum_{i\in f}b_i.
\end{aligned}
\tag{119.4}
$$

Then, with all original leakage retained,

$$
\delta\ge\frac{2}{c}\left[
 t+\frac{A_0^2-\sum_f s_f^2}{2}
       -\operatorname{Tr}\bigl((H\odot H)P\bigr)\right].
\tag{119.5}
$$

**Proof.** Choose $`E_{ii}=\bar a_i/|a_i|`$. Multiply the entire $`i`$-th Stinespring column of $`A`$ by $`\bar E_{ii}`$ and that of $`B`$ by $`E_{ii}`$. Both maps remain isometries, and their input phases cancel in the correlated encoding on every matrix unit, including every wrong-output component. The forward Grams and quotient data transform as

$$
G'=EGE^*,\quad H'=E^*HE,\quad a'=Ea,\quad
R'=E^{*2}RE^2,\quad P'=E^*PE.
\tag{119.6}
$$

Thus (119.2) persists, $`a'`$ is positive, and both the full error and every entry of $`K`$ are unchanged. Suppress primes. In particular

$$
R_{ij}=\frac{P_{ij}}{b_i b_j},\qquad
b^*Kb=\operatorname{Tr}\bigl((H\odot H)P\bigr),\qquad
b^*Tb=t+\frac{A_0^2-\sum_f s_f^2}{2}.
\tag{119.7}
$$

The trace in the middle is $`\sum_{i,j}H_{ij}^2P_{ji}`$; it uses a complex square, not a squared modulus.

A block-density realization of the witness is

$$
W=\frac{bb^*}{c},\qquad
\rho=\bigoplus_f\frac{b_f b_f^*}{S\beta_f},\qquad
\operatorname{Tr}\rho=1,\qquad0\preceq W\preceq\rho.
\tag{119.8}
$$

Indeed, weighted Cauchy–Schwarz gives $`|b^*x|^2\le S\sum_f|b_f^*x_f|^2/\beta_f=cx^*\rho x`$. To check the original normalization directly, use the unit input with four orthogonal reference tags

$$
|\psi\rangle=\sum_f\sum_{i\in f}
       \frac{b_i}{\sqrt{S\beta_f}}|i\rangle\otimes|f\rangle_R.
\tag{119.9}
$$

Compress the target-minus-product output to the span of $`|f,f\rangle\otimes|f\rangle_R`$. The target output is entirely in this space. The compressed error $`C`$ and a unit vector $`v`$ in it satisfy

$$
C_{fg}=\frac{\sum_{i\in f,j\in g}b_i b_j L_{ji}}
                    {S\sqrt{\beta_f\beta_g}},\qquad
v_f=\sqrt{\frac{\beta_f}{S}},\qquad
v^*Cv=\frac{b^*L^{\mathsf T}b}{c}=\frac{b^*Lb}{c}.
\tag{119.10}
$$

The transpose is required by the forward-Gram convention; the last equality holds because $`b`$ is real and $`L`$ is Hermitian. The complementary product output is positive. Pinching therefore bounds the full trace norm below by $`\|C\|_1+\operatorname{Tr}C=2\operatorname{Tr}C_+\ge2v^*Cv`$. Equations (119.7) and (119.10) prove (119.5). ∎

### 119.3. Calibrated spectral bounds and diagonal concentration

**Theorem 119.2 (diffuse-stress obstruction).** Suppose (119.2) holds and the actual channels are calibrated, so $`G_{ff}=H_{ff}=I_2`$. Their original error $`F(G,H)=\delta`$ obeys

$$
0<m\le\tfrac34,\qquad
F(G,H)\ge\max\left\{0,\frac{r}{4m}-\frac4r\right\}
       \ge\max\left\{0,\frac r3-\frac4r\right\}.
\tag{119.11}
$$

For $`15/4\le r\le4`$, the stronger bound is

$$
F(G,H)\ge
\frac{\left(5\sqrt3/2+\sqrt{r-15/4}\right)^2-16}{4r}.
\tag{119.12}
$$

Consequently

$$
F(G,H)<\tfrac14\quad\Longrightarrow\quad
r<\frac{1129}{300}.
\tag{119.13}
$$

If $`P`$ is a positive scalar multiple of a rank-four orthogonal projection, then

$$
F(G,H)\ge\frac{6+5\sqrt3}{32}>\frac13>\frac14.
\tag{119.14}
$$

**Proof.** Factor $`H=B^*B`$. Its four original column blocks $`B_f`$ are isometries. Thus $`BB^*=\sum_fB_fB_f^*\preceq4I`$, and $`H\preceq4I`$. If $`N`$ projects onto $`\ker H`$, positivity and $`PH=0`$ give

$$
H\preceq4(I-N),\qquad
N_{ii}\le\tfrac34,\qquad P\preceq\lambda N,
\qquad p_i\le\tfrac34\lambda.
\tag{119.15}
$$

The Schur product theorem gives $`H\odot H\succeq0`$, with trace eight. Hence

$$
\operatorname{Tr}\bigl((H\odot H)P\bigr)\le8\lambda,
\qquad\sum_f s_f^2\le2t,\qquad
A_0\ge\frac{t}{\sqrt{\lambda m}},\qquad c\le4t.
\tag{119.16}
$$

The target term in (119.7) is at least $`A_0^2/2`$. When $`t^2/(\lambda m)-16\lambda\ge0`$, Lemma 119.1 and (119.16) allow division by the upper bound $`c\le4t`$, giving the first lower bound in (119.11). When that numerator is negative, use $`F\ge0`$ instead. The cap $`m\le3/4`$ proves the second bound.

For the refinement, put $`x_i=p_i/\lambda`$. These eight numbers lie in $`[0,3/4]`$ and sum to $`r`$. On the compact capped simplex a minimum of $`\sum_i\sqrt{x_i}`$ exists. If two coordinates are interior, move them at fixed sum to an endpoint of their feasible segment. Concavity makes at least one endpoint no larger. Repetition leaves at most one fractional coordinate. For $`15/4\le r\le4`$, the resulting multiset is five copies of $`3/4`$, one copy of $`r-15/4`$, and two zeros. Therefore

$$
\frac{A_0}{\sqrt\lambda}\ge
       \frac{5\sqrt3}{2}+\sqrt{r-\frac{15}{4}}.
\tag{119.17}
$$

The square of this lower bound exceeds sixteen throughout the interval: at its left endpoint the difference is $`11/4`$. Thus the denominator substitution is again legitimate, proving (119.12). Its numerator minus $`r`$ is

$$
\left(\frac{5\sqrt3}{2}+\sqrt{r-\frac{15}{4}}\right)^2-16-r
       =-1+5\sqrt3\sqrt{r-\frac{15}{4}}.
\tag{119.18}
$$

This is nonnegative exactly for $`r\ge15/4+1/75=1129/300`$. For $`r>4`$, (119.11) already gives $`F>1/3`$, while $`r<15/4`$ satisfies (119.13). Finally a scalar rank-four projection has $`r=4`$, and (119.12) becomes (119.14). ∎

### 119.4. A uniform gap retaining arbitrary leakage

**Theorem 119.3 (isotropic stress with actual leakage).** Suppose the original channels satisfy (119.2) and

$$
P=\lambda N_0,\qquad\lambda>0,\qquad
N_0=N_0^*=N_0^2,\qquad\operatorname{rank}N_0=4.
\tag{119.19}
$$

Then $`\delta>2/5`$. It is enough that $`\operatorname{ran}N_0\subseteq\ker H`$; equality with the entire opposite kernel is not required.

**Proof.** Use the physical gauge of Lemma 119.1. Suppose $`\delta\le2/5`$. For the original basis input $`|i\rangle`$, the correct output has probability $`G_{ii}H_{ii}=H_{ii}^2`$, since $`R_{ii}=1`$. Measuring whether the output is the target basis vector gives

$$
\delta\ge2(1-H_{ii}^2),\qquad
H_{ii}\ge\sqrt{\frac45}>\frac89.
\tag{119.20}
$$

The actual correct-output blocks $`B_f`$ are contractions, so $`BB^*\preceq4I`$ still holds. With $`N`$ the projection onto $`\ker H`$, (119.19) and $`PH=0`$ imply $`N_0\preceq N`$. Consequently

$$
H\preceq4(I-N),\qquad
x_i:=\frac{P_{ii}}{\lambda}\le N_{ii}
       \le1-\frac{H_{ii}}4<\frac79,
\qquad\sum_i x_i=4.
\tag{119.21}
$$

The same finite concavity argument, now on the cap-$`7/9`$ simplex of sum four, leaves five copies of $`7/9`$, one of $`1/9`$, and two zeros. Thus

$$
\frac{A_0}{\sqrt\lambda}\ge\frac{5\sqrt7+1}{3},
\qquad A_0^2\ge\lambda\frac{176+10\sqrt7}{9}.
\tag{119.22}
$$

The original target identity still gives $`2b^*Tb\ge A_0^2`$. Also $`H\odot H\succeq0`$, $`\operatorname{Tr}(H\odot H)=\sum_iH_{ii}^2\le8`$, and $`c\le4\operatorname{Tr}P=16\lambda`$. Since $`A_0^2-16\lambda>0`$, the leakage-safe Lemma 119.1 yields

$$
\delta\ge\frac{A_0^2-16\lambda}{16\lambda}
       \ge\frac{16+5\sqrt7}{72}>\frac25.
\tag{119.23}
$$

The last strict inequality is equivalent to $`25\sqrt7>64`$, whose squared form is $`4375>4096`$. This contradicts the assumption and proves the theorem. ∎

### 119.5. The full-support local-minimum consumer

**Corollary 119.4.** Let $`(G,H)`$ be a local minimum on the full calibrated domain $`\mathcal E^2`$ of (118.1), with $`\operatorname{rank}G=7`$, a full-support kernel vector, and $`0<F(G,H)<1/4`$. Every common stress supplied by the quotient theorem satisfies

$$
\frac{\operatorname{Tr}P}{\|P\|_{\mathrm{op}}}
              <\frac{1129}{300}.
\tag{119.24}
$$

For the remaining rank-$`(7,4)`$ class, its four positive stress eigenvalues in Corollary 118.3 cannot be equal.

**Proof.** [RT III Lemma 95.2](ARITHMETIC_HOLOGRAPHIC_RT_III.md#952-one-rank-seven-side-gives-a-supported-psd-quotient) gives the full identity (119.2), because the first kernel has full support. Apply Theorem 119.2. Section 118 gives rank four and full opposite-kernel range in the stated subquarter rank-$`(7,4)`$ case, and (119.14) excludes equal positive eigenvalues. ∎

This conclusion concerns the actual common stress, rather than a freely chosen stress with the same support. Nonisotropic rank-four stresses satisfying (119.24), opposite rank three, and the global representative class with both ranks at most six remain outside these exclusions. Theorem 119.3 imposes its quotient on the full actual leaking Grams; it does not transfer calibrated local-minimum conditions to arbitrary leaking optimizers. The unrestricted global quarter optimum remains open.

## 追加锚（本行以下为增补区）

The full actual-quotient effective-rank extension, including its quantitative leakage bound, is proved in [RT V §120](ARITHMETIC_HOLOGRAPHIC_RT_V.md#120-effective-rank-bounds-for-full-actual-quotient-stresses).

## 追加锚（本行以下为增补区）

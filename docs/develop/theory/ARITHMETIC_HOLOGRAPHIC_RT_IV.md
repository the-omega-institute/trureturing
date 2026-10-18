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

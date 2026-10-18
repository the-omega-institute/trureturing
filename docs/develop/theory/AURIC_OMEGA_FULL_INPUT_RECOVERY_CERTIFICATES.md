# AURIC Ω full-input recovery certificates

## 1. The complete actual real-frame domain

**Definition 1.1 (objects and conventions).** Use the physical/passive correspondence (P.1)–(P.2), classes $\mathcal R_\beta\subseteq\mathcal C_\beta$, and full-input metrics of the [phase-gain volume](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md). Here $N:M_3\to M_5$ is the passive representation of an actual member of $\mathcal R_\beta$, $a=1-\beta$, $0\leq\beta\leq1/2$, and its Kraus matrices $K_\alpha$ are real in the fixed original bases. Put

$$
\sigma_\pm=N(\chi_\pm),\quad \sigma_2=N(|2\rangle\langle2|),\quad
V|i\rangle=\sum_\alpha K_\alpha|i\rangle\otimes|\alpha\rangle_E,
\quad \Gamma(X)=\operatorname{Tr}_B(VXV^\dagger).
\tag{R.1}
$$

The environment basis in (R.1) is real. Recoveries are always all complex CPTP maps on the entire five-dimensional output. Root fidelity is $f(A,B)=\|\sqrt A\sqrt B\|_1$, $F$ is its minimum over all input purifications, $g_N=\max_R F(RN,\mathrm{id}_3)$, and $\delta_N=\inf_R\|RN-\mathrm{id}_3\|_\diamond$ uses the unhalved norm and all finite references. The actual passive phase-difference spectrum is $(a,\beta,0,-\beta,-a)$; the physical native inputs are $\theta_\pm$, with swapped passive signs. Real-frame hypotheses in this volume are not asserted for every member of $\mathcal C_\beta$.

For $\Gamma:M_3\to M_r$ use the unnormalized input-first Choi matrix. If $J_0$ is its original-input-frame matrix and $J_p$ its phase-input-frame matrix, then

$$
H=(\chi_+,\chi_-,|2\rangle)
=\frac1{\sqrt2}\begin{pmatrix}1&1&0\\ i&-i&0\\0&0&\sqrt2\end{pmatrix},
\quad P=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},
$$

$$
J_p=(H^T\otimes I)J_0(\bar H\otimes I),\qquad
J_0=(\bar H\otimes I)J_p(H^T\otimes I).
\tag{R.2}
$$

Indeed the $(k,l)$ block of the first expression is $\sum_{ij}H_{ik}\bar H_{jl}\Gamma(|i\rangle\langle j|)=\Gamma(H|k\rangle\langle l|H^\dagger)$. A physical input density has phase coordinates $\rho_p=H^\dagger\rho_0H$. The reference transformation in (R.2) is thus not $H^\dagger$ on the left.

**Theorem 1.2 (support-aware complementary block domain and reverse realization).** The complete complementary domain, allowing any finite real environment, is

$$
J_p=\begin{pmatrix}
\tau&0&C\\0&\bar\tau&\bar C\\C^\dagger&C^T&\sigma
\end{pmatrix},\quad
\tau\succeq0,\quad\operatorname{Tr}\tau=1,\quad
\sigma=\bar\sigma=\sigma^T,\quad\operatorname{Tr}\sigma=1,\quad
\operatorname{Tr}C=0,
\tag{R.3}
$$

where $\tau=\Gamma(\chi_+)$ has nonzero spectrum $(a,\beta)$ for $\beta>0$, or $(1)$ at zero, and $C=\Gamma(|\chi_+\rangle\langle2|)$. With the Moore–Penrose inverse on the actual support, the remaining conditions are exactly

$$
\operatorname{ran}C\subseteq\operatorname{ran}\tau,\qquad
S:=\sigma-C^\dagger\tau^+C-\overline{C^\dagger\tau^+C}\succeq0,
\qquad
\begin{cases}\operatorname{rank}S\leq1,&\beta>0,\\
\operatorname{rank}S\leq3,&\beta=0.
\end{cases}
\tag{R.4}
$$

Every such block datum is the complement of an actual real-Kraus CPTP encoder into $\mathbb C^5$ with the stated actual phase-output spectrum. In particular this is not only a PSD relaxation.

**Proof.** The spectrum gives $\|\sigma_+-\sigma_-\|_1=2$. The positive spectral projection distinguishes these two density matrices perfectly; positivity then forces orthogonal supports, as in the proof of the phase-gain lower bound. Hence each is the corresponding positive or negative part of the difference. Reality gives $\sigma_-=\bar\sigma_+$. Their Schmidt environment states are $\tau$ and $\bar\tau$. Every output vector in $V\chi_+$ is orthogonal to every output vector in $V\chi_-$, so $\Gamma(|\chi_+\rangle\langle\chi_-|)=0$. The same real conjugation gives the barred $C$ block and real $\sigma$. Trace preservation gives precisely the three diagonal traces and $\operatorname{Tr}C=0$. Contracting $V$ with the five output basis vectors gives five real Kraus matrices for $\Gamma$, so $\operatorname{rank}J_p\leq5$.

For $A=\operatorname{diag}(\tau,\bar\tau)$ and $D_C=(C;\bar C)$, positivity of $\left(\begin{smallmatrix}A&D_C\\D_C^\dagger&\sigma\end{smallmatrix}\right)$ forces $\operatorname{ran}D_C\subseteq\operatorname{ran}A$. A vector in $\ker A$ cannot have a nonzero coupling to the lower block, as its two-dimensional quadratic-form compression would otherwise take a negative value. Under this range condition the invertible triangular congruence subtracting $A^+D_C$ from the upper variable gives $\operatorname{diag}(A,S)$. Thus, including singular $\tau$,

$$
J_p\succeq0\ \Longleftrightarrow\ (\text{range condition and }S\succeq0),
\qquad \operatorname{rank}J_p=2\operatorname{rank}\tau+\operatorname{rank}S.
\tag{R.5}
$$

Since $S$ is real, positive beta permits $S=vv^T$ with $v\in\mathbb R^r$, including $v=0$. At zero the phase rank is one, and the correct residual bound is three.

Conversely (R.3)–(R.4) give a PSD $J_p$ of rank at most five with $\operatorname{Tr}_EJ_p=I_3$. It obeys $J_p=(P\otimes I)\bar J_p(P\otimes I)$. Since $HP=\bar H$ and $PH^\dagger=H^T$, (R.2) makes $J_0$ real. Take a real spectral Gram decomposition of $J_0$, reshape its at most five vectors into real $r\times3$ Kraus matrices $L_n$ of $\Gamma$, and pad to five with zeros. Define

$$
(K_\alpha)_{n i}=(L_n)_{\alpha i}.
\tag{R.6}
$$

Then $\sum_\alpha K_\alpha^TK_\alpha=\sum_nL_n^TL_n=I_3$. Contracting indices shows that its actual complement on every matrix unit is the prescribed $\Gamma$. The zero $(+,-)$ block says $\langle K_\gamma\chi_-,K_\alpha\chi_+\rangle=0$ for every $\alpha,\gamma$, so the encoder's actual phase supports are orthogonal. Their Schmidt spectra are the spectra of $\tau$ and $\bar\tau$. Their actual difference has exactly $(a,\beta,0,-\beta,-a)$, including the rank-one zero-beta branch. Equation (P.1) therefore supplies an actual physical member of $\mathcal R_\beta$. $\square$

**Theorem 1.3 (all third columns and real Kraus compression).** For $\beta>0$ there is a real output orthonormal frame $(b_1,g_1,b_2,g_2,h)$ with

$$
\sigma_\pm=a|f_1^\pm\rangle\langle f_1^\pm|
+\beta|f_2^\pm\rangle\langle f_2^\pm|,
\quad f_j^\pm=(b_j\pm ig_j)/\sqrt2.
\tag{R.7}
$$

Let $Jb_j=g_j$, $Jg_j=-b_j$ on the real active space $U$. Every real Kraus list has exactly the form

$$
K_\alpha=(x_\alpha,Jx_\alpha,t_\alpha),\quad
x_\alpha=\sum_{j=1}^2(\operatorname{Re}z_{j\alpha}b_j-\operatorname{Im}z_{j\alpha}g_j),
\quad ZZ^\dagger=\operatorname{diag}(a,\beta),
\tag{R.8}
$$

$$
t_\alpha\in\mathbb R^5,\quad
\sum_\alpha\|t_\alpha\|^2=1,\quad
\sum_\alpha x_\alpha^Tt_\alpha=0,\quad
\sum_\alpha(Jx_\alpha)^Tt_\alpha=0.
\tag{R.9}
$$

These conditions are also sufficient. At zero complete the active plane by any three real orthonormal directions; (R.8)–(R.9) still hold with the second row of $Z$ zero. Every such actual channel admits a real Kraus list of length $r\leq9$.

**Proof.** Orthogonality and conjugation give $\sigma_\pm=(|\Delta|\pm\Delta)/2$ for $\Delta=\sigma_+-\sigma_-$; the common real part is $|\Delta|/2$. The real skew-normal form gives (R.7), correcting orientation by the unused axis if needed. Positivity of the sum $\sigma_+=\sum_\alpha|K_\alpha\chi_+\rangle\langle K_\alpha\chi_+|$ places every $K_\alpha\chi_+$ in its actual support. Equating real and imaginary parts of $K_\alpha|0\rangle+iK_\alpha|1\rangle=\sum_jz_{j\alpha}(b_j+ig_j)$ gives exactly the first two columns in (R.8), and their weighted output sum gives $ZZ^\dagger=\operatorname{diag}(a,\beta)$. This already supplies both column norms and their inner product: $x_\alpha^TJx_\alpha=0$ separately. The remaining TP equations are exactly (R.9); there is no condition deleting components of $t_\alpha$ along $U$.

The real space of matrices $(x,Jx,t)$ has dimension $4+5=9$. The real encoder Choi matrix is a sum of vectorized real Kraus outer products supported there, so its real spectral decomposition supplies at most nine real Kraus matrices for the same channel. At zero the active $x$ space has dimension two and the same upper bound remains valid. Compression changes the complementary environment representation; all block data must be transformed with it. This is not a two-Kraus assumption. $\square$

## 2. The residual is the actual outside-support weight

**Theorem 2.1 (same-dilation identity at all endpoints).** Let $\Pi$ be the sum of the two actual phase support projections. It is real, of rank four for $\beta>0$ and rank two for $\beta=0$. Then

$$
w:=\operatorname{Tr}[(I-\Pi)\sigma_2]=\operatorname{Tr}S\in[0,1].
\tag{R.10}
$$

For positive beta $S=vv^T$, where $v=(\langle h|\otimes I)V|2\rangle$ in a real unit direction $h\in\ker\Pi$. At zero $S=HH^T$ for the three outside-output columns $H$, so rank three is permitted.

**Proof.** Choose a real output basis adapted to the actual $\Pi$. If its rank is $d_\Pi=2\operatorname{rank}\tau$, the actual Gram factor of $J_p$ obtained by contracting $V$ with these output basis vectors has the form

$$
J_p=\begin{pmatrix}AA^\dagger&AB^\dagger\\BA^\dagger&BB^\dagger+HH^T\end{pmatrix},
\quad AA^\dagger=\operatorname{diag}(\tau,\bar\tau),\quad
AB^\dagger=(C;\bar C).
$$

The first $d_\Pi$ columns form $A$; the outside columns have zero upper blocks, and their bottom blocks form the real matrix $H$. Since $\operatorname{rank}AA^\dagger=d_\Pi$, $A$ has full column rank. Singular-value decomposition on its nonzero singular values gives $A^\dagger(AA^\dagger)^+A=I_{d_\Pi}$. Consequently the actual Schur residual is

$$
S=BB^\dagger+HH^T-BA^\dagger(AA^\dagger)^+AB^\dagger=HH^T.
$$

Its trace is the squared norm of $((I-\Pi)\otimes I)V|2\rangle$, exactly the Born probability in (R.10). There is one outside direction at positive beta and three at zero. All third-output coherences remain in $B$ and $V|2\rangle$; no arbitrary residual is assigned to an unrelated channel. Real output rotations here calculate the same object and supply no extra native control. $\square$

**Theorem 2.2 (actual rank-three zero-beta residual).** The endpoint branch of (R.4) is attained by

$$
K_0=e_0\langle0|+e_1\langle1|,\quad
K_1=\tfrac13e_2\langle2|,\quad
K_2=\tfrac23e_3\langle2|,\quad
K_3=\tfrac23e_4\langle2|.
$$

**Proof.** The TP sum is $I_3$. The phase support is $\operatorname{span}(e_0,e_1)$, $\tau$ has rank one, $C=0$, and $S=\operatorname{diag}(0,1/9,4/9,4/9)$ in the displayed environment. Thus $w=1$, $\operatorname{rank}S=3$ and $\operatorname{rank}J_p=5$. A rank-one restriction at zero would exclude an actual original-class channel. $\square$

## 3. Three inputs, one recovery POVM, and the exact threshold

**Theorem 3.1 (coherence-preserving residual bound).** For $0<\beta\leq1/2$ and every actual encoder in Definition 1.1, put

$$
e_\beta(w)=\frac{\beta(1-w)}{\beta+2+\sqrt{8\beta w}}.
$$

For every single complex CPTP recovery $R$,

$$
\|RN-\mathrm{id}_3\|_\diamond\geq2e_\beta(w),\qquad
F(RN,\mathrm{id}_3)^2\leq1-e_\beta(w).
\tag{R.11}
$$

Hence $\delta_N\geq2e_\beta(w)$ and $g_N^2\leq1-e_\beta(w)$ on the full input/reference domain.

**Proof.** For the orthonormal inputs $\eta_j=\chi_+,\chi_-,|2\rangle$, let $P_j=|\eta_j\rangle\langle\eta_j|$ and $E_j=R^\dagger(P_j)$. These are one POVM: $E_j\succeq0$, $\sum_jE_j=I_5$, even when $R$ is complex. Set $p_j=\operatorname{Tr}[E_jN(\eta_j)]$ and $\varepsilon=\max_j(1-p_j)$. Measuring the pure ideal target gives

$$
\|RN-\mathrm{id}\|_\diamond\geq2\varepsilon,
\qquad F(RN,\mathrm{id})^2\leq\min_jp_j=1-\varepsilon.
\tag{R.12}
$$

The actual $D_\sigma=\sigma_++\sigma_-$ obeys $D_\sigma\succeq\beta\Pi$. Since $E_2\preceq I-E_+$ and $E_2\preceq I-E_-$,

$$
\beta\operatorname{Tr}(\Pi E_2)\leq\operatorname{Tr}(D_\sigma E_2)
\leq(1-p_+)+(1-p_-)\leq2\varepsilon,
\quad \Pi E_2\Pi\preceq d\Pi,\quad d=2\varepsilon/\beta.
\tag{R.13}
$$

The last inequality uses that a PSD operator's largest eigenvalue is at most its trace. It does not diagonalize $E_2$ or the third output.

Set $E_0=\beta/(\beta+2)$. Since $0\leq e_\beta(w)\leq E_0$, the branch $\varepsilon\geq E_0$ is done. On the other branch $d<1-\varepsilon\leq p_2$ and $d<1$. If $w=1$ the bound is zero and needs no normalization. Otherwise take the normalized mathematical vectors

$$
\Psi=V|2\rangle,\qquad
\phi=((\Pi\otimes I)\Psi)/\sqrt{1-w},\qquad
|\langle\phi,\Psi\rangle|=\sqrt{1-w}.
$$

For $E=E_2\otimes I$, put $r=\langle\phi|E|\phi\rangle\leq d$ and $p=\langle\Psi|E|\Psi\rangle=p_2\geq1-\varepsilon$. Splitting the overlap into its $E$ and $I-E$ parts and using Cauchy–Schwarz gives

$$
\sqrt{1-w}\leq\sqrt{pr}+\sqrt{(1-p)(1-r)}.
\tag{R.14}
$$

Equivalently this is Watrous root-fidelity monotonicity under the binary CPTP measurement. The vector $\phi$ is an auxiliary proof vector, not an encoded input or a physical postselection instruction. Both terms in (R.14) retain the entire third-state coherence.

On the exact rectangle $0\leq r\leq d<1-\varepsilon\leq p\leq1$, the function $B(p,r)=\sqrt{pr}+\sqrt{(1-p)(1-r)}$ increases in $r$ and decreases in $p$. In the interior this follows from

$$
\partial_pB=\tfrac12(\sqrt{r/p}-\sqrt{(1-r)/(1-p)})<0,\quad
\partial_rB=\tfrac12(\sqrt{p/r}-\sqrt{(1-p)/(1-r)})>0;
$$

continuity includes the zero and unit endpoints. Thus its exact rectangle maximum is $B(1-\varepsilon,d)$, giving

$$
\sqrt{1-w}\leq H_\beta(\varepsilon)
:=\sqrt{2\varepsilon(1-\varepsilon)/\beta}
+\sqrt{\varepsilon(1-2\varepsilon/\beta)}.
\tag{R.15}
$$

This envelope bounds the two numbers from the same fixed recovery, not numbers attained at different recoveries.

For $0\leq x\leq E_0$, put $\alpha(x)=\arcsin\sqrt{1-x}$ and $\gamma(x)=\arcsin\sqrt{2x/\beta}$. Then $\alpha\geq\gamma$ and $H_\beta(x)=\cos(\alpha-\gamma)$ strictly increases from zero to one. Indeed $\alpha-\gamma$ strictly decreases from $\pi/2$ to zero. Let $M=\beta+2+\sqrt{8\beta w}$ and $e=\beta(1-w)/M$. The exact nonnegative-root identities

$$
1-e=\frac{(\sqrt2+\sqrt{\beta w})^2}{M},\qquad
1-2e/\beta=\frac{(\sqrt\beta+\sqrt{2w})^2}{M}
$$

give $H_\beta(e)=\sqrt{1-w}$. Hence (R.15) forces $\varepsilon\geq e$. At $w=0$ this says $e=E_0$ and the small-$\varepsilon$ branch would be impossible; at $w=1$ no $\phi$ was formed; at $\varepsilon=E_0$ the large branch applies. Combining with (R.12) proves (R.11), including every complex recovery before optimization. Product witnesses already belong to the larger full-reference test domain. $\square$

**Theorem 3.2 (exact exclusion threshold and endpoint boundary).** For positive beta define

$$
w_c(\beta)=\frac12\left[(1-\beta)^{1/4}-
\frac{\sqrt\beta}{1+\sqrt{1-\beta}}\right]^2.
\tag{R.16}
$$

Then $0<w_c<1/2$, and $w\leq w_c$ implies $\delta_N\geq1-\sqrt{1-\beta}$; $w<w_c$ gives the strict inequality. Equality at the threshold concerns the derived bounds, not necessarily the actual optimum.

**Proof.** $e_\beta$ is continuous and strictly decreasing in $w\in[0,1]$. Set $c=\sqrt{1-\beta}\in[1/\sqrt2,1)$. At zero $2e_\beta(0)=2\beta/(\beta+2)>1-c$, since after cancelling $1-c>0$ this is $c^2+2c-1>0$. At one the bound is zero. There is exactly one equality point. With $y=\sqrt w$ the equation $2e_\beta(w)=1-c$ becomes

$$
2(1+c)y^2+2\sqrt{2\beta}y-(c^2+2c-1)=0,
\qquad
\left(y+\frac{\sqrt\beta}{\sqrt2(1+c)}\right)^2=c/2.
$$

Its nonnegative root is $y_c=(\sqrt c-\sqrt\beta/(1+c))/\sqrt2$, which yields (R.16). Positivity of the bracket follows from $c(1+c)^2-\beta=(1+c)(c^2+2c-1)>0$, and $y_c^2<1/2$. Strict monotonicity proves both claims.

At $\beta=1/2$,

$$
\delta_N\geq\frac{2(1-w)}{5+4\sqrt w},\qquad
w_c=\tfrac12[2^{-1/4}-(\sqrt2-1)]^2,
$$

so $w=0$ gives $\delta_N\geq2/5$. As a scalar limit at fixed numerical $w$, $e_\beta(w)/\beta\to(1-w)/2$ and $w_c(\beta)\to1/2$ as $\beta\downarrow0$. This is not continuity of an actual support projection across a rank change. At zero $\Pi$ has rank two, (R.10) still holds with rank $S\leq3$, and the displayed algebraic $e_0(w)=0$ gives only $\delta_N\geq0$ and $g_N^2\leq1$. There is no division by beta or strict exclusion at that endpoint. $\square$

## 4. Nonempty complex sector and the remaining region

**Theorem 4.1 (actual family with nonreal environment state).** In a real output frame $(b_1,g_1,b_2,g_2,h)$ let $0<\beta\leq1/2$, $0<\vartheta<\pi/4$, $0\leq w\leq1$, and $t=\sqrt{1-w}\,b_2+\sqrt w\,h$. The three real Kraus matrices

$$
\begin{aligned}
K_0&=\sqrt a\cos\vartheta(b_1\langle0|+g_1\langle1|)+t\langle2|,\\
K_1&=\sqrt\beta(b_2\langle0|+g_2\langle1|),\\
K_2&=\sqrt a\sin\vartheta(-g_1\langle0|+b_1\langle1|)
\end{aligned}
\tag{R.17}
$$

define an actual member of the original real class with (R.7), actual outside weight $w$, nonreal $\tau$, and $C\ne0$ whenever $w<1$.

**Proof.** The three individual TP products are respectively $\operatorname{diag}(a\cos^2\vartheta,a\cos^2\vartheta,1)$, $\operatorname{diag}(\beta,\beta,0)$ and $\operatorname{diag}(a\sin^2\vartheta,a\sin^2\vartheta,0)$; they sum to $I_3$. The third column is orthogonal to the first plane, so no cross terms were discarded. Directly $K_0\chi_\pm=\sqrt a\cos\vartheta f_1^\pm$, $K_1\chi_\pm=\sqrt\beta f_2^\pm$, and $K_2\chi_\pm=\pm i\sqrt a\sin\vartheta f_1^\pm$. Thus (R.7) holds. The actual third output is $|t\rangle\langle t|$, including its $b_2$–$h$ coherences $\sqrt{w(1-w)}$.

In the unchanged real environment $(\epsilon_0,\epsilon_1,\epsilon_2)$ put $z_\vartheta=\cos\vartheta\epsilon_0+i\sin\vartheta\epsilon_2$. Then

$$
V\chi_+=\sqrt a f_1^+\otimes z_\vartheta+\sqrt\beta f_2^+\otimes\epsilon_1,
\quad V|2\rangle=t\otimes\epsilon_0,
$$

$$
\tau=a|z_\vartheta\rangle\langle z_\vartheta|+\beta|\epsilon_1\rangle\langle\epsilon_1|,
\quad \sigma=|\epsilon_0\rangle\langle\epsilon_0|,
\quad C=\sqrt{\beta(1-w)/2}|\epsilon_1\rangle\langle\epsilon_0|.
\tag{R.18}
$$

In particular $\tau_{02}=-ia\cos\vartheta\sin\vartheta\ne0$. The support inverse is $\tau^+=a^{-1}|z_\vartheta\rangle\langle z_\vartheta|+\beta^{-1}|\epsilon_1\rangle\langle\epsilon_1|$, so $C^\dagger\tau^+C=(1-w)|\epsilon_0\rangle\langle\epsilon_0|/2$ and $S=w|\epsilon_0\rangle\langle\epsilon_0|$. Fidelity adds over the orthogonal environment blocks, giving

$$
f(\tau,\bar\tau)=a|\langle z_\vartheta,\bar z_\vartheta\rangle|+\beta
=a\cos(2\vartheta)+\beta.
\tag{R.19}
$$

No complex environment gauge has been used to erase this imaginary part. $\square$

**Theorem 4.2 (nonempty strict exclusion beyond two simpler certificates).** The region in which $C\ne0$, $\tau$ is nonreal and $f(\tau,\bar\tau)>\sqrt a$ nevertheless contains actual encoders with $\delta_N>1-\sqrt a$ by Theorem 3.1.

**Proof.** At $\beta=1/2$, $\vartheta=\pi/8$, (R.19) is $(1+1/\sqrt2)/2>1/\sqrt2$. For every $0<w<w_c(1/2)$, (R.17) has $C\ne0$, rank $S=1$, rank $J_p=5$ and the asserted strict bound.

An exact witness independent of this radical endpoint takes

$$
\beta=9/25,\quad\sqrt a=4/5,\quad
\cos\vartheta=12/13,\quad\sin\vartheta=5/13,
\quad\sqrt{1-w}=12/13,\quad\sqrt w=5/13.
$$

Then $w=25/169$, $f(\tau,\bar\tau)=137/169>4/5$, $C\ne0$ and $\tau$ is nonreal, with ranks $\operatorname{rank}S=1$ and $\operatorname{rank}J_p=5$. Moreover

$$
2e_\beta(w)=\frac{2592}{9971+1950\sqrt2}>\frac15=1-\sqrt a,
$$

because $2989>1950\sqrt2$, as $2989^2-2\cdot1950^2=1329121>0$. These are actual channels and exact inequalities, not feasibility of an unrelated block relaxation. $\square$

**Theorem 4.3 (two complementary certificates and necessary improving region).** At positive beta either $C=0$ or $f(\tau,\bar\tau)\leq\sqrt a$ implies

$$
\delta_N\geq1-\sqrt a,\qquad g_N^2\leq(1+\sqrt a)/2.
\tag{R.20}
$$

Consequently any encoder actually improving the diamond benchmark must obey

$$
C\ne0,\quad f(\tau,\bar\tau)>\sqrt a,\quad
w_c(\beta)<\operatorname{Tr}S<1,\quad
0<2\operatorname{Tr}(C^\dagger\tau^+C)<1-w_c(\beta).
\tag{R.21}
$$

**Proof.** First if orthogonal pure inputs $\eta_\pm$ have output distance at most $2m$, contraction and the triangle inequality give $\|RN-\mathrm{id}\|_\diamond\geq1-m$ for every same recovery. Let $p_\pm$ be its respective pure-target probabilities. A binary target measurement with the unused logical direction assigned to one outcome has sum of correct probabilities at least $p_++p_-$. Its optimum binary sum is $1+\|RN(\eta_+)-RN(\eta_-)\|_1/2\leq1+m$. Thus $\min p_\pm\leq(1+m)/2$, which gives the worst-input fidelity assertion for every recovery as well.

If $C=0$, each Kraus third-output vector $t_\gamma$ is orthogonal to all $K_\alpha\chi_+$ and all $K_\alpha\chi_-$. Positive beta makes their span the entire active four-dimensional support, hence $V|2\rangle=h\otimes v$ with real unit $v$. For any complex unit $q$ in the original $0$–$1$ plane, $\Gamma(q)=|c_+|^2\tau+|c_-|^2\bar\tau$ on writing $q=c_+\chi_++c_-\chi_-$. Because $v$ is real, $v^T\tau v=v^T\bar\tau v\leq a$. Therefore

$$
N(|q\rangle\langle2|)=|z_q\rangle\langle h|,\quad z_q\perp h,
\quad\|z_q\|^2=v^T\tau v\leq a.
$$

The inputs $(q\pm|2\rangle)/\sqrt2$ have output distance $2\|z_q\|\leq2\sqrt a$, proving (R.20) in this branch. At zero the outside space is three-dimensional, so this factorization is not asserted.

For arbitrary $C$, put $X=N(|\chi_+\rangle\langle\chi_-|)$. Its left and right supports are orthogonal, so $\|X+X^\dagger\|_1=2\|X\|_1$. Trace-norm duality on the retained output, equivalently Uhlmann's purification formula, gives $\|X\|_1=f(\tau,\bar\tau)$. Since $|0\rangle\langle0|-|1\rangle\langle1|=|\chi_+\rangle\langle\chi_-|+|\chi_-\rangle\langle\chi_+|$, the actual $0,1$ output distance is exactly $2f(\tau,\bar\tau)$. Apply the preceding pair argument when this is at most $2\sqrt a$.

Finally trace (R.4): $2\operatorname{Tr}(C^\dagger\tau^+C)=1-w$. The range condition implies this trace vanishes exactly when $C=0$, so $C=0$ iff $w=1$. Combining (R.20) and Theorem 3.2 proves (R.21). The conditions are necessary only; their satisfaction supplies no improved recovery. Theorem 4.2 shows the new exclusion is not contained in the two simpler regions. $\square$

## 5. Complete half-weight coordinates, frame actions and kernel

**Theorem 5.1 (entire endpoint $W,T,v$ domain).** At $\beta=1/2$ every block datum in Theorem 1.2, and only such a datum, has the representation

$$
\begin{gathered}
W\in\mathbb C^{r\times2},\quad W^\dagger W=I_2,\quad
T\in\mathbb C^{2\times r},\quad v\in\mathbb R^r,\\
\operatorname{Tr}(WT)=0,\qquad 2\|T\|_F^2+\|v\|^2=1,\\
\tau=WW^\dagger/2,\qquad C=WT/\sqrt2,\qquad
\sigma=T^\dagger T+T^T\bar T+vv^T,\qquad S=vv^T.
\end{gathered}
\tag{R.22}
$$

There is no restriction on the direction of $T$ or deletion of third-input coherences. In an internal column basis one may impose $W^TW=\operatorname{diag}(c_1,c_2)$, $0\leq c_j\leq1$, and then

$$
W_j=\sqrt{(1+c_j)/2}\,u_j+i\sqrt{(1-c_j)/2}\,v_j,\qquad
f(\tau,\bar\tau)=(c_1+c_2)/2.
\tag{R.23}
$$

All real vectors actually used in (R.23) are mutually orthonormal. The $u_j$ always occur; $v_j$ is omitted when $c_j=1$. The real dimension condition is exactly $r\geq2+\#\{j:c_j<1\}$.

**Proof.** Since $\tau$ is half a rank-two projection, take any isometric frame $W$ for its range. The range condition gives $T=\sqrt2W^\dagger C$ and $C=WT/\sqrt2$. The support inverse is $\tau^+=2WW^\dagger$, hence $C^\dagger\tau^+C=T^\dagger T$. Its conjugate and the real rank-one residual supply $\sigma$ in (R.22). Trace and cross-trace conditions give exactly the remaining equations. Conversely these equations give (R.3)–(R.4); the full Gram factor below verifies PSD and rank, so Theorem 1.2 supplies an actual encoder.

For completeness, the required two-dimensional Takagi step follows without distinctness or nonzero singular values. For any symmetric complex $2\times2$ matrix $A$, maximize $\operatorname{Re}(z^TAz)$ over complex unit $z$. A phase makes the maximum nonnegative real. Choose a unit $w$ Hermitian-orthogonal to a maximizer. Variations $z\cos t+w\sin t$ and $z\cos t+iw\sin t$ force $z^TAw=0$. Choose the phase of $w$ to make $w^TAw$ nonnegative. Thus the unitary with columns $z,w$ gives $U^TAU=\operatorname{diag}(c_1,c_2)$, $c_j\geq0$. If the maximum is zero, phase variation and polarization force $A=0$. These $c_j$ are the singular values by unitary congruence, including zero and repeated values.

Apply this inside the proof to $A=W^TW$ and replace $W$ by $WU$ while cotransforming $T$ as below. Its norm is at most one, so $c_j\in[0,1]$. Write $W_j=x_j+iy_j$ with real vectors. The equations $W^\dagger W=I$ and $W^TW=\operatorname{diag}(c_j)$ give

$$
x_j\cdot x_k=(1+c_j)\delta_{jk}/2,\quad
y_j\cdot y_k=(1-c_j)\delta_{jk}/2,\quad
x_j\cdot y_k=0.
$$

For the last equation the sum and difference of the two imaginary-part identities vanish, including the off-diagonal cases. Normalization gives (R.23). The required number of real directions is exactly the stated dimension; conversely mutually orthonormal directions of that number construct $W$. In particular $r=2$ forces both $c_j=1$, while $r=3$ permits at most one $c_j<1$. Values $c_j=0$, $c_j=1$ and repeated values need no inverse. Equivalently $c_j=\cos(2\vartheta_j)$ with $\vartheta_j\in[0,\pi/4]$.

As $W$ and $\bar W$ are isometries, the nonzero singular values of $\sqrt\tau\sqrt{\bar\tau}$ are those of $W^\dagger\bar W/2$. The latter is conjugate to $W^TW/2$ in singular values. This proves the fidelity formula. It does not determine $T$ or the kernel Schmidt data from the $c_j$ alone. $\square$

**Theorem 5.2 (internal, real and transported frames).** The complete coordinate actions relevant to (R.22) are

$$
\begin{array}{ll}
W\mapsto WU,\quad T\mapsto U^\dagger T,\quad v\mapsto v,
& U\in U(2)\quad\text{(same blocks)},\\
W\mapsto OW,\quad T\mapsto TO^T,\quad v\mapsto Ov,
& O\in O(r,\mathbb R)\quad\text{(real environment coordinates)}.
\end{array}
\tag{R.24}
$$

The second transforms $J_p$ by $I_3\otimes O$. An arbitrary complex environment unitary requires transport of the real antiunitary as well.

**Proof.** In the first action $WW^\dagger$, $WT$, $T^\dagger T$ and $T^T\bar T$ are unchanged, so it is an internal representation freedom, not an actual environment operation. It includes the Takagi choice with its necessary $T$ cotransformation. After fixing a diagonal Takagi form the remaining freedoms are precisely those $U$ preserving that form under congruence, together with any relabeling of the $c_j$. On a repeated positive-$c$ subspace its stabilizer is real orthogonal; on a zero-$c$ subspace the whole corresponding unitary group remains. Thus zero and repeated values do not select unique vectors.

The real action gives $\tau\mapsto O\tau O^T$, $C\mapsto OCO^T$, $\sigma\mapsto O\sigma O^T$ and the same for $S$, by direct multiplication. If instead an arbitrary complex environment unitary $Q$ is used, the original real conjugation becomes $\mathfrak k'=Q\mathfrak kQ^\dagger$, where $\mathfrak kx=\bar x$. Both $\Gamma(\chi_+)$ and $\Gamma(\chi_-)$ transform by $Q$, but their new relation is conjugation by $\mathfrak k'$, not generally entrywise conjugation. In particular $Q\bar\tau Q^\dagger$ need not equal $\overline{Q\tau Q^\dagger}$. The simple barred-block form is justified only with its stated real structure. $\square$

**Theorem 5.3 (full Gram factor, full kernel and reverse actual channel).** For all feasible endpoint parameters, including $v=0$, all-zero or repeated $c_j$, the entire Choi matrix is $J_p=BB^\dagger$ with

$$
B=\begin{pmatrix}
W/\sqrt2&0&0\\
0&\bar W/\sqrt2&0\\
T^\dagger&T^T&v
\end{pmatrix}\in M_{3r\times5}(\mathbb C).
\tag{R.25}
$$

Its complete kernel consists of

$$
\xi=\bigl(-\sqrt2WTz+u_+,\ -\sqrt2\bar W\bar Tz+u_-,\ z\bigr),
\quad v^Tz=0,\quad W^\dagger u_+=0,\quad W^Tu_-=0,
\tag{R.26}
$$

where $z,u_+,u_-$ are complex. Its rank is four if $v=0$ and five otherwise; kernel dimension is respectively $3r-4$ or $3r-5$. Every parameter choice reconstructs an actual real-Kraus encoder as in (R.6).

**Proof.** Multiplication in (R.25) gives every one of the nine blocks (R.3). The first four columns are independent since the upper two logical sectors contain the rank-two frames $W$ and $\bar W$ separately. The fifth column is independent exactly when $v\ne0$. There is no dependence on whether a $c_j$ vanishes or is repeated.

For $\xi=(x_+,x_-,z)$, $B^\dagger\xi=0$ is exactly

$$
W^\dagger x_+/\sqrt2+Tz=0,\quad
W^Tx_-/\sqrt2+\bar Tz=0,\quad v^Tz=0.
$$

Subtracting the particular solutions in (R.26) leaves precisely $\ker W^\dagger$ and $\ker W^T$. This parametrization is both injective in $(u_+,u_-,z)$ and surjective onto the kernel. Their dimensions are $r-2,r-2$, and $r-1$ when $v\ne0$, or $r$ when $v=0$, proving the count. For $r=2$ both $u$ terms vanish; for larger $r$ their full spaces remain. No inverse of $T$ or $c_j$, and no product-kernel assumption, is used.

Finally (R.25), its traces and its conjugation symmetry satisfy the reverse construction in Theorem 1.2. The actual reconstructed channel has orthogonal phase-output supports with Schmidt weights $(1/2,1/2)$, not merely these weights in an unrelated compression. A real output skew-normal frame can be chosen by an orthogonal coordinate change and its unused direction can correct orientation. The construction asserts a channel, not native preparation or a physical decoder. $\square$

## 6. Full-input filtered Choi fidelity and weighted kernel certificates

**Theorem 6.1 (small-root formula with the actual input transpose).** In any displayed input coordinates let the actual complement have $J_\Gamma=BB^\dagger$, using at most five columns. For every reference density $q\succeq0$, $\operatorname{Tr}q=1$, and environment density $\omega$, including singular ones,

$$
\Phi(q,\omega):=\operatorname{Tr}\sqrt{B^\dagger(q^2\otimes\omega)B},
\qquad g_N=\max_\omega\min_q\Phi(q,\omega).
\tag{R.27}
$$

The actual input density represented by $q$ is $q^T$. At the half-weight endpoint (R.25) supplies an explicit order-five root, including its zero column when $v=0$.

**Proof.** The vector $|\psi_q\rangle=\sum_{ij}(\sqrt q)_{ij}|i\rangle_R|j\rangle_A$ has reference marginal $q$ and input marginal $q^T$. Applying $\Gamma$ or $\mathcal C_\omega$ gives the normalized states

$$
A_q=(\sqrt q\otimes I)BB^\dagger(\sqrt q\otimes I),\qquad Q_q=q\otimes\omega.
$$

The first normalization uses $\operatorname{Tr}_EJ_\Gamma=I_3$, not an invertible $q$. With $M=(\sqrt q\otimes I)B$, the nonzero eigenvalues of $Q_q^{1/2}MM^\dagger Q_q^{1/2}$ and $M^\dagger Q_qM$ agree, by the two Gram products of $Q_q^{1/2}M$. Therefore

$$
f(A_q,Q_q)=\operatorname{Tr}\sqrt{M^\dagger Q_qM}
=\operatorname{Tr}\sqrt{B^\dagger(q^2\otimes\omega)B}.
$$

This needs no inverse and covers all singular supports and complex $q,\omega$. The map $q\mapsto q^T$ is a bijection on input densities. Applying unrestricted Bény–Oreshkov duality to the same $N,\Gamma$ gives (R.27), with a single center fixed across every input in the inner minimum. No input-dependent center is admitted. $\square$

**Theorem 6.2 (support-aware weighted kernel witness).** For any unit $\xi\in\ker J_\Gamma$, put $D_\xi=\operatorname{Tr}_E|\xi\rangle\langle\xi|$ and $\ell=\operatorname{Tr}\sqrt{D_\xi}>0$. Then for every same environment center,

$$
F(\Gamma,\mathcal C_\omega)^2
\leq1-\frac{\langle\xi|I\otimes\omega|\xi\rangle}{\ell^2}.
\tag{R.28}
$$

For Schmidt rank $k$, $\ell^2\leq k$; it equals one for a product vector and two for a maximally entangled rank-two vector. In particular the complete kernel (R.26), including its $u$ terms, is available for certificates.

**Proof.** Set $q=\sqrt{D_\xi}/\ell$ on its actual support, and let $q^+$ denote its Moore–Penrose inverse. The vector $\zeta=(q^{-1/2}\otimes I)\xi/\ell$, using the inverse only on this support, has norm one because

$$
\|\zeta\|^2=\operatorname{Tr}(D_\xi q^+)/\ell^2
=\ell\operatorname{Tr}\sqrt{D_\xi}/\ell^2=1.
$$

For $A_q=(\sqrt q\otimes I)J_\Gamma(\sqrt q\otimes I)$, $(\sqrt q\otimes I)\zeta=\xi/\ell$ gives $A_q\zeta=0$. The binary measurement onto $\zeta$ charges the other state $q\otimes\omega$ by exactly $\langle\xi|I\otimes\omega|\xi\rangle/\ell^2$: the support projector fixes $\xi$ and commutes with $I\otimes\omega$. Root-fidelity monotonicity yields (R.28). The charge lies in $[0,1]$ since it is a probability. Cauchy–Schwarz on the $k$ Schmidt eigenvalues gives $\ell^2\leq k$. These are ordinary input purifications, not physical filtering or postselection. Combining several such bounds still requires one common $\omega$ before its maximization. $\square$

## 7. Exact recovery SDP on every input and every complex recovery

**Theorem 7.1 (fixed-input primal, full transpose and strong dual).** Fix the actual encoder Kraus list $K_\alpha:\mathbb C^3\to\mathbb C^5$ and an arbitrary complex input density $\rho$. With output-first vectorization put

$$
\operatorname{vec}(M)=\sum_{b,i}M_{bi}|b\rangle_5\otimes|i\rangle_3,
\quad d_\alpha=\operatorname{vec}(K_\alpha\rho),\quad
D_\rho=[d_1\ \cdots\ d_r],\quad M_\rho=D_\rho D_\rho^\dagger.
\tag{R.29}
$$

For a recovery with Kraus matrices $L_j:\mathbb C^5\to\mathbb C^3$, let $(\ell_j)_{bi}=(L_j)_{ib}$, let $J_R=\sum_j\ell_j\ell_j^\dagger$ be its input-first Choi matrix in $M_5\otimes M_3$, and put $X=J_R^T$, the full transpose. Then

$$
F_e(\rho,RN)=\sum_{\alpha,j}|\operatorname{Tr}(\rho L_jK_\alpha)|^2
=\operatorname{Tr}(XM_\rho),\quad
X\succeq0,\quad\operatorname{Tr}_{3}X=I_5.
\tag{R.30}
$$

Here $F_e$ is squared entanglement fidelity with the pure identity target. The exact fixed-input optimum is

$$
\begin{aligned}
p(\rho)&=\max_{X\succeq0,\ \operatorname{Tr}_3X=I_5}\operatorname{Tr}(XM_\rho)\\
&=\min_{Y=Y^\dagger,\ Y\otimes I_3\succeq D_\rho D_\rho^\dagger}\operatorname{Tr}Y.
\end{aligned}
\tag{R.31}
$$

Both optima are attained for every $\rho$, including singular inputs.

**Proof.** The recovery Choi PSD and marginal conditions are exactly the CPTP conditions: a Gram decomposition reshapes into all recovery Kraus lists, and partial tracing is their TP sum. Full transpose preserves PSD and takes the partial trace to its transpose, still $I_5$. Thus it is a bijection on the complete recovery feasible set. Partial transpose would not preserve positivity and is not used.

The index contraction is

$$
\ell_j^Td_\alpha=\sum_{b,i}(L_j)_{ib}(K_\alpha\rho)_{bi}
=\operatorname{Tr}(\rho L_jK_\alpha).
$$

For a purification of $\rho$, its overlap with $(L_jK_\alpha\otimes I)$ applied to itself is this trace. Summing the squared overlaps of all composite Kraus matrices gives the first equality in (R.30). Also $X=\sum_j\bar\ell_j\ell_j^T$, giving the second. There is no transpose missing from $K_\alpha\rho$. The different $q^T$ rule in (R.27) concerns a reference density, not this actual input variable.

For Hermitian $Y\in M_5$, the Lagrangian is $\operatorname{Tr}Y+\operatorname{Tr}[X(M_\rho-Y\otimes I_3)]$. Its supremum over $X\succeq0$ is finite exactly when $Y\otimes I_3\succeq M_\rho$, yielding the dual in (R.31). The primal set is nonempty and compact, with $\operatorname{Tr}X=5$, and $X_0=I_5\otimes I_3/3$ is strictly feasible. A dual point $Y=tI_5$ is strictly feasible for $t>\|M_\rho\|$. Slater strong duality therefore gives equality and attainment even for singular $\rho$. Alternatively dual feasible $Y$ is PSD, and a bounded-trace sublevel set is compact. This invokes the finite-dimensional Hermitian SDP theorem with both strict feasible points explicitly supplied. $\square$

**Theorem 7.2 (full-input minimax and order at most twenty-four).** For this same actual encoder,

$$
\begin{aligned}
g_N^2
&=\max_X\min_{\rho\in\mathsf D(\mathbb C^3)}F_e(\rho,X)
=\min_{\rho\in\mathsf D(\mathbb C^3)}p(\rho)\\
&=\min_{\rho,Y}\left\{\operatorname{Tr}Y:
\rho\succeq0,\ \operatorname{Tr}\rho=1,\ Y=Y^\dagger,\quad
\begin{pmatrix}Y\otimes I_3&D_\rho\\D_\rho^\dagger&I_r\end{pmatrix}\succeq0\right\}.
\end{aligned}
\tag{R.32}
$$

The top block has order fifteen and the bottom is the actual encoder Kraus-list identity $I_r$, not $I_5$. For a real compression from Theorem 1.3, $r\leq9$ and the whole matrix has order $15+r\leq24$.

**Proof.** For fixed $X$, choose any representing recovery Kraus list. Formula (R.30) is a sum of squared absolute values of real-linear functions of the Hermitian variable $\rho$, so it is continuous and convex in $\rho$. For fixed $\rho$ it is affine and continuous in $X$. Both input densities and recovery Choi variables form nonempty compact convex sets. The continuous convex-concave minimax theorem therefore applies with $\rho$ the minimizing variable and $X$ the maximizing variable. It proves the first exchange in (R.32); this is not an assumption that recovery may depend on the input. The left-hand optimization chooses one actual recovery before its worst input. Since square root is increasing, its value is exactly $g_N^2$.

Substitute the attained dual (R.31). The Schur complement with positive definite bottom $I_r$ is exactly $Y\otimes I_3\succeq D_\rho D_\rho^\dagger$. Since $D_\rho$ is linear in $\rho$, the displayed matrix inequality is affine and defines an SDP. Continuity of $p(\rho)$ on the compact input domain gives an optimal input; Theorem 7.1 supplies its attained dual. No diagonal-input, rank-one-input, two-Kraus or real-recovery restriction enters this equality. The same proof works for every beta in the real class, not only the half-weight coordinates. $\square$

**Theorem 7.3 (original-real reduction and its phase antiunitary).** In the stipulated original real Kraus frame an optimum in (R.32) may be chosen with $\rho,Y$ real symmetric. In the actual real environment frame an optimal center in (R.27) may likewise be real symmetric. This makes neither $\tau=\Gamma(\chi_+)$ nor the phase-coordinate input entrywise real.

**Proof.** Real $K_\alpha$ give $D_{\bar\rho}=\overline{D_\rho}$. Full conjugation takes a feasible pair $(\rho,Y)$ in (R.32) to $(\bar\rho,\bar Y)$ with the same real objective. Averaging the two preserves the affine matrix inequality and yields real symmetric variables. All complex recoveries were already optimized in the primal; no realness restriction on their Choi matrices is inserted.

For the complement, $\Gamma(\bar X)=\overline{\Gamma(X)}$. At each input, root fidelity against $\mathcal C_\omega$ is concave in $\omega$. Its infimum over inputs is also concave: at every fixed input the concavity lower bound is at least the corresponding combination of the two infima. Let this worst-input function be $h(\omega)$. Conjugation invariance of fidelity and the input domain gives $h(\bar\omega)=h(\omega)$, hence $h((\omega+\bar\omega)/2)\geq h(\omega)$. The average is a real symmetric density in that actual environment frame.

An original real density $\rho_0$ becomes $\rho_p=H^\dagger\rho_0H$, which satisfies

$$
\rho_p=P\bar\rho_pP,\qquad q_p=\rho_p^T=P\bar q_pP.
\tag{R.33}
$$

Thus the correct phase-coordinate averaging is $(\rho_p+P\bar\rho_pP)/2$, not entrywise real part. For example the original real ket $(|1\rangle+|2\rangle)/\sqrt2$ has phase ket $(-i/2,i/2,1/\sqrt2)$, whose projector has imaginary third-column entries.

Full SDP covariance also follows directly. Use $K_\alpha^p=K_\alpha H$, $L_j^p=H^\dagger L_j$ and $\rho_p=H^\dagger\rho_0H$. Then

$$
D^p=(I_5\otimes H^T)D^0,\qquad
X^p=(I_5\otimes H^T)X^0(I_5\otimes\bar H).
\tag{R.34}
$$

The top block transforms by this unitary, its $Y\otimes I_3$ part is unchanged, and the recovery marginal remains $I_5$. This proves covariance without replacing the phase antiunitary by naive conjugation. $\square$

**Theorem 7.4 (what a certificate proves).** Every feasible $(\rho,Y)$ in (R.32) bounds every originally allowed recovery at that one witness input:

$$
F_e(\rho,RN)\leq\operatorname{Tr}Y,\qquad
\delta_N\geq2(1-g_N^2)\geq2(1-\operatorname{Tr}Y).
\tag{R.35}
$$

In particular $\operatorname{Tr}Y\leq(1+\sqrt a)/2$ certifies $\delta_N\geq1-\sqrt a$ for that actual encoder.

**Proof.** Positivity gives $\operatorname{Tr}(XM_\rho)\leq\operatorname{Tr}[X(Y\otimes I_3)]=\operatorname{Tr}Y$ for every recovery-feasible $X$. Thus each recovery's worst-input fidelity is at most this witness value, even without minimax. Measuring a pure identity target on any purification gives unhalved trace-norm error at least $2(1-F_e)$. Maximizing over inputs and then minimizing over recoveries yields (R.35).

The first inequality is a statement about one witness input, not an upper bound on every input's fidelity. No uniform existence of a threshold certificate is asserted. Conversely $g_N^2>(1+\sqrt a)/2$ does not refute the diamond benchmark: the fidelity-to-diamond lower bound then fails to certify that benchmark. An actual improved recovery with a full-reference diamond upper bound would still be required. $\square$

## 8. Matched full-input certificates for specified actual channels

**Theorem 8.1 (the phase-gain upper family has a matched certificate).** For the actual family (P.11) in the [phase-gain volume](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#4-an-actual-upper-family-and-its-individual-optimum), put $u=\sqrt a$, $p=(1+u)/2$. Then

$$
g_{N_\beta}^2=p.
\tag{R.36}
$$

A matched dual witness in the same fixed output ordering is

$$
\rho=\operatorname{diag}(1/2,0,1/2),\qquad
Y=\operatorname{diag}((a+u)/4,\ 0,\ \beta/4,\ 0,\ (1+u)/4).
\tag{R.37}
$$

**Proof.** Decoder (P.14) gives $RN=p\,\mathrm{id}+(1-p)\operatorname{Ad}_Z$, $Z=\operatorname{diag}(1,1,-1)$, on every complex matrix. Therefore its squared entanglement fidelity at every input is $p+(1-p)(\operatorname{Tr}\rho Z)^2\geq p$. This lower bound covers all inputs and purifications, with equality at the displayed $\rho$.

For that $\rho$, the columns of $D_\rho$ are $s_0|e_0,0\rangle+s_2|e_4,2\rangle$ and $(\sqrt\beta/2)|e_2,0\rangle$, with $s_0=u/2$, $s_2=1/2$. In $Y\otimes I_3-M_\rho$ the only nontrivial coupled block is

$$
\operatorname{diag}(s_0(s_0+s_2),s_2(s_0+s_2))
-(s_0,s_2)(s_0,s_2)^T
=s_0s_2\begin{pmatrix}1&-1\\-1&1\end{pmatrix}\succeq0.
$$

The other active scalar is $\beta/4-\beta/4=0$, and all remaining entries are nonnegative diagonal. Thus (R.37) is feasible with trace $p$, matching the recovery lower bound. Both zero and half-weight endpoints remain in the proof. This is the optimum for this specified encoder family, not a class-optimality theorem. $\square$

**Theorem 8.2 (complex certificates at the isometric endpoint).** Let $E:\mathbb C^3\to\mathbb C^5$ be the real coordinate isometry onto the first three output coordinates and $N(X)=EXE^\dagger$. For every complex density $\rho$, including singular and nonreal ones, $Y=E\rho E^\dagger$ gives a matched trace-one certificate in (R.32).

**Proof.** Here $D_\rho=d=\operatorname{vec}(E\rho)$. It is supported in the range of $Y\otimes I_3$, and

$$
d^\dagger(Y^+\otimes I_3)d
=\operatorname{Tr}(\rho\rho^+\rho)=\operatorname{Tr}\rho=1.
$$

Cauchy–Schwarz on that support implies $Y\otimes I_3-dd^\dagger\succeq0$, also when $\rho$ has zero eigenvalues. The full recovery with Kraus matrices $E^\dagger$, $|0\rangle\langle e_3|$, $|0\rangle\langle e_4|$ is TP and exactly inverts $N$, so the primal value is one and matches $\operatorname{Tr}Y=1$. Nonreal $\rho$ gives genuinely complex certificates; their validity does not justify an entrywise-real phase-input restriction. Under (P.1) this is an actual member of $\mathcal R_0$. $\square$

## 9. An actual entangled kernel and an exact all-input endpoint value

**Theorem 9.1 (crossblock channel and failure of a fixed-pair shortcut).** For $a=1-\beta$ consider

$$
K_0=\sqrt a(e_0\langle0|+e_1\langle1|+e_2\langle2|),\qquad
K_1=\sqrt\beta(e_3\langle0|+e_4\langle1|+e_1\langle2|).
\tag{R.38}
$$

This is an actual original-class encoder. At positive beta its complement has Choi eigenvalues $1,a,a,\beta,\beta,0$ and unique normalized kernel vector

$$
\xi=\sqrt\beta\,|1\rangle|0_E\rangle-\sqrt a\,|2\rangle|1_E\rangle.
\tag{R.39}
$$

Thus its only missing Choi direction is entangled. Every recovery has error at least $\beta>1-\sqrt a$, although the fixed pair $(|0\rangle\pm|2\rangle)/\sqrt2$ has output distance two.

**Proof.** The TP products are $aI_3$ and $\beta I_3$. The phase outputs are the orthogonal mixtures in planes $(e_0,e_1)$ and $(e_3,e_4)$, with weights $a,\beta$. In the original real environment,

$$
\tau=\sigma=\operatorname{diag}(a,\beta),\qquad
C=i\sqrt{a\beta/2}|0_E\rangle\langle1_E|,\qquad
S=a|0_E\rangle\langle0_E|.
$$

For beta zero the same residual is obtained directly with the support inverse. In original input coordinates the only off-diagonal complementary block is $\Gamma(|1\rangle\langle2|)=\sqrt{a\beta}|0_E\rangle\langle1_E|$ and its adjoint. The Choi diagonal is $(a,\beta,a,\beta,a,\beta)$, with a coupled block on $(1,0_E),(2,1_E)$ equal to $(\sqrt a,\sqrt\beta)(\sqrt a,\sqrt\beta)^T$. The other four scalar entries are $a,\beta,\beta,a$. This proves the spectrum and (R.39), with Schmidt rank two for all positive beta, maximally entangled at half weight. At zero the Choi rank is three and the unique-kernel assertion is not made.

For the fixed superposition pair the output difference has disjoint off-diagonal blocks of weights $a,\beta$, so its trace norm is $2a+2\beta=2$. In contrast the outputs on $|1\rangle,|2\rangle$ have diagonal difference with nonzero entries $a-\beta,\beta,-a$, of norm $2a$. The same-recovery contraction argument gives $\delta_N\geq1-a=\beta$. Since $\sqrt a>a$ for positive beta, this strictly exceeds $1-\sqrt a$. The fixed superposition pair's lack of contraction is not a counterexample to existence of some useful input pair or to the sharp class curve.

A full recovery with Kraus matrices $L_0=|0\rangle\langle e_0|+|1\rangle\langle e_1|+|2\rangle\langle e_2|$ and $L_1=|0\rangle\langle e_3|+|1\rangle\langle e_4|$ is TP. On all matrices its composite is $a\,\mathrm{id}+\beta\mathcal D$, where $\mathcal D(X)=P_0XP_0+X_{22}|1\rangle\langle1|$, $P_0=|0\rangle\langle0|+|1\rangle\langle1|$. The Kraus matrices $P_0,|1\rangle\langle2|$ make $\mathcal D$ CPTP. Its diamond distance from identity is two, bounded above as a difference of channels and attained on $|2\rangle$. This recovery's exact error is therefore $2\beta$, with all references included. This last value is not asserted to be the encoder's optimum. $\square$

**Theorem 9.2 (exact endpoint fidelity on the whole qutrit).** For (R.38) at $\beta=1/2$,

$$
g_N^2=\frac{3+2\sqrt2}{8},\qquad
\delta_N\geq\frac{5-2\sqrt2}{4}.
\tag{R.40}
$$

In particular a universal replacement of the kernel loss $\lambda_2/2$ in the phase-gain lower-bound proof by $\lambda_2$ is false on an actual admissible channel.

**Proof.** Put $Q=\operatorname{span}(|1\rangle,|2\rangle)$. On $Q$ the complement is

$$
\Lambda\begin{pmatrix}x&z\\\bar z&y\end{pmatrix}
=\tfrac12\begin{pmatrix}x+y&z\\\bar z&x+y\end{pmatrix},
$$

with Bloch coefficients $(1/2,1/2,0)$ and Pauli probabilities $(1/2,1/4,1/4,0)$. On the rest of the full input space, $\Gamma(|0\rangle\langle0|)=I_2/2$ and all $0$–$Q$ cross terms vanish, by the full matrix-unit identities in Theorem 9.1.

Take the full sixteen-element Pauli group on $Q$, including phases $\pm1,\pm i$, and extend each element $A$ to $U_A=1\oplus A$ on the qutrit. With the matching environment Pauli $W_A$, $\Gamma(U_A XU_A^\dagger)=W_A\Gamma(X)W_A^\dagger$ on the full matrix algebra. On $Q$ this is the covariance of the diagonal Bloch action; on $|0\rangle$ and the cross terms it follows from the preceding identities. These are mathematical symmetries, not additional native controls.

The worst-input root-fidelity function $h(\omega)$ is concave in $\omega$, as proved in Theorem 7.3, and covariance makes it invariant under these environment conjugations. Averaging sends every $\omega$ to $I_2/2$ and cannot lower $h$. Thus that single center is optimal across all inputs.

For fixed channels and input $\rho$, Uhlmann's contraction formula gives

$$
F_\rho(\mathcal A,\mathcal B)=
\max_{\|T\|\leq1}\operatorname{Re}\operatorname{Tr}
[\rho V_{\mathcal A}^\dagger(I\otimes T)V_{\mathcal B}],
$$

padding environment spaces if necessary. It is a maximum of real affine functions of $\rho$, hence convex. At center $I_2/2$, covariance makes it invariant under the full input group. Averaging can therefore only decrease it. The full group average of any input is

$$
\rho_p=p|0\rangle\langle0|+(1-p)I_Q/2.
$$

The scalar phases in the sixteen-element group remove all $0$–$Q$ coherences; averaging only the four representatives $I,X,Y,Z$ would not justify that removal.

For a purification of $\rho_p$, both compared states are block diagonal in the corresponding reference split. Root fidelity adds across these blocks. The $|0\rangle$ block contributes $p$. In the $Q$ block the normalized Choi state $J_\Lambda/2$ has eigenvalues $1/2,1/4,1/4,0$ while the constant comparison state is $I_4/4$, so its root fidelity is

$$
c=\tfrac12(\sqrt{1/2}+\sqrt{1/4}+\sqrt{1/4})
=\frac{2+\sqrt2}{4}.
$$

Thus $F_{\rho_p}=p+(1-p)c$, whose minimum is $c$ at $p=0$. Input convexity proves no untwirled input has a lower value, and center concavity proves no other center has a higher worst-input value. Duality yields $g_N^2=c^2$ and the pure-target norm conversion gives (R.40). At this optimal center $\lambda_2=1/2$, while $c^2>1-\lambda_2=1/2$, refuting the stronger proposed kernel bound. This does not determine the exact diamond optimum or refute the class benchmark; indeed $c^2<(1+1/\sqrt2)/2$. $\square$

## 10. Standard sources and unresolved uniform certificate problem

**Definition 10.1 (attribution and domains of the standard inputs).** The conventional complex-linear CPTP, Kraus, Stinespring and full-Choi interfaces are the finite-dimensional ones already used in [FiniteKrausReversibility](../../../Blueprint/D5/S3/Quantum/Recovery/FiniteKrausReversibility.md), [OrthogonalSyndromeChannel](../../../Blueprint/D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel.md) and the [Bény–Oreshkov library note](../../../Library/QuantumChannels/beny2010approximate.md). Their exact-recovery constructions are not duplicated as new general theorems. Gram reshaping in (R.6) and (R.30) supplies the actual all-matrix channels needed here; no compiled statement in those sources is claimed to check these new applications.

Watrous, [*The Theory of Quantum Information*, Chapter 3](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf), Definition 3.11, (3.64), supplies the root convention, and Theorem 3.27, (3.173), supplies fidelity monotonicity for a CPTP map between finite complex Euclidean spaces and arbitrary PSD operands. The binary maps in Theorems 3.1 and 6.2 have PSD effects summing to identity, so singular states and unequal input/output dimensions cause no missing hypothesis. The direct Cauchy–Schwarz argument in (R.14) also proves the particular inequality needed there. Uhlmann's purification/contraction formula, including singular density operators, is used for the complementary trace norm and the input convexity in Theorems 4.3 and 9.2.

[Bény–Oreshkov, *General conditions for approximate quantum error correction and near-optimal recovery channels*, arXiv:0907.5391v4, Theorem 1, (3)](https://arxiv.org/pdf/0907.5391v4), and [*Approximate simulation of quantum channels*, arXiv:1103.0649v3, (54)–(56), Corollary 5, (64)](https://arxiv.org/pdf/1103.0649v3), are the literature-attested unrestricted recovery/complement result. The latter identifies $F_\rho$ as the square root of Schumacher fidelity. The target here is always $\mathrm{id}_3$, whose complement is the scalar trace, giving constant-density channels. No Kraus-restricted or trace-decreasing optimization replaces its all-quantum-channel maxima.

The continuous finite-dimensional convex-concave minimax theorem is used exactly as [Watrous, Chapter 1, Theorem 1.12](https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf): convex domains, compact maximizing domain, continuity, convexity in the minimizing variable and concavity in the maximizing variable. Slater duality is Theorem 1.18 there, with strictly feasible primal and dual points explicitly exhibited in Theorem 7.1. These are literature-attested tools, not claims of new minimax or SDP theory. The $2\times2$ Takagi step is a standard symmetric-matrix congruence proved inside Theorem 5.1 for this composition; it is not a new factorization theorem.

The support-aware actual-channel assembly, outside-weight bound and exact exclusion threshold, actual complex-sector witnesses, full endpoint kernel and convention-complete recovery certificates are repo-derived ordinary applications and compositions of these tools. No global originality, priority or kernel-verification claim is attached. Finite controls may support individual matrix identities or detect convention errors; no finite sample, numerical tolerance or optimized finite test replaces the continuous-domain proofs. There is no experimental program or data prerequisite in these statements.

**Definition 10.2 (remaining mathematical and realization obligations).** For positive beta the sharp whole-class problem remains to prove $\delta^*_{\mathcal R}(\beta)=1-\sqrt{1-\beta}$, or to construct an actual original-class encoder and one recovery with a smaller full-reference unhalved diamond error. The larger complex-class optimum in (P.20) is separate and also unresolved. Neither the necessary region (R.21), endpoint parameters nor the exact SDP supplies a threshold certificate uniformly over all remaining encoders. Angles alone do not determine $T$, a kernel vector's Schmidt geometry or a common environment center. A higher optimized fidelity alone does not settle a diamond counterexample.

The residual probability is exactly the Born probability of $I-\Pi$ on the actual mathematical $N(|2\rangle\langle2|)$; it is not identified with the physical joint occupation $\kappa$, a native readable event or a sensor calibration. Original-real reductions are confined to their stated frames, and the real-class certificates are not extended to arbitrary complex encoders. Every physical application retains (P.1)–(P.2), the original native menu, source-fiber membership and shared-word legality obligations of the [phase-gain volume](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#6-class-optimization-and-remaining-mathematical-obligations). These mathematical constructions do not supply source preparation, finite-history transport, native apparatus, empirical physics or completion of the wider programme.

## 追加锚（本行以下为增补区）
## 11. Joint filtered-kernel certificates from one actual complement

**Definition 11.1 (joint certificate data).** Retain the actual original-real class, coordinates, metrics and complementary blocks of Definition 1.1 and (R.2)–(R.4). Write

$$
s=\sqrt a,\qquad t_\beta=(1+s)/2,\qquad U(\beta)=1-s,
\qquad J=J_\Gamma=BB^\dagger.
$$

Here $J$ is the input-first Choi matrix of one actual complement in the displayed input frame. For every complex reference density $q\in\mathsf D(\mathbb C^3)$, including singular $q$, set

$$
A_q=(\sqrt q\otimes I_r)J(\sqrt q\otimes I_r),\qquad
P_q=\operatorname{supp}A_q,
$$

$$
0\preceq Z_q\preceq I-P_q,\qquad
H_{q,Z_q}=\operatorname{Tr}_{\mathbb C^3}
\bigl[(\sqrt q\otimes I_r)Z_q(\sqrt q\otimes I_r)\bigr].
\tag{R.41}
$$

The letter $Z_q$ denotes a kernel effect, distinct from the comparison state $Q_q$ in Theorem 6.1. It may be the full kernel projection or the projection onto any specified orthonormal subset of the kernel. Let $\mathscr H(J)$ consist of all finite convex aggregates

$$
H=\sum_{\ell=1}^m p_\ell H_{q_\ell,Z_{q_\ell}},
\qquad p_\ell\geq0,\qquad \sum_{\ell=1}^m p_\ell=1.
\tag{R.42}
$$

Every summand is constructed from this same $J$. Such aggregation varies witness inputs, not the encoder, dilation or environment center. By (R.27), the corresponding physical input in these coordinates is $q^T$, rather than $q$. In particular

$$
|\psi_q\rangle=\sum_{ij}(\sqrt q)_{ij}|i\rangle_R|j\rangle_A,
\quad \operatorname{Tr}_A P_{\psi_q}=q,
\quad \operatorname{Tr}_R P_{\psi_q}=q^T,
\quad \operatorname{Tr}A_q=1.
$$

These identities impose no reality or invertibility assumption on $q$. Under the original-to-phase change (R.2), the reference density transforms as $q_p=H^Tq_0\bar H$; the actual density transforms as $\rho_p=H^\dagger\rho_0H$, with $\rho_0=q_0^T$ and $\rho_p=q_p^T$. The $H$ in this coordinate formula is the fixed basis matrix of (R.2), not the certificate in (R.42).

**Theorem 11.2 (finite joint-kernel loss).** For every actual encoder in Definition 1.1 and every $H\in\mathscr H(J)$,

$$
0\preceq H\preceq I_r,\qquad
g_N^2\leq1-\lambda_{\min}(H),\qquad
\delta_N\geq2\lambda_{\min}(H).
\tag{R.43}
$$

More precisely, at each single environment density $\omega$, define

$$
m(\omega)=\min_{q\in\mathsf D(\mathbb C^3)}\Phi(q,\omega)^2.
$$

Then all the inequalities

$$
m(\omega)\leq1-\operatorname{Tr}(\omega H),\qquad
m(\omega)\leq f(\tau,\omega)^2,\quad
m(\omega)\leq f(\bar\tau,\omega)^2,\quad
m(\omega)\leq f(\sigma,\omega)^2
\tag{R.44}
$$

hold at that same $\omega$, and $g_N^2=\max_\omega m(\omega)$.

**Proof.** The small-root identity of Theorem 6.1 gives $\Phi(q,\omega)=f(A_q,q\otimes\omega)$, without an inverse of $q$. Apply root-fidelity monotonicity under the binary CPTP measurement with effects $P_q,I-P_q$. Its first distribution is $(1,0)$, whence

$$
\Phi(q,\omega)^2
\leq\operatorname{Tr}[P_q(q\otimes\omega)]
\leq1-\operatorname{Tr}[Z_q(q\otimes\omega)]
=1-\operatorname{Tr}(\omega H_{q,Z_q}).
\tag{R.45}
$$

This is the finite-complex, arbitrary-PSD data-processing statement of Watrous, Theorem 3.27, (3.173), cited in Definition 10.1. Positive congruence and partial trace give $0\preceq H_{q,Z_q}\preceq\operatorname{Tr}_{\mathbb C^3}(q\otimes I_r)=I_r$. Since $m(\omega)$ is at most every selected input value, averaging (R.45) gives the first inequality in (R.44). The other three use the actual pure inputs $\chi_+,\chi_-,|2\rangle$. In the original input frame their reference vectors are the conjugate kets; their actual environment states remain $\tau,\bar\tau,\sigma$.

Unrestricted Bény–Oreshkov duality in (R.27) fixes the order $\max_\omega\min_q$. Maximizing the first inequality of (R.44) only after aggregation gives $g_N^2\leq1-\min_\omega\operatorname{Tr}(\omega H)=1-\lambda_{\min}(H)$. For every complex CPTP recovery and every purification, measuring the pure identity target gives error at least $2(1-F_e)$. Taking the worst input and then the best recovery yields $\delta_N\geq2(1-g_N^2)$, as in (R.35), and proves (R.43).

No interchange with $\min_q\max_\omega$ occurs here. For example, two orthogonal pure environment states separately have optimized squared fidelity one, whereas the maximum over one common $\omega$ of the minimum of their squared fidelities is $1/2$: the latter two values are $\omega_{00}$ and $\omega_{11}$, whose sum is at most one. Thus separate optimized centers cannot supply (R.44). $\square$

## 12. Joint inverse and simultaneous three-state bounds

**Theorem 12.1 (inverse certificate retaining the kernel direction).** For $H\in\mathscr H(J)$ and $z>0$, put

$$
\eta_z(H;D)=\operatorname{Tr}[D(zI_r+H)^{-1}],
\qquad D\in\{\tau,\bar\tau,\sigma\}.
$$

Then

$$
g_N^2\leq\frac{(1+z)\eta_z(H;D)}{1+\eta_z(H;D)}.
\tag{R.46}
$$

In particular, for any of these actual environment states,

$$
\operatorname{Tr}[D(sI_r+H)^{-1}]\leq1
\ \Longrightarrow\ g_N^2\leq t_\beta
\ \Longrightarrow\ \delta_N\geq U(\beta).
\tag{R.47}
$$

A strict inverse inequality gives a strict diamond lower bound above $U(\beta)$.

**Proof.** Schatten Hölder, in its $2$-by-$2$ product form, gives for every positive definite $A$

$$
\begin{aligned}
f(D,\omega)
&=\|\sqrt D A^{-1/2}A^{1/2}\sqrt\omega\|_1\\
&\leq\|\sqrt D A^{-1/2}\|_2\|A^{1/2}\sqrt\omega\|_2
=\sqrt{\operatorname{Tr}(DA^{-1})\operatorname{Tr}(\omega A)}.
\end{aligned}
$$

This is the standard Schatten duality/Hölder inequality of Watrous, [*The Theory of Quantum Information*, (1.173)–(1.174), printed p.33](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf); it requires neither commuting nor real operands. With $A=zI_r+H$ and $h=\operatorname{Tr}(\omega H)$, (R.44) therefore gives simultaneously

$$
m(\omega)\leq\eta_z(z+h),\qquad m(\omega)\leq1-h.
$$

Weight these two bounds by $1/(1+\eta_z)$ and $\eta_z/(1+\eta_z)$ respectively. The $h$ terms cancel and yield (R.46) before maximizing $\omega$. Setting $z=s>0$ gives (R.47), since $x\mapsto x/(1+x)$ is strictly increasing. This combines the pure-state restriction and actual kernel charge at one center, rather than comparing their separate optima.

As a calibration of the existing $C=0$ branch of Theorem 4.3, at positive beta it has $\sigma=|v\rangle\langle v|$ with real unit $v$. The third pure input gives $H=I_r-|v\rangle\langle v|$. With $d=\langle v|\tau|v\rangle\leq a=s^2$,

$$
\eta_s(H;\tau)=\frac d s+\frac{1-d}{s+1}
=\frac{s+d}{s(s+1)}\leq1.
$$

Thus the inverse certificate recovers that prior exclusion even though $\lambda_{\min}(H)=0$. This is a calibration, not an additional exclusion or a new general Hölder theorem. The rank-one factorization is not imposed at beta zero. $\square$

**Theorem 12.2 (support-aware simultaneous certificate).** Set $D_+=\tau$, $D_-=\bar\tau$, $D_2=\sigma$. Choose three PSD matrices $A_j$ satisfying

$$
\operatorname{ran}D_j\subseteq\operatorname{ran}A_j,\qquad
\operatorname{Tr}(D_jA_j^+)\leq1,\qquad j\in\{+,-,2\}.
\tag{R.48}
$$

For nonnegative weights $\lambda_0+\lambda_++\lambda_-+\lambda_2=1$ and $H\in\mathscr H(J)$, define

$$
M=\lambda_0(I_r-H)+\lambda_+A_++\lambda_-A_-+\lambda_2A_2.
$$

Then $g_N^2\leq\lambda_{\max}(M)$. In particular,

$$
M\preceq t_\beta I_r\quad\Longrightarrow\quad\delta_N\geq U(\beta).
\tag{R.49}
$$

All kernels, states and matrices in this test belong to the same actual complementary representation.

**Proof.** The range condition implies $\sqrt{D_j}P_{A_j}=\sqrt{D_j}$. Inserting $(A_j^+)^{1/2}A_j^{1/2}=P_{A_j}$ into the fidelity product and using the same Schatten inequality gives

$$
f(D_j,\omega)^2
\leq\operatorname{Tr}(D_jA_j^+)\operatorname{Tr}(\omega A_j)
\leq\operatorname{Tr}(\omega A_j).
$$

This remains valid for singular $A_j,D_j,\omega$. A pseudoinverse trace condition alone is insufficient: $A_j=0$ would have zero such trace without bounding fidelity to a nonzero $D_j$. Weighting these three bounds and the kernel bound in (R.44) gives $m(\omega)\leq\operatorname{Tr}(\omega M)$ for every same $\omega$. Maximization gives the claim. The complete $J$, and hence its actual $C$ and $S$, enters through $H$; none of the three pure-state tests is detached from that $J$. $\square$

## 13. Complete joint geometry for filtered certificates

**Theorem 13.1 (positive-spectrum Gram and full kernel at every beta).** Let the actual blocks satisfy Theorem 1.2. Write

$$
\tau=W\Lambda W^\dagger,\quad W^\dagger W=I_k,\quad
\Lambda\succ0,\quad
T=\Lambda^{-1/2}W^\dagger C,\quad S=V_SV_S^T,
\tag{R.50}
$$

where $V_S$ is real with $d=\operatorname{rank}S$ independent columns, with no columns when $S=0$. The eigenvalue and residual branches are

$$
\begin{cases}
k=2,\quad\Lambda=\operatorname{diag}(a,\beta),\quad d\leq1,&\beta>0,\\
k=1,\quad\Lambda=(1),\quad d\leq3,&\beta=0.
\end{cases}
$$

In phase-input coordinates the same actual $J_p$ has the Gram factor

$$
B=\begin{pmatrix}
W\Lambda^{1/2}&0&0\\
0&\bar W\Lambda^{1/2}&0\\
T^\dagger&T^T&V_S
\end{pmatrix},\quad
C=W\Lambda^{1/2}T,\quad
\sigma=T^\dagger T+T^T\bar T+V_SV_S^T.
\tag{R.51}
$$

The remaining scalar constraints are

$$
\operatorname{Tr}(W\Lambda^{1/2}T)=0,\qquad
2\|T\|_F^2+\|V_S\|_F^2=1.
$$

Together with the displayed isometry, positive spectrum and real residual branches, these constraints also suffice for actual-channel realization by Theorem 1.2. Its complete kernel is

$$
\begin{pmatrix}
-W\Lambda^{-1/2}Tz+u_+\\
-\bar W\Lambda^{-1/2}\bar Tz+u_-\\
z
\end{pmatrix},\qquad
V_S^Tz=0,\quad W^\dagger u_+=0,\quad W^Tu_-=0,
\tag{R.52}
$$

with complex $z,u_+,u_-$. Consequently

$$
\operatorname{rank}J_p=2k+d\leq5,\quad
\dim\ker J_p=3r-2k-d,\quad
\ker A_q=\ker[B^\dagger(\sqrt q\otimes I_r)].
\tag{R.53}
$$

**Proof.** The range condition in (R.4) gives $C=W\Lambda^{1/2}T$. Its actual support inverse gives $C^\dagger\tau^+C=T^\dagger T$, so the residual identity gives the last block of (R.51). Multiplication of the displayed Gram factor recovers all nine blocks of (R.3), including both $C$ blocks. The block equations $B^\dagger(x_+,x_-,z)=0$ are

$$
\Lambda^{1/2}W^\dagger x_++Tz=0,\quad
\Lambda^{1/2}W^Tx_-+\bar Tz=0,\quad V_S^Tz=0.
$$

Solving only on the positive spectrum gives exactly (R.52), with the full two orthogonal-complement freedoms retained. The first $2k$ columns of $B$ are independent by their upper blocks; the $d$ remaining columns are independent of them and each other by the full column rank of $V_S$. This proves the rank and dimension formulas. Finally $A_q=MM^\dagger$ with $M=(\sqrt q\otimes I_r)B$, so its kernel is exactly $\ker M^\dagger$, even when $q$ is singular. In particular weighted kernels need not be obtained by an ordinary inverse of $\sqrt q$.

At half weight $\Lambda=I_2/2$, (R.51)–(R.52) reduce exactly to (R.25)–(R.26), including $S=0$, $v=0$, zero or repeated Takagi values and every $u_\pm$. At zero only the positive eigenvalue one is inverted; $d=3$ is allowed and is attained by Theorem 2.2. There is no limiting inversion of beta and no replacement of that rank-three residual by a single vector. Theorem 1.2 supplies reverse actual-channel realization with the original trace conditions; an arbitrary PSD block relaxation is not substituted for it. $\square$

**Theorem 13.2 (frame covariance and unused environment directions).** The certificates (R.41)–(R.49) are independent of the chosen Gram factor of the same $J$. Under a real orthogonal environment coordinate change $O$, their data transform by

$$
W\mapsto OW,\quad T\mapsto TO^T,\quad V_S\mapsto OV_S,
\qquad D_j\mapsto OD_jO^T,\quad H\mapsto OHO^T.
\tag{R.54}
$$

Under a general complex environment unitary $U$, every actual environment matrix, kernel effect and certificate must instead be transported by the corresponding unitary conjugation. The underlying real antiunitary becomes $\mathfrak k'=U\mathfrak kU^\dagger$, where $\mathfrak kx=\bar x$.

**Proof.** The first assertion follows because $A_q$ and its kernel effect in (R.41) use $J$, not a factorization. Direct substitution proves (R.54). For a complex change use $J'=(I_3\otimes U)J(I_3\otimes U^\dagger)$ and $Z_q'=(I_3\otimes U)Z_q(I_3\otimes U^\dagger)$. Then $H'=UHU^\dagger$, $D_j'=UD_jU^\dagger$, and the support conditions, eigenvalue bounds, inverse traces and matrix order are invariant. The second phase block is $U\bar\tau U^\dagger=\mathfrak k'(U\tau U^\dagger)\mathfrak k'^{-1}$, generally different from $\overline{U\tau U^\dagger}$. The same transport is required for the barred $C$ relation. A complex gauge cannot silently make the original real structure into entrywise conjugation.

With $\Lambda$ fixed diagonal, an internal eigenframe change $W\mapsto WV$ preserves (R.50) when $V$ is unitary and commutes with $\Lambda$, with $T\mapsto V^\dagger T$. At half weight every $V\in U(2)$ is allowed, exactly as in (R.24). In particular using Takagi coordinates at that endpoint requires cotransforming $T$; their two angles alone do not determine (R.52).

If zero Kraus matrices are added, embed the used environment $E$ into $E\oplus E_0$. The actual $A_q$ vanishes on $\mathbb C^3\otimes E_0$. For the full kernel projection its contribution in (R.41) is $I_{E_0}$, so $H_{q,\mathrm{full}}'=H_{q,\mathrm{full}}\oplus I_{E_0}$. Finite full-kernel aggregates have the same direct sum. Thus their minimum eigenvalue and inverse traces against $D_j\oplus0$ are unchanged. A selected partial-kernel effect need not acquire that identity block automatically; it can be extended by this full unused block if desired. This distinction preserves validity for nonminimal environments without attributing extra charge to an unselected effect. $\square$

## 14. An actual family whose two third-column coherences meet

**Theorem 14.1 (real three-Kraus family and its joint complement).** In the fixed original passive output basis $e_0,\ldots,e_4$, let $0\leq w\leq1$, $0\leq\theta\leq\pi/4$ and $0\leq\beta\leq1/2$. Define

$$
\begin{aligned}
K_0={}&\sqrt a\cos\theta(e_0\langle0|+e_1\langle1|)
       +\sqrt w\,e_4\langle2|,\\
K_1={}&\sqrt\beta(e_2\langle0|+e_3\langle1|)
       +\sqrt{1-w}\,e_0\langle2|,\\
K_2={}&\sqrt a\sin\theta(-e_1\langle0|+e_0\langle1|).
\end{aligned}
\tag{R.55}
$$

These define an actual original-class CPTP encoder. In its real environment basis $\epsilon_0,\epsilon_1,\epsilon_2$, put $z_\theta=\cos\theta\,\epsilon_0+i\sin\theta\,\epsilon_2$. Its joint data are

$$
\begin{aligned}
\tau&=a|z_\theta\rangle\langle z_\theta|+\beta|\epsilon_1\rangle\langle\epsilon_1|,\\
C&=\sqrt{a(1-w)/2}\,|z_\theta\rangle\langle\epsilon_1|,\\
\sigma&=w|\epsilon_0\rangle\langle\epsilon_0|+(1-w)|\epsilon_1\rangle\langle\epsilon_1|,\\
S&=w|\epsilon_0\rangle\langle\epsilon_0|,\qquad
f(\tau,\bar\tau)=a\cos(2\theta)+\beta=1-2a\sin^2\theta.
\end{aligned}
\tag{R.56}
$$

**Proof.** Different columns of each $K_\alpha$ are orthogonal. Their summed squared norms are $a\cos^2\theta+\beta+a\sin^2\theta=1$ for each of the first two inputs and $w+1-w=1$ for the third. Thus $\sum_\alpha K_\alpha^TK_\alpha=I_3$ on the whole input space.

For $u_\pm=(e_0\pm ie_1)/\sqrt2$ and $v_\pm=(e_2\pm ie_3)/\sqrt2$, the three phase images are respectively $\sqrt a\cos\theta\,u_\pm$, $\sqrt\beta\,v_\pm$ and $\pm i\sqrt a\sin\theta\,u_\pm$. Therefore

$$
N(\chi_\pm)=a|u_\pm\rangle\langle u_\pm|+\beta|v_\pm\rangle\langle v_\pm|,
$$

with difference spectrum $(a,\beta,0,-\beta,-a)$. The zero weight is simply omitted at beta zero. In the same dilation,

$$
V\chi_+=\sqrt a\,u_+\otimes z_\theta+\sqrt\beta\,v_+\otimes\epsilon_1,
\quad V|2\rangle=\sqrt w\,e_4\otimes\epsilon_0+\sqrt{1-w}\,e_0\otimes\epsilon_1.
$$

Taking the two partial traces gives the first three blocks in (R.56). On the support of $\tau$, $C^\dagger\tau^+C=(1-w)|\epsilon_1\rangle\langle\epsilon_1|/2$; its conjugate is identical, also at beta zero. This gives $S$. Root fidelity adds on the two orthogonal environment blocks and $\langle z_\theta,\bar z_\theta\rangle=\cos2\theta\geq0$, giving the last formula. The three-Kraus list constructs this family; it is not a parameterization or rank restriction of the full original class. $\square$

**Theorem 14.2 (orthogonal input contraction using the shared output direction).** For every parameter in (R.55),

$$
\delta_N\geq1-\mu(N)\geq1-\sqrt a,\qquad
\mu(N)=\sqrt{aw\cos^2\theta+\beta(1-w)}.
\tag{R.57}
$$

The bound holds against every complex CPTP recovery with arbitrary finite references.

**Proof.** Take the orthogonal actual inputs $\psi_\pm=(|0\rangle\pm|2\rangle)/\sqrt2$. Their projector difference is $|0\rangle\langle2|+|2\rangle\langle0|$. Direct application of the actual Kraus matrices gives

$$
N(P_{\psi_+}-P_{\psi_-})
=u(|e_0\rangle\langle e_4|+|e_4\rangle\langle e_0|)
+v(|e_2\rangle\langle e_0|+|e_0\rangle\langle e_2|),
$$

where $u=\sqrt{aw}\cos\theta$ and $v=\sqrt{\beta(1-w)}$. On the ordered subspace $(e_4,e_0,e_2)$ the matrix is

$$
\begin{pmatrix}0&u&0\\u&0&v\\0&v&0\end{pmatrix},
\qquad\operatorname{spec}=\{\sqrt{u^2+v^2},0,-\sqrt{u^2+v^2}\}.
\tag{R.58}
$$

The two additional output eigenvalues are zero. Its half trace norm is thus $\mu(N)$. For any one recovery, write $\varepsilon_R=\|RN-\mathrm{id}_3\|_\diamond$. The triangle inequality and CPTP trace-norm contraction give

$$
2=\|P_{\psi_+}-P_{\psi_-}\|_1
\leq2\varepsilon_R+\|RN(P_{\psi_+}-P_{\psi_-})\|_1
\leq2\varepsilon_R+2\mu(N).
$$

Infimizing $R$ proves the first bound. The second follows from $a\geq\beta$, since

$$
a-\mu(N)^2=(a-\beta)(1-w)+aw\sin^2\theta\geq0.
\tag{R.59}
$$

These product inputs are valid tests in the full-reference diamond supremum; they do not restrict that supremum or the recovery domain. The useful information in (R.58) is that the two third-column coherences meet at the same actual output direction $e_0$, giving a square root of a sum of squares.

This direction information is not encoded by $w$ and $f(\tau,\bar\tau)$ alone. With the same $\beta,w,\theta$, the earlier family (R.17) has those same scalars, but its $K_0$ third column is the unit vector $\sqrt{1-w}\,e_2+\sqrt w\,e_4$ and its $K_1$ third column is zero. For this particular pair its half output distance is therefore $\sqrt a\cos\theta$, rather than (R.57). This comparison concerns a witness contraction, not the exact recovery optimum of either family.

Physical matrices remain $K_\alpha^{\rm ph}=DK_\alpha L^\dagger$, and recovery transport is exactly (P.16) of the [phase-gain volume](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#4-an-actual-upper-family-and-its-individual-optimum). The corresponding physical test pair is $L\psi_\pm$, while physical $\theta_\pm$ retain the passive sign swap (P.2). These identities preserve the full complex recovery optimization and add no free physical $D$ gate or native encoder/decoder supply. $\square$

## 15. Strict relatively open exclusions at every positive beta

**Theorem 15.1 (nonempty exclusions inside the prior remaining region).** For each fixed $0<\beta\leq1/2$, the original class has a nonempty relatively open subset on which

$$
C\ne0,\quad\tau\ne\bar\tau,\quad
\sqrt a<f(\tau,\bar\tau)<1,\quad
w_c(\beta)<w<1,\quad\delta_N>U(\beta).
\tag{R.60}
$$

Here $w_c$ is the exact threshold (R.16). The subset is relative to the whole actual original class at that beta, without a Kraus-rank restriction.

**Proof.** Choose a center $N_0$ in (R.55) with

$$
w=a,\qquad0<\sin^2\theta<\frac{1-\sqrt a}{2a}.
\tag{R.61}
$$

The upper endpoint is positive and below $1/2$, so an allowed $0<\theta<\pi/4$ exists. Formula (R.56) gives $\sqrt a<f(\tau,\bar\tau)<1$. Also $w_c<1/2\leq a<1$, $C\ne0$, and $\tau_{02}=-ia\cos\theta\sin\theta\ne0$. Thus the center satisfies all prior remaining conditions (R.21). Formula (R.59) is strictly positive: if $a>\beta$ its first term is positive, and at $a=\beta=1/2$ its second term is still positive. Hence $\mu(N_0)<\sqrt a$ and (R.57) gives the strict bound.

For the same fixed pair $\psi_\pm$ define $\mu(N)=\|N(P_{\psi_+}-P_{\psi_-})\|_1/2$ for any channel. Since the input difference has trace norm two,

$$
|\mu(N)-\mu(M)|\leq\|N-M\|_\diamond.
\tag{R.62}
$$

The same contraction proof gives $\delta_N\geq1-\mu(N)$ for every neighboring channel, independent of its Kraus rank. Therefore the diamond ball

$$
\|N-N_0\|_\diamond<\sqrt a-\mu(N_0)
\tag{R.63}
$$

consists of strict exclusions whenever $N$ remains in the original class.

The remaining inequalities can also be expressed continuously without choosing a continuous environment or Kraus list. Put $A=N(\chi_+)+N(\chi_-)$. On this fixed positive-beta class its eigenvalues are $a,\beta,a,\beta,0$, so

$$
\Pi=\frac{A(I_5-A)}{a\beta},\qquad
w=\operatorname{Tr}[(I_5-\Pi)N(|2\rangle\langle2|)],\qquad
f(\tau,\bar\tau)=\|N(|\chi_+\rangle\langle\chi_-|)\|_1.
\tag{R.64}
$$

The first identity is the spectral polynomial, valid also at the repeated half-weight eigenvalue. The second is Theorem 2.1; the last is the cross-partial-trace identity in Theorem 4.3, equivalently Watrous, Corollary 3.23, (3.148), printed p.152. They are continuous functions of the actual channel. Thus the conditions $w_c<w<1$ and $\sqrt a<f<1$ define a relatively open set containing $N_0$. The first ensures $C\ne0$ by the traced Schur identity; the second ensures $\tau\ne\bar\tau$, since normalized states have root fidelity one exactly when equal. Intersecting this set with (R.63) proves (R.60).

No three-Kraus restriction is imposed on this intersection. At beta zero the denominator in (R.64) vanishes and the actual phase-support rank changes; this polynomial and the positive-beta open-set claim are not extended there. The kernel certificates of Sections 11–13 remain valid there, while the benchmark lower bound is just zero. $\square$

## 16. An exact rational joint-kernel witness beyond the prior exclusions

**Theorem 16.1 (rational actual encoder, two kernel vectors and inverse trace).** In (R.55), take

$$
\beta=\frac9{25},\qquad a=w=\frac{16}{25},\qquad
\cos\theta=\frac{12}{13},\qquad\sin\theta=\frac5{13}.
$$

The actual real matrices are

$$
\begin{aligned}
K_0&=\frac{48}{65}(e_0\langle0|+e_1\langle1|)+\frac45e_4\langle2|,\\
K_1&=\frac35(e_2\langle0|+e_3\langle1|+e_0\langle2|),\\
K_2&=\frac4{13}(-e_1\langle0|+e_0\langle1|).
\end{aligned}
\tag{R.65}
$$

For this encoder there is $H\in\mathscr H(J)$ with

$$
H=\operatorname{diag}\left(\frac{169}{850},\frac{128}{425},\frac12\right),
\qquad g_N^2\leq\frac{681}{850},\qquad
\delta_N\geq\frac{169}{425}>\frac15=U(9/25),
\tag{R.66}
$$

and the exact joint inverse trace is

$$
\operatorname{Tr}\left[\tau\left(\frac45I_3+H\right)^{-1}\right]
=\frac{2352003}{2487004}<1.
\tag{R.67}
$$

**Proof.** Theorem 14.1 gives actual original-class membership, not merely positivity of a proposed complementary block matrix. Its joint blocks in the unchanged real environment are

$$
\tau=\begin{pmatrix}
2304/4225&0&-192i/845\\
0&9/25&0\\
192i/845&0&16/169
\end{pmatrix},\quad
C=\begin{pmatrix}
0&72\sqrt2/325&0\\
0&0&0\\
0&6i\sqrt2/65&0
\end{pmatrix},
$$

$$
\sigma=\operatorname{diag}(16/25,9/25,0),\qquad
S=\operatorname{diag}(16/25,0,0).
\tag{R.68}
$$

In particular

$$
f(\tau,\bar\tau)=\frac{16}{25}\frac{119}{169}+\frac9{25}
=\frac{137}{169}>\frac45,
\qquad w=\frac{16}{25}>\frac12>w_c(9/25),
$$

and $C\ne0$, $\tau\ne\bar\tau$. This witness is outside all three prior sufficient exclusions in Theorems 3.2 and 4.3.

Use the original-real reference density $q_0=(|0\rangle\langle0|+|2\rangle\langle2|)/2$. The phase reference density, using the transpose transport of Definition 11.1, is

$$
q_p=\begin{pmatrix}1/4&1/4&0\\1/4&1/4&0\\0&0&1/2\end{pmatrix}.
\tag{R.69}
$$

It contains phase off-diagonal entries. For the kernel calculation use the same actual complement in its original-input Choi frame $J_0$. Its relevant blocks are

$$
\Gamma(P_0)=\operatorname{diag}(2304/4225,9/25,16/169),\quad
\Gamma(P_2)=\operatorname{diag}(16/25,9/25,0),\quad
\Gamma(|0\rangle\langle2|)=\frac{144}{325}|\epsilon_0\rangle\langle\epsilon_1|.
\tag{R.70}
$$

Two orthonormal unit vectors in $\ker A_{q_0}$ are

$$
k=\frac{13|0,\epsilon_0\rangle-16|2,\epsilon_1\rangle}{\sqrt{425}},
\qquad \ell=|2,\epsilon_2\rangle.
\tag{R.71}
$$

Indeed the first kernel equation, after the common filter factor $1/2$, is

$$
\begin{pmatrix}2304/4225&144/325\\144/325&9/25\end{pmatrix}
\begin{pmatrix}13\\-16\end{pmatrix}=0;
$$

there is no coupling of these two coordinates to any other coordinate of $A_{q_0}$. The second follows from the zero third diagonal entry of $\Gamma(P_2)$ and the displayed cross block. The filtered Choi matrix vanishes on the remaining reference direction $|1\rangle$, so no omitted input block changes these kernel equations.

Take $Z_{q_0}=|k\rangle\langle k|+|\ell\rangle\langle\ell|$. It satisfies $0\preceq Z_{q_0}\preceq I-P_{q_0}$. In (R.41), $\sqrt{q_0}$ multiplies each displayed reference component by $1/\sqrt2$. The partial trace therefore gives exactly the diagonal $H$ in (R.66), whose minimum eigenvalue is $169/850$. Theorem 11.2 gives (R.66), and $169/425-1/5=84/425>0$.

The inverse in (R.67) is diagonal, so only the three diagonal entries of the nonreal $\tau$ contribute to its trace. Exact substitution yields the displayed fraction, with $2487004-2352003=135001>0$. Thus the same joint data also pass (R.47); the minimum-eigenvalue bound in (R.66) is stronger for this particular $H$. Neither lower certificate is asserted to equal this encoder's exact recovery optimum.

The direct contraction gives, independently,

$$
\mu(N)^2=\frac{50553}{105625},\qquad
\delta_N\geq1-\frac{\sqrt{50553}}{325}>\frac15.
$$

For (R.17) at the same parameters the same-pair squared contraction is $2304/4225$, confirming the direction distinction in Theorem 14.2 while $w$ and $f(\tau,\bar\tau)$ agree. All comparisons are for actual original-class channels. $\square$

## 17. Common-object necessary conditions and the remaining sharp gap

**Theorem 17.1 (all certificates and all orthogonal pairs constrain an improver).** Fix positive beta and an actual original-class encoder. If $\delta_N<U(\beta)$, then there is one maximizing environment density $\omega_\star$ for which, simultaneously,

$$
\begin{gathered}
m(\omega_\star)=g_N^2>t_\beta,\\
f(\tau,\omega_\star)^2>t_\beta,\quad
f(\bar\tau,\omega_\star)^2>t_\beta,\quad
f(\sigma,\omega_\star)^2>t_\beta,\\
\operatorname{Tr}(\omega_\star H_{q,Z_q})<\frac{U(\beta)}2
\quad\text{for every complex density }q\text{ and every allowed }Z_q.
\end{gathered}
\tag{R.72}
$$

For every finite aggregate $H\in\mathscr H(J)$ the same $\omega_\star$ has $\operatorname{Tr}(\omega_\star H)<U(\beta)/2$, and necessarily

$$
\lambda_{\min}(H)<\frac{U(\beta)}2,\qquad
\operatorname{Tr}[D(sI_r+H)^{-1}]>1
\quad(D=\tau,\bar\tau,\sigma).
\tag{R.73}
$$

Every simultaneous matrix $M$ allowed in Theorem 12.2 must likewise have $\lambda_{\max}(M)>t_\beta$. In addition, for every complex unit $u\in\operatorname{span}(|0\rangle,|1\rangle)$ and every real $\varphi$,

$$
\mu_{u,\varphi}(N):=
\frac12\left\|N\left(e^{-i\varphi}|u\rangle\langle2|
+e^{i\varphi}|2\rangle\langle u|\right)\right\|_1
\geq1-\delta_N>\sqrt a.
\tag{R.74}
$$

**Proof.** The pure-target bound gives $2(1-g_N^2)\leq\delta_N<1-s$, hence $g_N^2>t_\beta$. In a fixed finite environment the density domains are compact, and $\Phi(q,\omega)^2$ is continuous even at singular matrices. Its minimum over $q$ is continuous in $\omega$, so a maximizing $\omega_\star$ exists. Apply every inequality (R.44) at this one maximizer. They give the three strict fidelity conditions and all of the strict kernel charges in (R.72), with the quantifier order $\exists\omega_\star\ \forall(q,Z_q)$.

A finite convex average of these strict charge inequalities is still strict; thus $\lambda_{\min}(H)\leq\operatorname{Tr}(\omega_\star H)<U/2$. Contraposition of (R.47) gives all three inverse inequalities. The pointwise proof of Theorem 12.2 gives $\operatorname{Tr}(\omega_\star M)\geq m(\omega_\star)>t_\beta$, proving its eigenvalue condition.

Finally the states $(e^{-i\varphi}u\pm|2\rangle)/\sqrt2$ are orthogonal and have projector difference equal to the input in (R.74). The same-recovery contraction argument of Theorem 14.2 gives $\delta_N\geq1-\mu_{u,\varphi}(N)$ for each pair. Rearrangement proves (R.74). At beta zero the antecedent would be $\delta_N<0$ and is impossible; no positive-beta support formula is needed for that observation. $\square$

**Definition 17.2 (scope of the increment and attribution).** The joint kernel aggregation, inverse and simultaneous-state tests, their actual coherent-third-column family, the relatively open exclusions and the exact rational witness are repo-derived conditional ordinary mathematics for the domain of Definition 1.1. The proofs use standard results within that composition; they claim no new general fidelity inequality, global originality or priority. The standard literature and its relevant boundaries are as follows.

| Source and precise locator | Role and boundary in this model |
| --- | --- |
| [C. Bény and O. Oreshkov, *General conditions for approximate quantum error correction and near-optimal recovery channels*, arXiv:0907.5391v4, Theorem 1, (3), PDF p.2](https://arxiv.org/pdf/0907.5391v4); [*Approximate simulation of quantum channels*, arXiv:1103.0649v3, (54)–(56), Corollary 5, (64), PDF pp.5–7](https://arxiv.org/pdf/1103.0649v3) | The unrestricted finite-dimensional root-fidelity recovery/complement duality reused in (R.27). The identity target has scalar-trace complement and therefore one common prepared environment state. The Kraus-restricted theorem is not used in place of the unrestricted corollary. |
| [J. Watrous, *The Theory of Quantum Information*, (1.173)–(1.174), p.33; Theorem 3.22, p.151; Corollary 3.23, (3.148), p.152; Theorem 3.27, (3.173), p.156](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf) | Schatten duality/Hölder, Uhlmann, the cross-partial-trace identity and CPTP fidelity monotonicity, on finite complex spaces including singular PSD operands. These supply proof steps in Sections 11–16, not standalone new mathematics. |
| [G. Chiribella, M. Dall'Arno, G. M. D'Ariano, C. Macchiavello and P. Perinotti, *Quantum error correction with degenerate codes for correlated noise*, arXiv:1007.3655v2, (11), Proposition 3, (12), PDF p.3](https://arxiv.org/pdf/1007.3655v2) | The exact packing statement uses the KL-matrix rank; replacing it by noise Choi rank requires nondegeneracy. It supplies no automatic approximate sharp constant from $3\cdot2>5$. |
| [S. L. Braunstein and A. K. Pati, *Quantum information cannot be completely hidden in correlations: implications for the black-hole information paradox*, arXiv:gr-qc/0603046v1, (4), (6)–(9), PDF p.2](https://arxiv.org/pdf/gr-qc/0603046v1) | Exact hiding gives factorization. The approximate premise includes an actual reference-product trace-norm estimate; the two phase-output spectra do not supply that premise. |
| [D. Kretschmann, D. Schlingemann and R. F. Werner, *The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation*, arXiv:quant-ph/0605009v1, Theorem 3, (32), PDF p.9](https://arxiv.org/pdf/quant-ph/0605009v1) | The cb inequalities correspond under Schrödinger duality to diamond inequalities. Their square/quadratic-root bounds do not by themselves prove this spectral model's sharp curve. |
| [J. Wu, M. Grossi, D. M. Kürkçüoğlu and S. Zorzetti, *Universal Optimization and Tighter Fidelity Bounds for Approximate Quantum Error Correction*, arXiv:2607.24968v2, Section 2, (1)–(6), Corollary 2, (8)](https://arxiv.org/html/2607.24968v2) | The relevant $F_e$ uses the maximally entangled input, fixing $I/d_L$. Corollary 2 requires every distinct-logical-index KL cross term to vanish. The actual $C\ne0$ sector is not covered by that simplification; fixed-input fidelity does not replace worst-input fidelity or diamond error. |
| [B. Li and L. Jiang, *High-Rank Encoding Can Improve Approximate Quantum Error Correction*, arXiv:2609.00778v1, Theorem 1, Section III, “A High-Rank Example”](https://arxiv.org/html/2609.00778v1) | The theorem concerns a specified input density and CPTNI maps, including deterministic CPTP maps as a special case. Its displayed example has $d_C=d_L^2=9$ for a qutrit, not output dimension five. It supplies neither an original-class diamond counterexample nor a reduction to three Kraus matrices. |

The last five comparisons are boundaries on possible imports, not premises asserting new lower or upper bounds. The existing $C=0$ exclusion remains a calibration, and the full-input duality and SDP of Sections 6–8 remain their cited interfaces.

The original sharp target is still $\delta^*_{\mathcal R}(\beta)=U(\beta)$: either prove $\delta_N\geq U(\beta)$ for every actual original real-Kraus encoder, which together with the attained upper family (P.11)–(P.16) in the [phase-gain volume](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#4-an-actual-upper-family-and-its-individual-optimum) would prove equality, or exhibit an actual original-class $N$ and one complex CPTP recovery with a rigorous full-reference unhalved diamond upper certificate strictly below $U(\beta)$. Universal incompatibility of (R.72)–(R.74) has not been established. Satisfying those necessary conditions would not construct an improving recovery. Failure of one kernel choice, inverse test or even the stronger uniform fidelity-certificate route would not refute the original diamond target.

All statements retain the original coordinates and physical/passive bijection, finite references, arbitrary complex recoveries and native applicability limits of the phase-gain volume. No free physical $D$ gates, source preparation, native encoder/decoder apparatus, physical realization or kernel verification is a conclusion of these ordinary channel arguments.

## 追加锚（本行以下为增补区）

## 18. An actual real-Kraus family with coupled third-column data

**Definition 18.1 (fixed model and the restricted method).** Retain Definition 1.1 and the [phase-gain volume, Definitions 1.1–1.4](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#1-actual-channels-physical-coordinates-and-the-native-contract). Thus the passive input and output are $\mathbb C^3$ and the entire $\mathbb C^5$, with fixed real bases $|0\rangle,|1\rangle,|2\rangle$ and $e_0,\ldots,e_4$. For the family below set

$$
a=1-\beta,\qquad 0<\beta\leq\tfrac12,\qquad
0<t<\sqrt{a\beta},\qquad
r_\beta=\sqrt{\beta/a},\qquad
s_t=\sqrt{1-(2+\beta/a)t^2}.
$$

Here $s_t$ is a family parameter, distinct from the abbreviation $s=\sqrt a$ in Sections 11–17. In particular $s_t^2>a^2>0$. For a complex unit $u\in\operatorname{span}(|0\rangle,|1\rangle)$ and $\varphi\in\mathbb R$, use exactly the restricted inputs of (R.74):

$$
X(u,\varphi)=e^{-i\varphi}|u\rangle\langle2|
             +e^{i\varphi}|2\rangle\langle u|,\qquad
\mu_N(u,\varphi)=\tfrac12\|N(X(u,\varphi))\|_1.
$$

Their preimages are the orthogonal pure states $(e^{-i\varphi}u\pm|2\rangle)/\sqrt2$. The stronger proposed method would require, for every original-class encoder, some such pair with $\mu_N\leq\sqrt a$. This requirement is separate from Theorem 17.1: (R.74) gives a necessary condition for improvement and asserts no sufficiency.

**Theorem 18.2 (actual channel, phase outputs and joint complement).** The two real matrices

$$
\begin{aligned}
K_0&=\sqrt a(e_0\langle0|+e_1\langle1|)
       +(s_t e_4-r_\beta t e_1)\langle2|,\\
K_1&=\sqrt\beta(e_2\langle0|+e_3\langle1|)
       +t(e_0+e_3)\langle2|
\end{aligned}
\tag{R.75}
$$

define the actual complex-linear CPTP map $N_{\beta,t}(X)=K_0XK_0^T+K_1XK_1^T$. Its physical channel belongs to $\mathcal R_\beta$. Its encoder Choi rank is two, while the Choi rank of its actual complement is five.

**Proof.** Direct multiplication, including the third-column cross terms, gives

$$
\begin{aligned}
K_0^TK_0&=\begin{pmatrix}
a&0&0\\0&a&-\sqrt\beta t\\0&-\sqrt\beta t&1-2t^2
\end{pmatrix},\qquad
K_1^TK_1=\begin{pmatrix}
\beta&0&0\\0&\beta&\sqrt\beta t\\0&\sqrt\beta t&2t^2
\end{pmatrix},\\
K_0^TK_0+K_1^TK_1&=I_3.
\end{aligned}
\tag{R.76}
$$

These real Kraus matrices therefore give complete positivity and trace preservation on all complex matrices. For $f_\pm=(e_0\pm ie_1)/\sqrt2$ and $g_\pm=(e_2\pm ie_3)/\sqrt2$,

$$
N_{\beta,t}(\chi_\pm)
=a|f_\pm\rangle\langle f_\pm|
 +\beta|g_\pm\rangle\langle g_\pm|.
\tag{R.77}
$$

The four vectors are orthonormal, so these states have orthogonal supports and nonzero spectra $(a,\beta)$; their difference has spectrum $(a,\beta,0,-\beta,-a)$ and is purely imaginary Hermitian. In physical coordinates, with precisely $D=\operatorname{diag}(1,i,i,i,1)$ and $L=\operatorname{diag}(1,i,i)$ from (P.1), the actual matrices are $K_\alpha^{\rm ph}=DK_\alpha L^\dagger$. Consequently $N^{\rm ph}(\theta_\pm)=D N_{\beta,t}(\chi_\mp)D^\dagger$, with the sign reflection of (P.2). This verifies the actual original-model spectrum condition; these coordinate identities supply no physical gates.

Use the same real environment basis $|0_E\rangle,|1_E\rangle$ and the actual dilation in (R.1). Its entries are $\Gamma(X)_{\alpha\gamma}=\operatorname{Tr}(K_\alpha X K_\gamma^T)$. Writing $E_{ij}=|i\rangle\langle j|$ gives

$$
\begin{gathered}
D_\beta=\Gamma(E_{00})=\Gamma(E_{11})=\operatorname{diag}(a,\beta),
\qquad \Gamma(E_{01})=0,\\
C_0=\Gamma(E_{02})=t\begin{pmatrix}0&\sqrt a\\0&0\end{pmatrix},\qquad
C_1=\Gamma(E_{12})=t\begin{pmatrix}-\sqrt\beta&0\\0&\sqrt\beta\end{pmatrix},\\
\sigma=\Gamma(E_{22})=\operatorname{diag}(1-2t^2,2t^2),\qquad
J_0=\begin{pmatrix}
D_\beta&0&C_0\\0&D_\beta&C_1\\C_0^T&C_1^T&\sigma
\end{pmatrix}.
\end{gathered}
\tag{R.78}
$$

The symbol $D_\beta$ is an environment density, distinct from the physical coordinate matrix $D$. For the fixed phase-input basis matrix $H$ in (R.2), the Choi reference transformation remains $J_p=(H^T\otimes I_2)J_0(\bar H\otimes I_2)$. It follows that

$$
J_p=\begin{pmatrix}
D_\beta&0&C\\0&D_\beta&\bar C\\C^\dagger&C^T&\sigma
\end{pmatrix},\qquad
\tau=D_\beta,\qquad
C=\frac{C_0+iC_1}{\sqrt2}
 =\frac{t}{\sqrt2}\begin{pmatrix}-i\sqrt\beta&\sqrt a\\0&i\sqrt\beta\end{pmatrix},
\qquad\operatorname{Tr}C=0.
\tag{R.79}
$$

The left reference factor is $H^T$, as proved in (R.2), rather than $H^\dagger$. In particular $C\ne0$. Directly,

$$
\begin{gathered}
C^\dagger D_\beta^{-1}C+C^TD_\beta^{-1}\bar C
 =t^2\operatorname{diag}(\beta/a,2),\\
S=\sigma-C^\dagger D_\beta^{-1}C-C^TD_\beta^{-1}\bar C
 =\operatorname{diag}(s_t^2,0),\qquad
\operatorname{rank}J_\Gamma=2+2+1=5.
\end{gathered}
\tag{R.80}
$$

The rank identity is the actual-support congruence (R.5), applied to the positive definite $D_\beta$ and this nonzero $S$. The two encoder matrices are linearly independent, as is already seen from their $|0\rangle$ columns, so the encoder Choi rank is two. All blocks above come from (R.75); no independently realized choice of $C$ or $S$ enters the construction. The fact that $\tau$ is real diagonal here does not restrict the full class to real or commuting complementary outputs. $\square$

## 19. Exact minimum over every complex restricted direction

**Theorem 19.1 (continuum restricted minimum and attainment).** For every parameter in Definition 18.1,

$$
\min_{\substack{u\in\operatorname{span}(|0\rangle,|1\rangle),\ \|u\|=1\\
                 \varphi\in\mathbb R}}
\mu_{N_{\beta,t}}(u,\varphi)
=\sqrt a\,s_t+\sqrt\beta\,t>\sqrt a.
\tag{R.81}
$$

**Proof.** Absorb the unrestricted phase into $c=e^{-i\varphi}u=c_0|0\rangle+c_1|1\rangle$, with $|c_0|^2+|c_1|^2=1$. Define

$$
p=c_0e_0+c_1e_1,\qquad q=c_0e_2+c_1e_3,\qquad
w_0=e_0+e_3,\qquad A_t=\sqrt a\,s_t,\qquad B_t=\sqrt\beta\,t.
$$

The $w_0$ here is a vector, distinct from the outside-support probability $w$ of (R.10). Substitution of the actual Kraus matrices gives

$$
H_t:=N_{\beta,t}(X(u,\varphi))
=A_t(pe_4^\dagger+e_4p^\dagger)
 +B_t(qw_0^\dagger+w_0q^\dagger-pe_1^\dagger-e_1p^\dagger).
\tag{R.82}
$$

Let $P_U$ project onto $U=\operatorname{span}(p,e_4)$, let $P=I-P_U$, and put $\xi=Pw_0$. The vector $q$ is unit and lies in $U^\perp$, whence

$$
PH_tP=B_t(q\xi^\dagger+\xi q^\dagger).
\tag{R.83}
$$

For this actual matrix, the reflection $Z=P_U-P$ is unitary and self-adjoint, and its two-block pinching is $(H_t+ZH_tZ^\dagger)/2=P_UH_tP_U+PH_tP$. Triangle inequality and unitary invariance therefore give, for every complex $c$,

$$
\|H_t\|_1\geq\|P_UH_tP_U\|_1+\|PH_tP\|_1.
\tag{R.84}
$$

In the orthonormal basis $(p,e_4)$, the first block and its half norm are

$$
P_UH_tP_U=
\begin{pmatrix}-2B_t\operatorname{Re}c_1&A_t\\A_t&0\end{pmatrix},\qquad
\tfrac12\|P_UH_tP_U\|_1
=\sqrt{A_t^2+B_t^2(\operatorname{Re}c_1)^2}.
\tag{R.85}
$$

For the second block, write $z=\langle q,\xi\rangle$, using the inner product conjugate-linear in its first variable. On $\operatorname{span}(q,\xi)$ the two possibly nonzero eigenvalues of $q\xi^\dagger+\xi q^\dagger$ are

$$
\operatorname{Re}z\ \pm\sqrt{\|\xi\|^2-(\operatorname{Im}z)^2}.
$$

Indeed splitting $\xi=zq+\xi_\perp$ gives the matrix with diagonal $(2\operatorname{Re}z,0)$ and off-diagonal magnitude $\|\xi_\perp\|$. Cauchy–Schwarz gives $\|\xi\|^2-|z|^2\geq0$, so the two displayed eigenvalues have opposite signs or include zero. Thus in this compression

$$
\tfrac12\|q\xi^\dagger+\xi q^\dagger\|_1
=\sqrt{\|\xi\|^2-(\operatorname{Im}\langle q,\xi\rangle)^2}.
\tag{R.86}
$$

Here $\|\xi\|^2=2-|c_0|^2=1+|c_1|^2$ and $\langle q,\xi\rangle=\bar c_1$. Combining the two blocks proves

$$
\begin{aligned}
\mu_{N_{\beta,t}}(u,\varphi)
&\geq\sqrt{A_t^2+B_t^2(\operatorname{Re}c_1)^2}
       +B_t\sqrt{1+(\operatorname{Re}c_1)^2}\\
&\geq A_t+B_t.
\end{aligned}
\tag{R.87}
$$

This is a pointwise inequality over the whole complex unit sphere. At $c_0=0,c_1=i$, (R.82) is

$$
H_t=iA_t(e_1e_4^\dagger-e_4e_1^\dagger)
    +iB_t(e_3e_0^\dagger-e_0e_3^\dagger),
$$

a direct sum on two orthogonal planes with eigenvalues $A_t,-A_t,B_t,-B_t,0$. Hence the lower bound is actually attained. Finally

$$
A_t^2=a-(2-\beta)t^2,\qquad
A_t^2-(\sqrt a-B_t)^2=2t(\sqrt{a\beta}-t)>0.
$$

Since $B_t<\beta\sqrt a<\sqrt a$, both sides compared before squaring are nonnegative. It follows that $A_t+B_t>\sqrt a$, proving (R.81). $\square$

**Corollary 19.2 (special parameter and endpoint scope).** The admissible choice

$$
t^2=\frac{a\beta}{2(2-\beta)}
\quad\Longrightarrow\quad
\min_{u,\varphi}\mu_{N_{\beta,t}}(u,\varphi)
=\sqrt{\frac{2a}{2-\beta}}.
\tag{R.88}
$$

At $\beta=1/2$ this is $\sqrt{2/3}>1/\sqrt2$.

**Proof.** At this parameter $s_t^2=1-\beta/2$, so $A_t=\sqrt{a(2-\beta)/2}$ and $B_t=\beta\sqrt{a/[2(2-\beta)]}$. Their sum gives (R.88), and $0<t^2<a\beta$ since $2(2-\beta)>1$.

For fixed positive beta the construction also extends to $t=0$ and $t=\sqrt{a\beta}$. The same pinching and attaining direction give the minimum $A_t+B_t$ at both endpoints. At $t=0$, $s_t=1$ and (R.75) is exactly the existing upper family (P.11); its individual optimum $U(\beta)$ is already proved in (P.12)–(P.16). At $t=\sqrt{a\beta}$, $s_t=a$ and $A_t+B_t=\sqrt a(a+\beta)=\sqrt a$. Neither endpoint is a strict restricted-method counterexample. At $\beta=1/2$ every interior $t$ still gives the strict inequality (R.81).

At $\beta=0$ the stipulated positive-$t$ interval is empty. The formulas dividing by beta in the tilted and kernel calculations below are not used there. Trace-norm contraction gives $\mu_N(u,\varphi)\leq1=\sqrt a$ for every actual channel and each such input; the isometric instance of (P.11) attains the zero class optimum. These zero-beta statements use the existing endpoint result, without extending the positive-beta inverse or kernel-rank calculations across its rank change. $\square$

## 20. The same joint kernel selects a tilted exclusion pair

**Theorem 20.1 (tilted pair, consumed two-Kraus factorization and diamond exclusion).** For the same actual encoder (R.75), let

$$
v=\frac{\sqrt\beta\,|2\rangle-t|1\rangle}{\sqrt{\beta+t^2}},\qquad
\psi_\pm=\frac{|0\rangle\pm v}{\sqrt2}.
\tag{R.89}
$$

These are orthogonal unit pure inputs, and their exact output half distance is

$$
m_{\rm tilt}^2:=
\left[\tfrac12\|N_{\beta,t}(P_{\psi_+}-P_{\psi_-})\|_1\right]^2
=a+\frac{\beta(2\beta-1)t^2}{\beta+t^2}\leq a,
\qquad P_\psi=|\psi\rangle\langle\psi|.
\tag{R.90}
$$

**Proof.** The original-input Choi matrix in (R.78) has the real kernel vector

$$
\kappa=-\frac{t}{\sqrt a}|0\rangle\otimes|0_E\rangle
       +\left(|2\rangle-\frac{t}{\sqrt\beta}|1\rangle\right)\otimes|1_E\rangle,
\qquad J_0\kappa=0.
\tag{R.91}
$$

To see the actual kernel equation without choosing separate blocks, contract $\kappa$ with the Gram map $\mathcal F(|i\rangle\otimes|\alpha_E\rangle)=K_\alpha|i\rangle$. The reality of the Kraus matrices gives $J_0=\mathcal F^T\mathcal F$. Its image is

$$
-\frac{t}{\sqrt a}K_0|0\rangle
 +K_1\left(|2\rangle-\frac{t}{\sqrt\beta}|1\rangle\right)=0.
$$

The rank five in (R.80) makes this the whole one-dimensional kernel in dimension six. The two logical factors in (R.91) are orthogonal and nonzero, so its logical Schmidt directions are precisely $|0\rangle$ and $v$. This is a kernel of the same $C_0,C_1,\sigma$ and, by (R.2), the same phase $C,S$.

The kernel relation has a concrete factorization consumer in this family proof. For two actual real Kraus matrices, real orthonormal $u,v$ and real coefficients $\lambda,\eta$ with $\eta\ne0$ and $\lambda K_0u+\eta K_1v=0$, put $x=K_0u$ and $y=K_0v-(\lambda/\eta)K_1u$. Expanding the two Kraus contributions and then using TP gives

$$
\begin{gathered}
N(uv^T+vu^T)=xy^T+yx^T,\\
x^Ty=(K_0u)^TK_0v+(K_1u)^TK_1v=u^Tv=0,\\
\tfrac12\|N(uv^T+vu^T)\|_1=\|x\|\,\|y\|.
\end{gathered}
\tag{R.92}
$$

For nonzero $x,y$, the last equality follows from the two eigenvalues $\pm\|x\|\|y\|$ on their orthogonal span; if either vector vanishes both sides are zero. Apply this calculation to (R.75) with $u=|0\rangle$, $v$ from (R.89), $\lambda=-t/\sqrt a$ and $\eta=\sqrt{(\beta+t^2)/\beta}$. The needed relation is exactly (R.91). With $c=\sqrt\beta/\sqrt{\beta+t^2}$, direct multiplication gives

$$
K_0v=c\left(s_t e_4-\frac{t}{\sqrt{a\beta}}e_1\right),\qquad
K_1v=ct\,e_0.
\tag{R.93}
$$

Consequently $x=\sqrt a\,e_0$, $\sqrt a\,y=f$, where

$$
\begin{gathered}
f=c\left(A_t e_4+B_t e_2-\frac{t}{\sqrt\beta}e_1\right),\qquad f\perp e_0,\\
N_{\beta,t}(P_{\psi_+}-P_{\psi_-})
=N_{\beta,t}(|0\rangle\langle v|+|v\rangle\langle0|)
=e_0f^T+fe_0^T.
\end{gathered}
\tag{R.94}
$$

Thus (R.92) gives half norm $\|f\|$; the full output eigenvalues are $\|f\|,-\|f\|,0,0,0$. In particular

$$
\begin{aligned}
\|f\|^2
&=\frac{\beta}{\beta+t^2}\left(A_t^2+B_t^2+\frac{t^2}{\beta}\right)\\
&=\frac{a\beta+(1-2a\beta)t^2}{\beta+t^2}
 =a+\frac{\beta(2\beta-1)t^2}{\beta+t^2},
\end{aligned}
$$

proving (R.90). The tilted difference has a nonzero $0$–$1$ component for $t>0$, whereas every $X(u,\varphi)$ in Definition 18.1 has only plane–$2$ coherences. Hence this witness lies outside that restricted family of differences.

Reuse the same-recovery contraction argument of Theorems 4.3 and 14.2. It also applies to any orthogonal-support density matrices $\rho,\sigma$. For a single arbitrary complex CPTP recovery $R:M_5\to M_3$, put $d_R=\|RN-\mathrm{id}_3\|_\diamond$. Then

$$
\begin{aligned}
2=\|\rho-\sigma\|_1
&\leq\|(\mathrm{id}-RN)(\rho)\|_1
      +\|RN(\rho-\sigma)\|_1
      +\|(\mathrm{id}-RN)(\sigma)\|_1\\
&\leq2d_R+\|N(\rho-\sigma)\|_1,\\
\delta_N&\geq1-\tfrac12\|N(\rho-\sigma)\|_1.
\end{aligned}
\tag{R.95}
$$

The contraction step uses only the Hermitian argument: its positive and negative parts are sent to PSD operators whose traces are preserved, so triangle inequality bounds the output norm by the sum of those traces. Each individual error term is bounded by the unhalved diamond norm. Infimizing the same $R$ proves the last line; no separately optimized recoveries have been combined. Using (R.89) yields

$$
\delta_{N_{\beta,t}}
\geq1-\sqrt{a+\frac{\beta(2\beta-1)t^2}{\beta+t^2}}
\geq1-\sqrt a=U(\beta).
\tag{R.96}
$$

For $0<\beta<1/2$ and $t>0$ the first lower bound is strictly greater than $U(\beta)$. At $\beta=1/2$ it equals $U(\beta)$; this establishes no equality for the encoder's optimum. Product inputs are legitimate lower witnesses in the original diamond norm with all finite references, and impose no restriction on its supremum. $\square$

**Corollary 20.2 (method refutation with the original target retained).** For every positive beta the actual family (R.75) has $\mu_N(u,\varphi)>\sqrt a$ for every restricted complex $u,\varphi$, yet has $\delta_N\geq U(\beta)$ by its actual tilted pair. Thus the universal restricted-third-direction method in Definition 18.1 fails throughout $0<\beta\leq1/2$. The threshold consequence $\mu_N(u,\varphi)>\sqrt a$ of (R.74) is not sufficient for improvement. This is consistent with Theorem 17.1, which stated it only as necessary. The family is excluded from improvement of the original sharp curve; it is not a counterexample to that curve.

**Proof.** Combine the exact attained minimum (R.81) with (R.96). The strict minimum includes all complex directions, while the exclusion uses the different pure inputs (R.89) of this same encoder. Returning to physical coordinates uses exactly $L\psi_\pm$ as the witness pair and $R^{\rm ph}=\operatorname{Ad}_L\circ R\circ\operatorname{Ad}_{D^\dagger}$. Equation (P.16) transports the full complex recovery domain and full-reference diamond norm bijectively, so the physical encoder obeys the same lower bound. This transport leaves the native candidate inputs $\theta_\pm$ and their passive sign reflection unchanged. $\square$

## 21. Additional Kraus terms and the remaining unreferenced directions

**Definition 21.1 (boundary of the consumed factorization).** Equation (R.92) used exactly two actual real Kraus matrices and a real orthogonal pair. If a channel has additional Kraus matrices and the same relation $\lambda K_0u+\eta K_1v=0$, the expansion instead reads

$$
\begin{aligned}
N(uv^T+vu^T)
&=xy^T+yx^T+\sum_{\gamma\geq2}
 \left[(K_\gamma u)(K_\gamma v)^T+(K_\gamma v)(K_\gamma u)^T\right],\\
x^Ty&=-\sum_{\gamma\geq2}(K_\gamma u)^T(K_\gamma v).
\end{aligned}
\tag{R.97}
$$

Indeed the relation combines only the first two summands, and TP makes the sum of all column inner products $u^Tv=0$. The residual therefore also supplies the trace cancellation: the isolated two-term part need not be traceless. Complementary Choi rank at most five neither removes this residual nor bounds its trace norm. The encoder rank two in Theorem 18.2 is a property of that family, not a consequence of the complementary rank bound for the whole class. A full-class kernel route still needs a bound on every remaining contribution in the same actual output, or a different uniform certificate. The all-third-column domain and rank-nine real compression in Theorem 1.3 are retained.

The family above needs no reference entanglement for its exclusion, since (R.89) is already an orthogonal pure pair. For the whole original class, neither a useful unrestricted orthogonal pure pair for every encoder nor the necessity of reference entanglement has been established. There is a separate mixed-state route before adding a reference. In this particular qutrit domain, take a nonzero traceless Hermitian input $X$. Its Jordan parts $X_+,X_-$ have disjoint supports and the same trace $c=\|X\|_1/2>0$, so $X=c(\rho-\sigma)$ with $\rho\sigma=0$. Their ranks sum to at most three, so after changing the sign of $X$ if needed, one state is pure and the other has rank at most two. Spectral decomposition supplies exactly

$$
\rho=|v\rangle\langle v|,\qquad
\sigma=p|w_1\rangle\langle w_1|+(1-p)|w_2\rangle\langle w_2|,
\qquad 0\leq p\leq1,
\tag{R.98}
$$

where $v,w_1,w_2$ are orthonormal; a zero-weight direction can be completed arbitrarily. Consequently the minimum of $\|N(X)\|_1/\|X\|_1$ over all nonzero traceless Hermitian qutrit inputs is the minimum of $\|N(\rho-\sigma)\|_1/2$ over these orthogonal-support pairs. Equation (R.95) applies to all of them. This Jordan reduction only delineates the remaining contraction method: it proves neither that mixed inputs are necessary in the original class nor that a reference is necessary or sufficient for its sharp bound. Failure to find a restricted pair, or even an unrestricted pure pair, would not exclude an orthogonal-support mixed witness.

## 22. Mathematical attribution and the unresolved original problem

**Definition 22.1 (model-specific content and reused ingredients).** The fixed physical/passive correspondence, arbitrary complex recovery domain and finite-reference convention are those of (P.1)–(P.6) and (P.16). The attained upper-family optimum at $t=0$ is already (P.11)–(P.16), with its matched fidelity certificate in Theorem 8.1. Complementary Choi support and rank accounting reuse (R.2)–(R.5); the same-recovery trace-distance obstruction is already in Theorems 4.3, 14.2 and 17.1. The exact-recovery interfaces remain owned by [FiniteKrausReversibility](../../../Blueprint/D5/S3/Quantum/Recovery/FiniteKrausReversibility.md) and [OrthogonalSyndromeChannel](../../../Blueprint/D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel.md); they do not supply the positive-error continuum minimum here.

The new model-specific composition is the forward actual family (R.75), its coupled blocks and distinct encoder/complement ranks (R.78)–(R.80), the all-complex exact minimum with attainment (R.81)–(R.88), and the same-kernel tilted exclusion (R.89)–(R.96). The reflection pinching, two-dimensional spectral calculations, Gram rank facts, real two-Kraus expansion and qutrit Jordan decomposition are standard finite-dimensional matrix ingredients used inside those proofs and their explicit method boundary. They are not asserted as new general theorems. The standard channel and norm interfaces retain the attribution in Definitions 10.1 and 17.2; these calculations require no additional literature theorem. No global novelty or kernel-verification assertion is attached to this composition.

**Definition 22.2 (sharp target and resource boundary).** For $0<\beta\leq1/2$, the original full-class task remains to prove $\delta_N\geq U(\beta)$ for every actual original real-Kraus encoder, or to give an actual encoder and one arbitrary complex CPTP recovery with a rigorous full-reference unhalved diamond upper certificate strictly below $U(\beta)$. Together with the existing upper family, the former would give $\delta^*_{\mathcal R}(\beta)=U(\beta)$. Equations (R.81) and (R.96) settle only the restricted method and the displayed same-channel exclusion. They supply neither the uniform lower proof nor an improving recovery. The larger complex-class optimization remains separate. At half beta only a lower bound is asserted for the new encoder's optimum; at beta zero the existing isometry already gives class optimum zero.

Every physical application still requires the actual source encoder and supplied inputs, common source-fiber membership, finite-history transport and joint legality of the native words in the phase-gain volume. The coordinate matrices, the pinching reflection and the tilted mathematical test states provide no native gate, input preparation, encoder/decoder apparatus or hardware resource. The standard matrix arguments and their source exposition are ordinary conditional mathematics, with no physical-realization or broader-programme conclusion.

## 追加锚（本行以下为增补区）

## 23. Common-Gram comparison and exact restricted witness transport

**Definition 23.1 (one original Kraus list and its output blocks).** Retain Definition 1.1, the physical/passive correspondence (P.1)–(P.2), and the full complex recovery and finite-reference conventions (P.6), (P.16). Fix $0<\beta\leq1/2$, $a=1-\beta$, and any finite original real Kraus list from (R.8)–(R.9), of length $n$. In the real output frame $(b_1,g_1,b_2,g_2,h)$ extend $J$ by $Jh=0$. Thus $J^T=-J$ and $J^2=-I$ on the active four-space $U=h^\perp$. Define, from this same list,

$$
\begin{gathered}
A=[x_\alpha]\in M_{5\times n}(\mathbb R),\qquad
T=[t_\alpha]\in M_{5\times n}(\mathbb R),\\
B=AA^T,\qquad C_{\rm out}=AT^T,\qquad D=TT^T,\qquad
Q=\operatorname{diag}(a,a,\beta,\beta,0).
\end{gathered}
\tag{R.99}
$$

Here $C_{\rm out}$ is an output-space matrix; it is not the complementary environment block $C$ of (R.3), (R.79). The $D$ in (R.99) is the actual output $N(E_{22})$, not the physical coordinate matrix of (P.1). The positive matrix $D_\perp$ below is an index-space projection residual and is not the complementary Schur residual $S$ of (R.4), (R.80). No Kraus terms or third-column components are omitted in these definitions.

**Theorem 23.2 (common-index residual and the full complex restricted action).** For the data in Definition 23.1,

$$
\begin{gathered}
B\succeq0,\quad Bh=0,\quad B+JBJ^T=Q,\quad
\operatorname{Tr}B=\operatorname{Tr}D=1,\\
\operatorname{Tr}C_{\rm out}=\operatorname{Tr}(JC_{\rm out})=0,\qquad
0\preceq B\preceq Q\preceq aI_5,\qquad
2\leq k:=\operatorname{rank}B\leq4.
\end{gathered}
\tag{R.100}
$$

The Moore–Penrose inverse $B^+$ is taken on the actual support, including singular $B$. The matrix $P_A=A^TB^+A$ is the orthogonal projection onto $\operatorname{ran}(A^T)$ in the original real Kraus-index space. In particular,

$$
\begin{gathered}
AP_A=A,\qquad \operatorname{ran}C_{\rm out}\subseteq\operatorname{ran}B,\\
D=C_{\rm out}^TB^+C_{\rm out}+D_\perp,\qquad
D_\perp=T(I-P_A)T^T\succeq0,\\
q:=\operatorname{Tr}(C_{\rm out}^TB^+C_{\rm out})
 =\|TP_A\|_F^2\in[0,1],\qquad
\operatorname{Tr}D_\perp=1-q.
\end{gathered}
\tag{R.101}
$$

Use the real seven-dimensional space and its associated minima

$$
\begin{gathered}
\mathcal H_0=\{X=X^\dagger:\operatorname{Tr}X=0,\ X_{22}=0\}
 =\left\{\begin{pmatrix}
\eta&z&w\\ \bar z&-\eta&v\\ \bar w&\bar v&0
\end{pmatrix}:\eta\in\mathbb R,\ z,w,v\in\mathbb C\right\},\\
m_0(N)=\min_{0\ne X\in\mathcal H_0}\frac{\|N(X)\|_1}{\|X\|_1},\qquad
m_{\min}(N)=\min_{\substack{0\ne X=X^\dagger\\\operatorname{Tr}X=0}}
\frac{\|N(X)\|_1}{\|X\|_1}.
\end{gathered}
\tag{R.102}
$$

Both minima exist by normalizing to the compact unit sphere in the indicated real vector space. In particular $m_{\min}(N)\leq m_0(N)$. All complex coordinates $z,w,v$ are retained. The nine original matrix-unit images are

$$
\left[N(E_{ij})\right]_{i,j=0}^2
=\begin{pmatrix}
B&BJ^T&C_{\rm out}\\
JB&JBJ^T&JC_{\rm out}\\
C_{\rm out}^T&C_{\rm out}^TJ^T&D
\end{pmatrix},
\qquad E_{ij}=|i\rangle\langle j|.
\tag{R.103}
$$

Consequently, on precisely $\mathcal H_0$, the channel action is

$$
\begin{aligned}
\mathcal L_{B,C_{\rm out}}(X)
={}&\eta(B-JBJ^T)+zBJ^T+\bar zJB\\
&+wC_{\rm out}+\bar wC_{\rm out}^T
 +vJC_{\rm out}+\bar vC_{\rm out}^TJ^T
=N(X).
\end{aligned}
\tag{R.104}
$$

The following estimates are ingredients for reducing this same-channel witness problem:

$$
\begin{gathered}
c_{\rm pl}:=\tfrac12\|B-JBJ^T\|_1=\|ZZ^T\|_1,\\
m_{\min}(N)\leq m_0(N)
\leq\min\{c_{\rm pl},\|C_{\rm out}\|_1\}
\leq\min\{c_{\rm pl},\sqrt q\}.
\end{gathered}
\tag{R.105}
$$

Thus $c_{\rm pl}\leq\sqrt a$ or $q\leq a$ already gives an $\mathcal H_0$ witness at most $\sqrt a$. The same conclusion holds when $\operatorname{rank}C_{\rm out}\leq1$.

**Proof.** The phase relation (R.8) gives $B+JBJ^T=Q$ and $Bh=0$. The first two column norms are equal because $J$ is an isometry on $U$; tracing the phase identity gives $\operatorname{Tr}B=1$. Equation (R.9) gives $\operatorname{Tr}D=1$ and exactly the two displayed cross traces. Positivity gives $B\preceq Q$, and $a\geq\beta$ gives $Q\preceq aI_5$. Since $Q$ has rank four, $4\leq2\operatorname{rank}B$, while $Bh=0$ gives the upper rank bound. No nondegeneracy of $a-\beta$ is used, so $\beta=1/2$ is included.

Take a real thin singular-value decomposition $A=U_A\Sigma V_A^T$, with $k$ positive singular values. Then $B^+=U_A\Sigma^{-2}U_A^T$ on its support and $P_A=V_AV_A^T$. This proves the projection and support assertions even when $B$ is singular. Orthogonal splitting of $T=TP_A+T(I-P_A)$ gives

$$
\begin{aligned}
C_{\rm out}^TB^+C_{\rm out}
 &=TA^TB^+AT^T=TP_AT^T=(TP_A)(TP_A)^T,\\
TT^T&=(TP_A)(TP_A)^T+
       [T(I-P_A)][T(I-P_A)]^T.
\end{aligned}
$$

Tracing proves (R.101). In particular $\operatorname{rank}D_\perp\leq\min(5,n-k)$, with no rank-one restriction. The original Kraus Choi rank is the rank of the stacked real matrix $(A;JA;T)$. Its row space is the orthogonal sum of $\operatorname{ran}(A^T)$ and the row space of $T(I-P_A)$: the rows of $JA$ and $TP_A$ already lie in the former. Thus the original rank is $k+\operatorname{rank}D_\perp\leq9$, consistent with Theorem 1.3, rather than bounded by four. At $q=0$, $TP_A=0$ and $C_{\rm out}=0$; at $q=1$, $D_\perp=0$ and $T=TP_A$. These are exact endpoint statements.

Each entry of (R.103) follows by expanding the original Kraus sum on $E_{ij}$; substitution gives (R.104). On a general input the third diagonal contribution is $X_{22}D$, including $X_{22}D_\perp$. It vanishes in (R.104) because $X_{22}=0$, not because the original channel lacks a residual. The real dimension in (R.102) is $1+2+2+2=7$.

For (R.105), $E_{00}-E_{11}$ has trace norm two. In the complex phase frame $(f_1^+,f_2^+,f_1^-,f_2^-,h)$ of (R.7), its output has off-diagonal block $ZZ^T$ and the adjoint block, with zero diagonal blocks. The singular values are therefore doubled, proving the expression for $c_{\rm pl}$. This is exactly the $0$-versus-$1$ distance already used in Theorem 4.3, so $c_{\rm pl}=f(\tau,\bar\tau)$ in the owning complementary notation; no additional plane certificate is being assumed.

The input $E_{02}+E_{20}\in\mathcal H_0$ also has trace norm two and output $C_{\rm out}+C_{\rm out}^T$. Triangle inequality bounds its ratio by $\|C_{\rm out}\|_1$. The common factorization $C_{\rm out}=A(TP_A)^T$ and Schatten Hölder give

$$
\|C_{\rm out}\|_1\leq\|A\|_F\|TP_A\|_F=\sqrt q,
\qquad
\|C_{\rm out}\|_F^2\leq\|A\|_{\rm op}^2\|TP_A\|_F^2\leq aq.
$$

When $\operatorname{rank}C_{\rm out}\leq1$, its trace and Frobenius norms agree, giving $\|C_{\rm out}\|_1\leq\sqrt{aq}\leq\sqrt a$. These standard norm steps are used only inside the common-Gram reduction. The condition $q\leq a$ is equivalent to $\operatorname{Tr}D_\perp\geq\beta$ and is not a condition on $\operatorname{Tr}S$. At $q=0$, the displayed cross input is a nonzero zero-output witness, so $m_0(N)=m_{\min}(N)=0$ without any normalization. $\square$

**Theorem 23.3 (actual normalized comparison and exact feasible realization).** For $q>0$ put $r=\sqrt q$ and form, from every term of the original list,

$$
K_\alpha^\sharp=
\left(x_\alpha,Jx_\alpha,\frac{(TP_A)_\alpha}{r}\right),\qquad
N^\sharp(X)=\sum_\alpha K_\alpha^\sharp X(K_\alpha^\sharp)^T.
\tag{R.106}
$$

This is an actual real-Kraus CPTP encoder in the same phase class, with

$$
\begin{gathered}
B^\sharp=B,\qquad C_{\rm out}^\sharp=C_{\rm out}/r,\qquad
D^\sharp=C_{\rm out}^TB^+C_{\rm out}/q,\\
q^\sharp=1,\qquad D_\perp^\sharp=0.
\end{gathered}
\tag{R.107}
$$

It admits at most $k=\operatorname{rank}B\leq4$ real Kraus matrices for the entire channel on all complex inputs. This bound belongs to $N^\sharp$. At $q=1$ the original and comparison channels coincide; no such identity or original rank bound is asserted when $q<1$.

The normalized comparison domain has the following exact constructive description. For fixed $\beta,J,h,Q$ as above, a real pair $(B,C_{\rm out})$ is feasible if and only if

$$
\begin{gathered}
B=B^T\succeq0,\qquad Bh=0,\qquad B+JBJ^T=Q,\\
\operatorname{ran}C_{\rm out}\subseteq\operatorname{ran}B,\qquad
\operatorname{Tr}C_{\rm out}=\operatorname{Tr}(JC_{\rm out})=0,\\
\operatorname{Tr}(C_{\rm out}^TB^+C_{\rm out})=1.
\end{gathered}
\tag{R.108}
$$

Here feasibility means realization by one actual channel of the form (R.106) with $q=1$, rather than separate positivity conditions on unrelated blocks. In the reverse direction, choose a real full-column-rank factor with $k$ columns and set

$$
AA^T=B,\qquad T=C_{\rm out}^TB^+A,\qquad
K_\alpha=(A_\alpha,JA_\alpha,T_\alpha).
\tag{R.109}
$$

These matrices supply the required common realization.

**Proof.** The first two columns of (R.106) retain their original summed norms one and their skew inner product zero. The third summed squared norm is $\|TP_A\|_F^2/r^2=1$. Since $AP_A=A$ and $(JA)P_A=JA$, the two summed cross inner products with $TP_A$ equal those with $T$ and hence vanish. Division by $r$ preserves their zero values. This proves every TP entry; the actual Kraus sum proves CP on the complex matrix algebra. Its first two columns are unchanged, so both actual phase outputs and their spectra are unchanged. Multiplying the blocks proves (R.107).

All three rows of column maps $A,JA,TP_A/r$ vanish on $\ker P_A$. Choose a real $n\times k$ matrix $W$ with orthonormal columns spanning $\operatorname{ran}P_A$, so $WW^T=P_A$. Define $\widehat K_j=\sum_\alpha W_{\alpha j}K_\alpha^\sharp$. Expanding their Kraus sum replaces the index contraction $I_n$ by $WW^T=P_A$; the omitted index directions have all three output columns zero. Thus $\sum_j\widehat K_jX\widehat K_j^T=N^\sharp(X)$ for every complex $X$. Tensoring this identity with any finite reference preserves it. This proves the comparison rank bound without truncating an original channel. When $q=1$, (R.101) gives $T=TP_A$ and $r=1$, proving the endpoint identity.

Necessity of (R.108) follows from (R.100)–(R.101). For sufficiency, spectral factorization gives the real factor $A$ in (R.109). Its columns lie in $h^\perp$ by $Bh=0$. The range condition gives $BB^+C_{\rm out}=C_{\rm out}$, hence

$$
AT^T=BB^+C_{\rm out}=C_{\rm out},\qquad
TT^T=C_{\rm out}^TB^+BB^+C_{\rm out}
     =C_{\rm out}^TB^+C_{\rm out}.
$$

Trace of the phase identity gives $\operatorname{Tr}B=1$, because $J$ is an isometry on $h^\perp$. The two first-column norms, their skew inner product, the two cross traces in (R.108), and the final trace one in (R.108) now give precisely $\sum_\alpha K_\alpha^TK_\alpha=I_3$. In particular the normalization is an actual TP condition, not an independent assignment of a third block. The joint Gram matrix is

$$
\begin{pmatrix}
B&C_{\rm out}\\ C_{\rm out}^T&C_{\rm out}^TB^+C_{\rm out}
\end{pmatrix}
=\begin{pmatrix}A\\T\end{pmatrix}
 \begin{pmatrix}A\\T\end{pmatrix}^{T}\succeq0,
$$

of rank $k$, also for singular $B$. Since $JQ=JB-BJ^T$ on the active space, direct expansion gives $N(\chi_\pm)=(Q\pm iJQ)/2$. In the frame (R.7) these are the orthogonal-support states with nonzero spectra $(a,\beta)$, including $a=\beta=1/2$. This proves membership in the actual original real phase class. The full-column-rank factor gives $P_A=I_k$ and hence $q=1$, as required. The support, phase, $Bh=0$, trace and normalization conditions in (R.108) are all used; omitting them does not license this realization. $\square$

**Theorem 23.4 (exact inverse-damping transport on $\mathcal H_0$).** For $q>0$ and the actual comparison of Theorem 23.3, define the input map, in the original $0,1$ versus $2$ splitting,

$$
\begin{gathered}
F=\operatorname{diag}(1,1,-1),\qquad
\Gamma_r=\frac{1+r}{2}\,\mathrm{id}_3+
          \frac{1-r}{2}\operatorname{Ad}_F,\\
\Gamma_r\begin{pmatrix}H&\xi\\\xi^\dagger&d\end{pmatrix}
=\begin{pmatrix}H&r\xi\\r\xi^\dagger&d\end{pmatrix}.
\end{gathered}
\tag{R.110}
$$

The map is CPTP for $0\leq r\leq1$. On $\mathcal H_0$ exactly, $N(Y)=N^\sharp(\Gamma_r(Y))$. For any nonzero comparison witness in that space, set

$$
X^\sharp=\begin{pmatrix}H&\xi\\\xi^\dagger&0\end{pmatrix},\qquad
Y=\begin{pmatrix}H&\xi/r\\\xi^\dagger/r&0\end{pmatrix}.
\quad
\begin{gathered}
N(Y)=N^\sharp(X^\sharp),\qquad
\|X^\sharp\|_1\leq\|Y\|_1,\\
m_{\min}(N)\leq m_0(N)\leq m_0(N^\sharp).
\end{gathered}
\tag{R.111}
$$

The inverse construction is a Hermitian test-operator construction, with no assertion of a CP state-preparation map. For a general complex matrix $Y$, the full discrepancy is

$$
N(Y)-N^\sharp(\Gamma_r(Y))
=Y_{22}(D-D^\sharp)
=Y_{22}\,[D_\perp-(1-q)D^\sharp].
\tag{R.112}
$$

**Proof.** Both coefficients in (R.110) are nonnegative and sum to one, so this is a convex mixture of two unitary channels. Triangle inequality and unitary invariance give $\|\Gamma_r(Y)\|_1\leq\|Y\|_1$ for every matrix $Y$. Equations (R.103), (R.107) show that damping precisely cancels the factor $1/r$ in every plane–third cross image, including its complex conjugate. The plane block is unchanged. The only remaining difference is the $22$ image, proving (R.112) and the claimed equality when $Y_{22}=0$.

For the specified inverse, $Y\in\mathcal H_0$, $Y\ne0$, and $\Gamma_r(Y)=X^\sharp$. Norm contraction therefore gives the first two identities of (R.111) and

$$
\frac{\|N(Y)\|_1}{\|Y\|_1}
\leq\frac{\|N^\sharp(X^\sharp)\|_1}{\|X^\sharp\|_1}.
$$

Minimize over the comparison witnesses to obtain (R.111). The inverse need not preserve positivity and is not used as a physical preprocessing operation. An unrestricted witness for $m_{\min}(N^\sharp)$ cannot replace $X^\sharp$ here unless it also satisfies $X^\sharp_{22}=0$; (R.112) identifies the missing term. No division by $q$ is used at $q=0$, which was already settled by Theorem 23.2. $\square$

**Assumption 23.5 (sufficient lemma G, unproved).** For every $0<\beta\leq1/2$, $a=1-\beta$, and every real pair $(B,C_{\rm out})$ satisfying all of (R.108), there exists a nonzero complex Hermitian $X\in\mathcal H_0$ such that

$$
\|\mathcal L_{B,C_{\rm out}}(X)\|_1
\leq\sqrt a\,\|X\|_1.
\tag{R.113}
$$

No proof or counterexample to G is supplied. Theorem 23.2 already treats the part with $c_{\rm pl}\leq\sqrt a$ or $\operatorname{rank}C_{\rm out}\leq1$. Thus the remaining part of G has $c_{\rm pl}>\sqrt a$, $\operatorname{rank}C_{\rm out}\geq2$ and $\operatorname{rank}B\in\{2,3,4\}$. None of these three possible ranks of $B$ is discarded. The original unnormalized branch $q\leq a$ is another settled ingredient, whereas the domain of G itself has $q=1$.

**Theorem 23.6 (conditional implication for the unchanged sharp target).** If G holds, every actual original real-Kraus encoder in Definition 1.1 at positive beta satisfies

$$
m_{\min}(N)\leq\sqrt a,\qquad
\delta_N\geq1-\sqrt a=U(\beta),\qquad
\delta^*_{\mathcal R}(\beta)=U(\beta).
\tag{R.114}
$$

These consequences include arbitrary complex inputs and recoveries on the whole output and all finite complex references in the original unhalved diamond convention. Failure of G would refute this sufficient seven-dimensional route only; it would not by itself refute the full $m_{\min}$ claim or the original diamond target.

**Proof.** The $q=0$ branch is already a zero-output witness. For every $q>0$, Theorem 23.3 gives one actual comparison whose pair $(B,C_{\rm out}/r)$ satisfies (R.108). G gives $m_0(N^\sharp)\leq\sqrt a$, and Theorem 23.4 transports that restricted witness to the same original channel, proving $m_{\min}(N)\leq m_0(N)\leq\sqrt a$.

Reuse the Jordan domain (R.98): every nonzero traceless Hermitian qutrit input, up to sign and scale, is the difference of one pure state and a density of rank at most two on its orthogonal complement. Applying (R.95) to these actual orthogonal-support states gives $\delta_N\geq1-m_{\min}(N)$. This uses one arbitrary complex CPTP recovery at a time; product lower witnesses are admissible within the full-reference diamond supremum and do not restrict that supremum. Combining with the attained upper family (P.11)–(P.16) proves the conditional class equality. At beta zero the existing isometric family already attains the nonnegative class optimum zero, without extending the positive-beta rank assumptions.

Conversely, failure of G means that one feasible normalized actual channel has no required $\mathcal H_0$ witness. Its minimum over all traceless Hermitian inputs can still be smaller, and its full-reference recovery lower certificate can arise by another method. Thus neither of the broader targets follows negatively from that failure. The original alternative remains an actual original-class encoder and one complex CPTP recovery with a rigorous full-reference diamond upper certificate strictly below $U(\beta)$; no such object is constructed here. $\square$

**Definition 23.7 (overlap, attribution and mathematical boundary).** The repo-derived content is the normalized common-Gram comparison (R.101), (R.106)–(R.109), its exact restricted action and inverse-damping transport (R.104), (R.110)–(R.112), and the resulting conditional route (R.113)–(R.114). The SVD projection, Schatten inequalities, unitary-mixture contraction and Jordan decomposition are standard ingredients inside this composition. The plane exclusion reuses Theorem 4.3, the recovery obstruction reuses (R.95), and the unrestricted pure-versus-rank-two domain remains (R.98); none is an additional standalone general result.

For calibration, the actual family (R.75) has $P_A=I_2$, $q=1$, $D_\perp=0$, $c_{\rm pl}=1$ and $\operatorname{rank}C_{\rm out}=2$. Nevertheless its complementary residual is $S=\operatorname{diag}(s_t^2,0)\ne0$. These statements follow by inserting its two independent first columns into (R.99)–(R.101), and by (R.80). Its already established tilted difference (R.89) has $X_{22}=0$ and is therefore an $\mathcal H_0$ witness. This calibrates the hard normalized region without proving G for arbitrary feasible pairs.

The minimum in (R.102) agrees, by the Jordan argument already in (R.98), with the minimum trace-distance ratio and the orthogonal-support formulation of [G. Chiribella and K. Goswami, *Maximum and minimum causal effects of physical processes*, arXiv:2404.07683v3, Definition 3, (13), PDF p.5; Proposition 6, (14), PDF p.6; Section III.A, (24) and its following paragraph, PDF p.8](https://arxiv.org/pdf/2404.07683v3). The pure-state reduction there is automatic for qubit input. It does not license a pure-versus-pure restriction for this qutrit domain or show that mixed states are necessary in this real class. That source supplies no $\sqrt a$ estimate for G.

The exact-isometry interface is [F. Ticozzi and L. Viola, *Quantum Information Encoding, Protection, and Correction from Trace-Norm Isometries*, arXiv:0912.0963v1, Section II, Definition 1, Lemma 1, (4)–(8), Theorem 1, PDF pp.2–3; Section IV, Definitions 4–5, (16), PDF p.7; DOI 10.1103/PhysRevA.81.032313](https://arxiv.org/pdf/0912.0963v1). Its stochastic-isometry formula (6) permits unitary or antiunitary components. For a complex CPTP channel every nonzero compressed block must be CP; an antiunitary block acts as unitary-conjugated transposition, whose Choi swap has a negative eigenvalue on the antisymmetric subspace. Thus such a block is excluded here. The exact CPTP left-inverse structure is $\rho\mapsto U(\rho\otimes\tau)U^\dagger$ on its support, as also treated by the existing exact-recovery interfaces in Definition 22.1. A rank-two pure output then requires two orthogonal qutrit copies and hence output dimension at least six. This is an exact-recovery obstruction. Definitions 4–5 and (16) assume a perturbation of an actual specified isometry; neither that premise nor the sharp positive-error bound is furnished by the exact dimension count or by a lower trace-distance ratio alone.

These two primary interfaces have only the attributed roles above. The model-specific comparison is repo-derived ordinary finite-dimensional mathematics, with no global novelty, exhaustive literature coverage or kernel-verification assertion. Universal identities rest on the displayed proofs, rather than finite numerical checks. G and the positive-beta all-encoder sharp lower bound remain unproved here. The larger complex encoder class is unchanged and separate. All physical uses still require the actual encoder and supplied inputs, common source-fiber membership, finite-history transport and native-word joint legality of the phase-gain volume. The comparison encoder, inverse damping, coordinate frames and mathematical witnesses supply no native gates, state preparation, physical encoder/decoder apparatus or hardware resources.

## 追加锚（本行以下为增补区）

## 24. Expanded actual rank-two families and the full tilted phase circle

**Definition 24.1 (actual family and inherited domain).** Retain the actual real class, passive frame, arbitrary complex recoveries on the whole output, unhalved norms and all finite references of Definitions 1.1 and 23.1. Write $(e_0,e_1,e_2,e_3,h)=(b_1,g_1,b_2,g_2,h)$, with $Je_0=e_1$, $Je_2=e_3$, $J^T=-J$ and $Jh=0$. Throughout Sections 24–27 take $0<\beta\leq1/2$, $a=1-\beta$. Choose real, possibly signed or zero parameters satisfying

$$
u^2+\frac{v^2}{a}+s_0^2+s_1^2+k^2=1,
\qquad
\begin{aligned}
K_0&=(\sqrt a\,e_0,\sqrt a\,e_1,
       -\sqrt{\beta/a}\,v e_1+s_0e_2+s_1e_3+kh),\\
K_1&=(\sqrt\beta\,e_2,\sqrt\beta\,e_3,u e_0+v e_3).
\end{aligned}
\tag{R.115}
$$

The notation $(x,y,t)$ specifies all three columns. These two matrices define $N(X)=K_0XK_0^T+K_1XK_1^T$ on every complex input. The specialization $u=v=t$, $s_0=s_1=0$ is already owned by (R.75), (R.89)–(R.96); those statements are reused directly. The additional independent coefficients and their phase interference are the subject here.

**Theorem 24.2 (complete phase-circle output and attained minimum).** The matrices (R.115) are an actual TP common realization with

$$
B=\operatorname{diag}(a,0,\beta,0,0),\quad
B+JBJ^T=Q,\quad q=1,\quad
\operatorname{rank}B=2,\quad c_{\rm pl}=1.
\tag{R.116}
$$

For $d=\sqrt{\beta+v^2}>0$, set

$$
\eta=\frac{\sqrt\beta\,|2\rangle-v|1\rangle}{d},\quad
X_\theta=e^{i\theta}|0\rangle\langle\eta|
          +e^{-i\theta}|\eta\rangle\langle0|,
\quad X_+=X_0,\quad X_-=X_{\pi/2}.
\tag{R.117}
$$

Every $X_\theta$ belongs to the full complex Hermitian $\mathcal H_0$ of (R.102), has eigenvalues $1,-1,0$, and has trace norm two. Its exact ratio is

$$
\begin{aligned}
r(\theta)^2
&:=\frac{\|N(X_\theta)\|_1^2}{4}\\
&=\frac{v^2+a\beta(s_0^2+s_1^2+k^2)+\beta^2u^2
       +2\beta\sqrt{a\beta}\,s_0u\cos(2\theta)}{\beta+v^2},\\
r_*^2:=\min_{\theta\in\mathbb R}r(\theta)^2
&=\min\{r(0)^2,r(\pi/2)^2\}\\
&=a-\frac{\beta(a-\beta)u^2+2\beta\sqrt{a\beta}|s_0u|}{\beta+v^2}
\leq a.
\end{aligned}
\tag{R.118}
$$

For $s_0u>0$ choose $X_-$; for $s_0u<0$ choose $X_+$; for $s_0u=0$ either phase attains the minimum. If $s_0u\ne0$, the minimizing phases are exactly those with $\cos(2\theta)=-\operatorname{sign}(s_0u)$. The family therefore has

$$
m_0(N)\leq r_*,\qquad
\delta_N\geq1-r_*\geq1-\sqrt a.
\tag{R.119}
$$

The first inequality is a witness bound, not an assertion that this circle contains a minimizer over all of $\mathcal H_0$.

**Proof.** In the TP sum the first two diagonal entries are $a+\beta=1$, and the $01$ entry vanishes termwise. The $02$ entry is zero. The two contributions to the $12$ entry are $-\sqrt\beta v$ and $+\sqrt\beta v$. The third diagonal entry is $u^2+v^2/a+s_0^2+s_1^2+k^2=1$. Thus the full two-term map is CPTP. Its $A$ in (R.99) has independent columns $\sqrt a e_0,\sqrt\beta e_2$, so $P_A=I_2$, $q=\operatorname{Tr}TT^T=1$, and the displayed $B$ follows. Equation (R.103) gives $N(\chi_\pm)=(Q\pm iJQ)/2$, with orthogonal phase supports and eigenvalues $a,\beta$. This verifies actual class membership rather than just a putative block constraint. The diagonal difference in (R.105) has trace norm two, giving $c_{\rm pl}=1$.

The vectors $|0\rangle,\eta$ are real orthonormal, so the input assertions follow on their two-dimensional span, including when $v=0$. Direct column multiplication, keeping both Kraus terms, gives

$$
K_1\eta=\frac{\sqrt\beta u}{d}e_0,\qquad
g:=\sqrt a K_0\eta=
\frac{-v e_1+\sqrt{a\beta}(s_0e_2+s_1e_3+kh)}d,
\qquad j:=\frac{\beta u}{d}e_2.
$$

Both $g,j$ are orthogonal to $e_0$. Consequently

$$
N(X_\theta)=e^{i\theta}(e_0g^T+je_0^T)
            +e^{-i\theta}(ge_0^T+e_0j^T).
$$

This Hermitian matrix has only an $e_0$-to-$e_0^\perp$ block and its adjoint. Its nonzero eigenvalues are $\pm\|e^{i\theta}g+e^{-i\theta}j\|_2$; the formula remains valid if the vector is zero. Squaring the vector norm uses $g^Tj=\beta\sqrt{a\beta}s_0u/d^2$ and proves the first line of (R.118). In particular

$$
\begin{gathered}
w_\pm=\frac{-v e_1+(\sqrt{a\beta}s_0\pm\beta u)e_2
                         +\sqrt{a\beta}s_1e_3+\sqrt{a\beta}kh}{d},\\
N(X_+)=e_0w_+^T+w_+e_0^T,\qquad
N(X_-)=i(e_0w_-^T-w_-e_0^T).
\end{gathered}
$$

Minimizing the cosine chooses the sign stated. Subtracting the phase-independent numerator from $a(\beta+v^2)$ and using (R.115) gives $\beta(a-\beta)u^2$. This proves the minimum formula without restrictions on any parameter sign. Its nonnegativity also follows from its attained squared-norm expression. The inequality is strict precisely when $\beta(a-\beta)u^2+2\beta\sqrt{a\beta}|s_0u|>0$. This includes $0<\beta<1/2$, $u\ne0$; at half beta it requires $s_0u\ne0$ for this formula. For any phase, $X_\theta$ is the difference of the orthogonal pure states $(e^{i\theta}|0\rangle\pm\eta)/\sqrt2$. Apply the existing same-recovery estimate (R.95) to the minimizing phase. It already permits every complex CPTP recovery and the full finite-reference unhalved diamond norm, proving (R.119). $\square$

**Proposition 24.3 (phase discrimination and the exact extra frame conditions).** At $a=\beta=1/2$, $v=s_1=k=0$, $u=s_0=1/\sqrt2$, the ratios of $X_+$ and $X_-$ are respectively one and zero. Replacing $s_0$ by $-s_0$ exchanges them. Thus the real phase alone cannot replace the circle minimum in Theorem 24.2.

In a canonical first-column frame $x_0=\sqrt a e_0$, $x_1=\sqrt\beta e_2$, write the two plane projections of the third column $t_1$ as $r_A=(t_{1,0},t_{1,1})$, $r_B=(t_{1,2},t_{1,3})$. The common $SO(2)$ rotation of these two coordinate pairs puts $t_1$ in the form $u e_0+v e_3$ if and only if

$$
\langle h,t_1\rangle=0,\qquad r_A\cdot r_B=0.
\tag{R.120}
$$

Here a common output-plane rotation may be accompanied by the inverse input $01$-plane rotation to retain the displayed canonical first two columns. The criterion is for this specified frame freedom; it is not a classification under every possible parameter-dependent change of representation. Once this form of $t_1$ is obtained, TP forces $t_{0,0}=0$ and $t_{0,1}=-\sqrt{\beta/a}v$, leaving exactly the other coefficients in (R.115). The two conditions (R.120) are additional hypotheses, not consequences of TP.

**Proof.** The first assertions follow from the explicit $w_\pm$. A common planar rotation preserves $r_A\cdot r_B$ and the $h$ component. If $r_A\ne0$, align it with the first axis; orthogonality puts $r_B$ on the second axis. If $r_A=0$ but $r_B\ne0$, align $r_B$ with the second axis. If both vanish nothing needs alignment. Signed $u,v$ include all orientations and zero projections. The $02$ TP equation becomes $\sqrt a t_{0,0}=0$; the $12$ equation becomes $\sqrt a t_{0,1}+\sqrt\beta v=0$. The remaining third-column norm is precisely (R.115). These equations impose neither condition on an arbitrary initial $t_1$. $\square$

**Proposition 24.4 (when $B$ is canonical and actual instances outside the family).** For $a\ne\beta$, the additional condition $[B,Q]=0$ is sufficient to put any feasible rank-two $B$ of (R.108) in the canonical form (R.116) by $J$-preserving orthogonal plane frames. At $a=\beta=1/2$, every feasible rank-two $B$ has a $J$-preserving canonical frame. Neither assertion supplies (R.120).

There are also actual noncanonical rank-two examples in the region $c_{\rm pl}>\sqrt a$. An exact one is obtained with $\beta=1/5$, $a=4/5$, $t=1/5$, $c=2\sqrt6/5$, and

$$
\begin{gathered}
x_0=\sqrt a c e_0-\sqrt\beta t e_3,\qquad
x_1=-\sqrt a t e_1+\sqrt\beta c e_2,\\
t_0=h/\sqrt2,\qquad
t_1=\frac{\sqrt\beta c e_0-\sqrt a t e_3}
                {\sqrt{2(\beta c^2+a t^2)}},\qquad
K_j=(x_j,Jx_j,t_j)\quad(j=0,1).
\end{gathered}
\tag{R.121}
$$

It has $q=1$, $\operatorname{rank}B=\operatorname{rank}C_{\rm out}=2$, $[B,Q]\ne0$, and

$$
\begin{gathered}
\operatorname{spec}_{>0}B=(97/125,28/125)\ne(a,\beta),\\
c_{\rm pl}^2=1-(a-\beta)^2(2ct)^2
             =\frac{14761}{15625}>
               \frac{12500}{15625}=a.
\end{gathered}
\tag{R.122}
$$

Canonical $B$ also allows third columns outside (R.120). For any positive beta, $t_0=e_2/\sqrt2$, $t_1=h/\sqrt2$ is actual with a forbidden $h$ component. At $\beta=1/5$, the alternative

$$
t_1=(e_0+e_2)/2,\qquad
t_0=-\tfrac12\sqrt{\beta/a}\,e_0
       +\sqrt{\tfrac12-\tfrac{\beta}{4a}}\,h
$$

is actual with $r_A\cdot r_B=1/4$. Both have $q=1$, $c_{\rm pl}=1$ and $\operatorname{rank}C_{\rm out}=2$. These instances show missing hypotheses in a proposed exhaustive use of (R.115); they assert no impossibility of finding other witnesses.

**Proof.** If $[B,Q]=0$ and $a\ne\beta$, $B$ splits over the two distinct two-dimensional eigenspaces of $Q$. The identity $B+JBJ^T=Q$ gives block traces $a,\beta$. Both blocks are nonzero PSD, so total rank two makes each rank one. Rotating an eigenvector within each oriented $J$ plane makes the two blocks $\operatorname{diag}(a,0)$ and $\operatorname{diag}(\beta,0)$. At half beta, $B\preceq aI$ on $U$, $\operatorname{Tr}B=2a$ and rank two force both positive eigenvalues to be $a$. Thus $B=aP_L$, where $L$ has dimension two, and $JP_LJ^T=I_U-P_L$. In particular $JL=L^\perp$; an orthonormal basis of $L$ followed by its $J$ images gives the claimed canonical frame. Third columns have not entered either argument.

For (R.121), the summed first-column norm is $a+\beta=1$, and $x_j^TJx_j=0$. The two $02$ products vanish. The only possible nonzero $12$ product is $(Jx_1)^Tt_1$, whose two terms $\sqrt{a\beta}tc$ cancel. The third-column squared norms are $1/2,1/2$. Thus TP holds. The complex phase coefficients in (R.8) can be taken as the rows $(\sqrt a c,i\sqrt a t)$ and $(i\sqrt\beta t,\sqrt\beta c)$; their Hermitian cross product is zero and their squared norms are $a,\beta$. Hence this is an actual original-class channel. Both $A$ and $T$ have independent columns, giving the stated ranks and $q=1$.

The two $x$ vectors have disjoint coordinate supports; their squared lengths are $ac^2+\beta t^2$ and $at^2+\beta c^2$, giving (R.122)'s spectrum. The $03$ entry of $B$ is $-\sqrt{a\beta}ct\ne0$, while those two $Q$ entries differ, so the commutator is nonzero. In the $(e_0,e_3)$ block, $B-JBJ^T$ has diagonal entries $a(c^2-t^2),-\beta(c^2-t^2)$ and off-diagonal entry $-2\sqrt{a\beta}ct$. Its determinant is $-a\beta$ and its trace is $(a-\beta)(c^2-t^2)$. The other block has the opposite eigenvalues. Thus the half trace norm squared is $(a-\beta)^2(c^2-t^2)^2+4a\beta=1-(a-\beta)^2(2ct)^2$, proving the exact strict inequality.

For the two canonical counterinstances, use the first two columns of (R.115) and the specified third columns. Their two summed cross inner products vanish: in the second instance the $02$ terms are $-\sqrt\beta/2$ and $+\sqrt\beta/2$. Their total third squared norms are one. The third columns are independent, so the full-column-rank $A$ again gives $q=1$ and rank two for $C_{\rm out}$. The $h$ component and dot product are exactly those stated. $\square$

## 25. Three actual Kraus terms and one shared tilted input

**Theorem 25.1 (full rank-three output, exact norm and endpoints).** Let $u,v,k$ be real with $u^2+v^2/a+k^2=1$, and $0\leq p\leq1$. Use all three terms

$$
\begin{aligned}
K_0&=(\sqrt a e_0,\sqrt a e_1,-\sqrt{\beta/a}v e_1+kh),\\
K_1&=\sqrt p(\sqrt\beta e_2,\sqrt\beta e_3,u e_0+v e_3),\\
K_2&=\sqrt{1-p}(\sqrt\beta e_3,-\sqrt\beta e_2,u e_0-v e_2).
\end{aligned}
\tag{R.123}
$$

This is an actual real-Kraus CPTP channel. For $0<p<1$,

$$
B=\operatorname{diag}(a,0,\beta p,\beta(1-p),0),\quad
q=1,\quad \operatorname{rank}B=3,\quad
c_{\rm pl}=a+\beta|2p-1|.
\tag{R.124}
$$

In this interior range $\operatorname{rank}C_{\rm out}=3$ if and only if $v\ne0$; in particular $k\ne0$ is not necessary. For the identical $\eta,X_+$ of (R.117),

$$
\begin{gathered}
N(X_+)=e_0w_p^T+w_pe_0^T,\qquad
w_p=\frac{-v e_1+\beta u[pe_2+(1-p)e_3]+\sqrt{a\beta}kh}
                    {\sqrt{\beta+v^2}},\\
\frac{\|N(X_+)\|_1^2}{4}
=\|w_p\|^2
=\frac{v^2+\beta^2u^2[p^2+(1-p)^2]+a\beta k^2}{\beta+v^2}\\
=a-\frac{\beta[(a-\beta)+2\beta p(1-p)]u^2}{\beta+v^2}
\leq a.
\end{gathered}
\tag{R.125}
$$

Consequently (R.95) gives $\delta_N\geq1-\|w_p\|\geq1-\sqrt a$. All formulas have their stated values at $p=0,1$, where $\operatorname{rank}B=2$ instead of three. In the interior, this actual family lies in $c_{\rm pl}>\sqrt a$ exactly when

$$
|2p-1|>\frac{\sqrt a}{1+\sqrt a}.
\tag{R.126}
$$

At half beta, interior $p$ and $u\ne0$, (R.125) is strictly below $a$. Thus the complete third term supplies a strict witness also at that endpoint.

**Proof.** The first two summed column norms are one and their inner product is zero. The $02$ products vanish. The $12$ contributions are $-\sqrt\beta v$, $p\sqrt\beta v$ and $(1-p)\sqrt\beta v$. Their full sum is zero. The third summed squared norm is $\beta v^2/a+k^2+u^2+v^2=1$. This proves TP with no discarded term. The first columns give (R.124); $B+JBJ^T=Q$ gives the required actual phase outputs by (R.103). For interior $p$ these three first columns are independent, so $P_A=I_3$ and $q=1$. Their independence also implies $\operatorname{rank}C_{\rm out}=\operatorname{rank}T$. If $v\ne0$, the $e_3$ and $e_2$ coordinates distinguish $t_1,t_2$, while the nonzero $e_1$ coordinate of $t_0$ is outside their span. Thus rank $T$ is three even when $k=0$ or $u=0$. If $v=0$, the last two third columns are parallel to $e_0$ and the first is parallel to $h$, so rank is at most two. At $p=0,1$ there are only two nonzero first columns, giving the endpoint rank assertion.

Directly $K_1\eta=\sqrt{p\beta}u e_0/d$ and $K_2\eta=\sqrt{(1-p)\beta}u e_0/d$. Their contributions to $N(X_+)$ are respectively $p\beta u(e_2e_0^T+e_0e_2^T)/d$ and $(1-p)\beta u(e_3e_0^T+e_0e_3^T)/d$. The $K_0$ contribution supplies $-v e_1$ and $\sqrt{a\beta}kh$ in $w_p$. This proves the entire output in (R.125); $w_p\perp e_0$ gives eigenvalues $\pm\|w_p\|$. Squaring and using $p^2+(1-p)^2=1-2p(1-p)$ and the stated normalization gives the last equality. Equation (R.95) consumes this one common input pair. Finally (R.105) applied to the diagonal $B$ gives $c_{\rm pl}=a+\beta|2p-1|$. For $b_*=\sqrt a$, $(b_*-a)/\beta=b_* /(1+b_*)$, proving (R.126) and its strictness direction. $\square$

**Proposition 25.2 (an exact omitted-term discriminator).** At $a=\beta=1/2$, $u=v=k=1/2$, $p=1/10$, the actual channel (R.123) has rank $B=\operatorname{rank}C_{\rm out}=3$, $c_{\rm pl}=9/10>1/\sqrt2$, and the squared ratio in (R.125) is $97/200$. Keeping just $K_0,K_1$ instead gives $167/400$ for that same input and fails TP.

**Proof.** The parameter norm is $1/4+(1/4)/(1/2)+1/4=1$. The full numerator in (R.125) is $1/4+(1/16)(82/100)+1/16=291/800$, and its denominator is $3/4$, giving $97/200$. Deleting $K_2$ deletes the $e_3$ coefficient $\beta u(1-p)/d$ of $w_p$, so the squared ratio decreases by $\beta^2u^2(1-p)^2/d^2=27/400$. The result is $167/400$. The removed nonzero PSD contribution $K_2^TK_2$ also prevents the remaining list from being TP. The rank and plane inequalities follow from Theorem 25.1. $\square$

## 26. Four actual Kraus terms with the same input witness

**Theorem 26.1 (common-witness mixture and exact zero-$k$ formula).** Let $N_0$ be (R.115) with $s_0=s_1=0$, $u^2+v^2/a+k^2=1$. Let $S|_U=J|_U$ and $Sh=h$, so $S$ is a real orthogonal matrix, rather than the singular extension $J$ itself. For $0\leq p\leq1$, the actual channel $N_p=pN_0+(1-p)\operatorname{Ad}_S N_0$ has the complete four-term list

$$
\sqrt p K_0,\quad \sqrt p K_1,\quad
\sqrt{1-p}SK_0,\quad\sqrt{1-p}SK_1.
\tag{R.127}
$$

For positive beta and $0<p<1$ its common blocks satisfy

$$
\begin{gathered}
B_p=\operatorname{diag}(ap,a(1-p),\beta p,\beta(1-p),0),\\
q=1,\quad \operatorname{rank}B_p=4,\quad
c_{\rm pl}=|2p-1|,\qquad
\operatorname{rank}C_{{\rm out},p}=4\ \Longleftrightarrow\ v\ne0.
\end{gathered}
\tag{R.128}
$$

For exactly the same $X_+$ of (R.117) in both summands,

$$
\begin{aligned}
\frac{\|N_p(X_+)\|_1}{2}
&\leq\frac{\|N_0(X_+)\|_1}{2}
=\sqrt{a-\frac{\beta(a-\beta)u^2}{\beta+v^2}}
\leq\sqrt a.
\end{aligned}
\tag{R.129}
$$

When $k=0$, this squared ratio is exactly

$$
\frac{\|N_p(X_+)\|_1^2}{4}
=\frac{(1-2p)^2v^2+\beta^2u^2}{\beta+v^2}
=a-\frac{\beta(a-\beta)u^2+4p(1-p)v^2}{\beta+v^2}.
\tag{R.130}
$$

Both formulas include $p=0,1$, where $B_p$ has rank two and no rank-four conclusion is made. Equation (R.95) again gives $\delta_{N_p}\geq1-\sqrt a$. In the zero-$k$ formula, half beta, $v\ne0$ and interior $p$ make the squared ratio strictly less than $a$. The hard plane region here is exactly $|2p-1|>\sqrt a$.

**Proof.** Orthogonality of $S$ makes (R.127) TP, and $SQ S^T=Q$, $SJ=JS$ preserve the actual phase-output relation. The displayed first-column matrix has four independent columns for positive beta and interior $p$, giving (R.128)'s $B$, $P_A=I_4$, and $q=1$. For $v\ne0$, consider the unscaled four third columns $t_0,t_1,St_0,St_1$. Their $e_3,e_2$ coordinates first distinguish $t_1,St_1$, respectively. After their coefficients vanish, their $e_1,e_0$ coordinates distinguish $t_0,St_0$, respectively, because $\sqrt{\beta/a}v\ne0$. Thus all four are independent, even for $k=0$ or $u=0$. If $v=0$, $t_0,St_0$ are both multiples of $h$, while $t_1,St_1$ are multiples of $e_0,e_1$, so rank is at most three. The full-column-rank $A$ transfers this exact rank statement to $C_{{\rm out},p}$. The diagonal difference gives $c_{\rm pl}$ as displayed.

The input is fixed before taking either output norm:

$$
N_p(X_+)=pN_0(X_+)+(1-p)SN_0(X_+)S^T.
$$

Triangle inequality and orthogonal invariance bound its norm by $\|N_0(X_+)\|_1$. The explicit zero-$s_0,s_1$ case of (R.118) supplies (R.129); this is an application within the present four-term proof.

When $k=0$, the $h$ row and column vanish. In the ordered split $(e_0,e_3)\mid(e_1,e_2)$ the output is $\left(\begin{smallmatrix}0&M\\M^T&0\end{smallmatrix}\right)$ with

$$
M=\frac1d\begin{pmatrix}(1-2p)v&p\beta u\\(1-p)\beta u&0\end{pmatrix}.
$$

Its trace norm is $2\|M\|_1$. If $\sigma_1,\sigma_2\geq0$ are the singular values of $M$, then $(\sigma_1+\sigma_2)^2=\operatorname{Tr}(MM^T)+2|\det M|$. Here $\det M=-p(1-p)\beta^2u^2/d^2$, so the terms in $u^2$ combine to $[p^2+(1-p)^2+2p(1-p)]\beta^2u^2/d^2=\beta^2u^2/d^2$. This proves the first expression in (R.130), including zero determinant and repeated singular values. Substitute $u^2+v^2/a=1$ to obtain the second. No sign of $u$ or $v$ was discarded. At $p=0,1$ just two first columns remain; the formulas are still defined because $\beta>0$. $\square$

**Proposition 26.2 (a strict actual instance and the common-input requirement).** The parameters $a=\beta=1/2$, $u=k=0$, $v^2=1/2$, $p=1/10$ give an actual rank-four example with $\operatorname{rank}C_{\rm out}=4$, $c_{\rm pl}=4/5>1/\sqrt2$, and squared witness ratio $8/25<1/2$.

**Proof.** All assertions follow by direct substitution in (R.128)–(R.130). The common input in the preceding proof cannot be replaced by unrelated minimizers for arbitrary component channels. For a concrete standard caution within this use of mixtures, qubit Pauli channels with probabilities $(1/2,0,1/4,1/4)$ and $(3/8,3/8,1/8,1/8)$, in the order $(I,\sigma_x,\sigma_y,\sigma_z)$, have Bloch matrices $\operatorname{diag}(0,1/2,1/2)$ and $\operatorname{diag}(1/2,0,0)$. Each has minimum traceless-Hermitian contraction zero. Their equal mixture has Bloch matrix $I_3/4$ and minimum contraction $1/4$. The probability tables verify CPTP directly, and the contraction values are the least singular values on the Bloch sphere. Thus minimum contraction is not a convex function that would justify mixing separately chosen zero witnesses. This is a limitation of that proof step, not an extra all-class package or a claim that these qubit maps belong to the original qutrit class. $\square$

## 27. A half-beta channel isometric on every imaginary direction

**Theorem 27.1 (exact imaginary-space obstruction with a real zero witness).** At $a=\beta=1/2$ the actual two-Kraus channel

$$
K_0=(e_0,e_1,e_2)/\sqrt2,\qquad
K_1=(e_2,e_3,-e_0)/\sqrt2
\tag{R.131}
$$

has $q=1$, rank $B=\operatorname{rank}C_{\rm out}=2$ and $c_{\rm pl}=1$. For every $\xi=(x,y,z)\in\mathbb R^3$, including zero, put

$$
X(\xi)=i\begin{pmatrix}0&x&y\\-x&0&z\\-y&-z&0\end{pmatrix},\qquad
E_{ij}^{\wedge}=e_ie_j^T-e_je_i^T.
$$

Then $X(\xi)\in\mathcal H_0$ and

$$
\begin{gathered}
N(X(\xi))=iF(\xi),\\
F(\xi)=\frac{x}{2}(E_{01}^{\wedge}+E_{23}^{\wedge})
        +yE_{02}^{\wedge}
        +\frac z2(E_{12}^{\wedge}+E_{03}^{\wedge}),\\
\|N(X(\xi))\|_1=\|X(\xi)\|_1=2\sqrt{x^2+y^2+z^2}.
\end{gathered}
\tag{R.132}
$$

In contrast the nonzero real symmetric input $X_{\rm r}=|0\rangle\langle2|+|2\rangle\langle0|\in\mathcal H_0$ obeys

$$
\|X_{\rm r}\|_1=2,\qquad N(X_{\rm r})=0,\qquad m_0(N)=0.
\tag{R.133}
$$

Thus searching only the imaginary antisymmetric Hermitian three-space cannot establish G even for this example: every nonzero member of that search space has ratio one, while a valid real witness has ratio zero. The example satisfies G and supplies no counterexample to it.

**Proof.** Each displayed column triple is orthonormal before division by $\sqrt2$, so the TP sum is $I_3$. Its first columns give $B=\operatorname{diag}(1/2,0,1/2,0,0)$ and its cross block is $C_{\rm out}=(e_0e_2^T-e_2e_0^T)/2$. The phase relation, rank and $q$ assertions follow as in (R.116); the third columns are independent. The input spectrum is $0,\pm\sqrt{x^2+y^2+z^2}$, by the characteristic polynomial of its $3\times3$ skew matrix. Direct multiplication of both Kraus terms gives exactly the signed expression for $F$ in (R.132), whose $h$ row and column vanish.

Let the four active eigenvalues of the real skew matrix $F$ be $\pm i\lambda_1,\pm i\lambda_2$, with $\lambda_j\geq0$. These are its two possibly zero singular-value pairs. On the ordered active frame $(e_0,e_1,e_2,e_3)$,

$$
\begin{aligned}
\lambda_1^2+\lambda_2^2
 &=\tfrac12\|F\|_F^2=(x^2+z^2)/2+y^2,\\
\operatorname{Pf}F
 &=F_{01}F_{23}-F_{02}F_{13}+F_{03}F_{12}
   =(x^2+z^2)/4,\\
\lambda_1\lambda_2&=|\operatorname{Pf}F|=(x^2+z^2)/4,\\
(\lambda_1+\lambda_2)^2&=x^2+y^2+z^2.
\end{aligned}
$$

Here the Pfaffian identity follows by expanding the $4\times4$ determinant as the square of the displayed three-term expression. The nonnegative square root fixes the sign of $\lambda_1+\lambda_2$. The Hermitian eigenvalues of $iF$ have absolute values $\lambda_1,\lambda_1,\lambda_2,\lambda_2$, proving the norm identity. The calculation permits all signs of $x,y,z$, the zero vector, repeated singular values and vanishing singular values without division. Finally $N(X_{\rm r})=C_{\rm out}+C_{\rm out}^T=0$, proving (R.133). $\square$

## 28. The exact pointwise dual on the seven-dimensional complex Hermitian domain

**Theorem 28.1 (source-specific all-complex norming-functional dual).** For any actual common real Kraus realization of Definition 23.1, let $P=|0\rangle\langle0|+|1\rangle\langle1|$, and define on $M_3$ the complex-linear map

$$
\Pi(Z)=Z-\frac{Z_{00}+Z_{11}}2P-Z_{22}E_{22},\qquad
\mathcal A=\Pi\circ N^\dagger.
\tag{R.134}
$$

Its restriction to Hermitian matrices is the real trace-inner-product orthogonal projection onto precisely the real seven-dimensional $\mathcal H_0$ in (R.102). In this theorem $\Pi$ is an input-space projection, not the output phase-support projection of Theorem 2.1, and $\mathcal A$ is a map, not the first-column matrix $A$ of (R.99). For every real $s\geq0$,

$$
\begin{aligned}
m_0(N)\geq s
\quad\Longleftrightarrow\quad
&\text{for every }\psi\in\mathbb C^3,\ \|\psi\|_2=1,\text{ there exists }F_\psi=F_\psi^\dagger\in M_5\text{ with}\\
&-I_5\preceq F_\psi\preceq I_5,\qquad
\mathcal A(F_\psi)=2s\Pi(|\psi\rangle\langle\psi|).
\end{aligned}
\tag{R.135}
$$

The choices are pointwise in $\psi$; a linear selection is not required. Both sides depend only on the same $B,C_{\rm out}$, not $D$ or $D_\perp$. The vector $\psi$ indexes all complex norming functionals, not a pure-versus-pure restriction on the primal witness $X$.

**Proof.** For Hermitian $Z$, $\Pi(Z)$ has trace zero and $22$ entry zero, and $\Pi$ fixes every $X\in\mathcal H_0$. The removed term belongs to $\operatorname{span}_{\mathbb R}\{P,E_{22}\}$, which is orthogonal to $\mathcal H_0$ for $\langle Z,X\rangle=\operatorname{Tr}(ZX)$. Conversely these are exactly the two independent real constraints defining $\mathcal H_0$, so its real dimension is $9-2=7$ and

$$
\operatorname{Tr}(\Pi(Z)X)=\operatorname{Tr}(ZX)\quad(X\in\mathcal H_0),\qquad
\ker\Pi|_{\operatorname{Herm}}=\operatorname{span}_{\mathbb R}\{P,E_{22}\}.
$$

The formula is also a complex-linear projection on all matrices. No positivity of this projection is assumed. For a Hermitian $F$, $N^\dagger(F)=\sum_\alpha K_\alpha^TFK_\alpha$. The only entry using $D$ is its $22$ entry $\operatorname{Tr}(FD)$, by (R.103). The projection deletes that entry; every remaining entry is determined by $B,C_{\rm out}$ and $J$. Equivalently $\operatorname{Tr}(\mathcal A(F)X)=\operatorname{Tr}(F\mathcal L_{B,C_{\rm out}}(X))$. Thus this is the adjoint of the precise restricted action (R.104), establishing the claimed dependence on the common pair.

For every traceless Hermitian qutrit $X$,

$$
\|X\|_1=2\|X\|_{\rm op}.
$$

Indeed if there are two positive eigenvalues, their sum is the absolute value of the single negative eigenvalue, which is at least each of them; the reverse sign case is identical. A zero eigenvalue gives the same equality, and the zero matrix is immediate. This proves the identity for rank two, rank three, repeated eigenvalues and both sign patterns. It is specific to the traceless qutrit space.

Assume first the pointwise lifts in (R.135). For any $X\in\mathcal H_0$ and complex unit $\psi$,

$$
2s|\langle\psi|X|\psi\rangle|
=|\operatorname{Tr}(F_\psi N(X))|
\leq\|N(X)\|_1.
$$

The last inequality is Hermitian operator-norm/trace-norm duality, since $\|F_\psi\|_{\rm op}\leq1$. Taking the supremum over all complex unit $\psi$ gives $2s\|X\|_{\rm op}=s\|X\|_1\leq\|N(X)\|_1$. This is exactly the lower bound defining $m_0$. The absolute value covers both signs with the same functional; it needs no extra factor or second family of lifts.

Conversely assume $m_0(N)\geq s>0$. The restriction of $N$ to the real normed space $\mathcal H_0$ is injective. On the real subspace $N(\mathcal H_0)\subseteq\operatorname{Herm}(M_5)$, define for each complex unit $\psi$

$$
\ell_\psi(N(X))=2s\operatorname{Tr}(X|\psi\rangle\langle\psi|).
\tag{R.136}
$$

It is well defined by injectivity, real linear, and has norm at most one because

$$
|\ell_\psi(N(X))|\leq2s\|X\|_{\rm op}
 =s\|X\|_1\leq\|N(X)\|_1.
$$

Apply the real Hahn–Banach theorem to extend it to all of $\operatorname{Herm}(M_5)$ with norm at most one. In finite dimension any real linear functional on this real Hermitian space has a unique Hermitian trace representative $F_\psi$: this follows by taking a real orthonormal Hermitian matrix basis and its coefficients. Testing the extension on the signed rank-one spectral projections of $F_\psi$ gives $\|F_\psi\|_{\rm op}\leq1$; conversely this bound controls the functional by spectral decomposition. The extension therefore has $-I_5\preceq F_\psi\preceq I_5$ and

$$
\operatorname{Tr}\bigl([\mathcal A(F_\psi)-2s\Pi(|\psi\rangle\langle\psi|)]X\bigr)=0
\quad\text{for all }X\in\mathcal H_0.
$$

The bracket is itself in $\mathcal H_0$, so its pairing with itself forces it to vanish. This proves the other direction. At $s=0$, the lower bound is automatic and $F_\psi=0$ supplies every lift without injectivity; the separate endpoint requires no inverse. Real Hahn–Banach and finite-dimensional Schatten duality are standard ingredients consumed in this particular restricted-channel proof, not new general results. $\square$

**Proposition 28.2 (complex norming directions and a noninjective check).** Real unit $\psi$ cannot replace all complex unit $\psi$ in the norming step of Theorem 28.1. For $X=i(E_{01}-E_{10})\in\mathcal H_0$, all real $\psi$ have $\langle\psi|X|\psi\rangle=0$, while $(|0\rangle-i|1\rangle)/\sqrt2$ has expectation one. For $\psi=(1,i,1)/\sqrt3$, the matrix $\Pi(|\psi\rangle\langle\psi|)$ has nonzero imaginary entries. On the channel (R.131), no positive $s$ can satisfy (R.135); $s=0$ still does.

**Proof.** A real quadratic form of a real antisymmetric matrix is zero, whereas the stated complex vector is a unit eigenvector of $X$ with eigenvalue one. Directly $\Pi$ removes only diagonal entries from the second example, leaving its imaginary $01$ and $12$ entries. Thus a restriction to real norming functionals would discard an actual part of $\mathcal H_0$. For the channel (R.131), use the real kernel input $X_{\rm r}$ from (R.133) and $\psi=(|0\rangle+|2\rangle)/\sqrt2$, for which $\operatorname{Tr}(X_{\rm r}|\psi\rangle\langle\psi|)=1$. Pairing the asserted lift with $X_{\rm r}$ would give $0=2s$, impossible for $s>0$. The zero choice handles $s=0$. Neither example restricts the primal domain to pure differences; the entire real seven-dimensional Hermitian space remains in (R.135). $\square$

## 29. A finite sufficient certificate and an actual lower-certificate family

**Theorem 29.1 (linear and decomposable sufficient certificate for the exact dual).** Fix an actual channel as in Theorem 28.1 and $s\geq0$. A sufficient condition for (R.135) is a complex-linear Hermiticity-preserving map $W:M_3\to M_5$ such that

$$
\mathcal A\circ W=2s\Pi,\qquad
\Phi_\pm:Z\longmapsto\operatorname{Tr}(Z)I_5\pm W(Z)
\text{ are positive maps}.
\tag{R.137}
$$

Use the unnormalized input-first Choi convention

$$
\begin{gathered}
C_W=\sum_{i,j=0}^2E_{ij}\otimes W(E_{ij}),\qquad
\Omega_3=\sum_{i=0}^2|i\rangle\otimes|i\rangle,\\
C_\Pi=|\Omega_3\rangle\langle\Omega_3|
       -\tfrac12P\otimes P-E_{22}\otimes E_{22},\\
(\mathrm{id}_3\otimes\mathcal A)(C_W)=2sC_\Pi.
\end{gathered}
\tag{R.138}
$$

For a finite sufficient strengthening of positivity in (R.137), it is enough to find Hermitian matrices satisfying

$$
I_{15}\pm C_W=S_\pm+T_\pm^{\Gamma},\qquad
S_\pm\succeq0,\quad T_\pm\succeq0,
\tag{R.139}
$$

where $\Gamma$ is partial transpose on the three-dimensional INPUT factor, in the fixed original basis. The equality in (R.138) and these four PSD conditions are a finite sufficient system for $m_0(N)\geq s$. No converse from the pointwise choices $F_\psi$ to a single $W$, or from positivity to (R.139), is asserted.

**Proof.** For each complex pure input $\rho_\psi=|\psi\rangle\langle\psi|$, set $F_\psi=W(\rho_\psi)$. Hermiticity preservation makes it Hermitian; positivity of $\Phi_\pm$ gives $I_5\pm F_\psi\succeq0$. The first equality in (R.137) gives its exact lift in (R.135), which is sufficient by Theorem 28.1.

Expanding $\Pi(E_{ij})$ gives the stated $C_\Pi$: only $E_{00},E_{11}$ have the $-P/2$ term, and $E_{22}$ has the $-E_{22}$ term. Linearity of the Choi representation proves the last equality of (R.138) equivalent to the first in (R.137), on the whole complex matrix algebra. In particular the maximally entangled vector is unnormalized; normalizing it without changing the other coefficients would change the equation. The Choi matrix of $Z\mapsto\operatorname{Tr}(Z)I_5$ is $I_{15}$.

For clarity, the standard Choi positivity ingredient can be consumed directly here. A PSD input-first matrix $S=\sum_r|v_r\rangle\langle v_r|$ can be reshaped as $v_r=\sum_i|i\rangle\otimes L_r|i\rangle$, giving the CP map $Z\mapsto\sum_rL_rZL_r^\dagger$. Applying input transpose changes its Choi matrix to $S^\Gamma$. Consequently the right side of (R.139) represents a CP map plus another CP map composed with input transposition. Transposition preserves PSD inputs, so this sum is positive on every complex PSD input. It is not necessary for $T_\pm^\Gamma$ itself to be PSD. This proves sufficiency for each sign and therefore (R.137). These are the usual Choi and decomposable-map ingredients inside this common-pair certificate. Neither Hahn–Banach nor this argument supplies a linear selection or proves that all positive maps are decomposable. $\square$

**Theorem 29.2 (an explicit actual nonzero certificate with both PSD decompositions).** On the already-owned $t=0$ member of (R.75), the actual normalized Kraus list is, also including $\beta=0$,

$$
K_0=(\sqrt a e_0,\sqrt a e_1,h),\qquad
K_1=(\sqrt\beta e_2,\sqrt\beta e_3,0),\qquad
0\leq\beta\leq1/2.
\tag{R.140}
$$

Let $V=(e_0,e_1,h)$, $D_a=\operatorname{diag}(\sqrt a,\sqrt a,1)$, $L=VD_a^{-1}$. For every $0\leq s\leq a$ the map

$$
W(Z)=sL(2Z-\operatorname{Tr}(Z)I_3)L^\dagger
\tag{R.141}
$$

satisfies (R.137)–(R.139), and hence $m_0(N)\geq s$. Explicitly put $R_s=I_5-sLL^\dagger\succeq0$, $\omega_L=\sum_i|i\rangle\otimes L|i\rangle$, and let $\mathsf F$ be the swap on $\mathbb C^3\otimes\mathbb C^3$. Valid PSD choices are

$$
\begin{aligned}
C_W&=s(2|\omega_L\rangle\langle\omega_L|-I_3\otimes LL^\dagger),\\
S_+&=I_3\otimes R_s+2s|\omega_L\rangle\langle\omega_L|,&T_+&=0,\\
S_-&=I_3\otimes R_s,&
T_-&=2s(I_3\otimes L)(I_9-\mathsf F)(I_3\otimes L^\dagger).
\end{aligned}
\tag{R.142}
$$

For positive beta the endpoint certificate $s=a$ is nonzero and satisfies $a<\sqrt a$. It is a lower bound on contraction, not an improving recovery or a counterexample to G. At $\beta=0$ this channel is isometric and $m_0(N)=1$.

**Proof.** The TP sum for (R.140) is $\operatorname{diag}(a+\beta,a+\beta,1)=I_3$, and the phase outputs follow as before. For positive beta, its two first columns are independent, so $q=1$; the disappearance of the second Kraus term at zero is allowed. The ranges of $V$ and $K_1$ are orthogonal, and $K_0=VD_a$, so $K_0^\dagger L=L^\dagger K_0=I_3$ and $K_1^\dagger L=0$. Hence on every complex $Z$,

$$
N^\dagger(W(Z))=s(2Z-\operatorname{Tr}(Z)I_3),\qquad
\mathcal A(W(Z))=2s\Pi(Z),
$$

using $\Pi(I_3)=0$. For a complex unit $\psi$, $2\rho_\psi-I_3$ has eigenvalues $1,-1,-1$, so $\|W(\rho_\psi)\|_{\rm op}\leq s\|L\|_{\rm op}^2=s/a\leq1$. Thus $I_5\pm W(\rho_\psi)\succeq0$; spectral decomposition of any PSD $Z$ proves positivity of $\Phi_\pm$. This also verifies the nonzero certificate directly, independently of its decomposition.

The nonzero eigenvalues of $LL^\dagger$ are $1/a,1/a,1$, so $R_s\succeq0$ for the stated interval. The swap is a self-adjoint involution, so $I_9-\mathsf F\succeq0$. Every term in (R.142) is therefore PSD. Expansion of $W$ on matrix units gives its displayed Choi matrix. Under input partial transpose,

$$
\bigl[(I_3\otimes L)\mathsf F(I_3\otimes L^\dagger)\bigr]^\Gamma
=|\omega_L\rangle\langle\omega_L|,
$$

because $\mathsf F=\sum_{ij}E_{ij}\otimes E_{ji}$, and interchanging $i,j$ after transposing the first factor gives $\sum_{ij}E_{ij}\otimes LE_{ij}L^\dagger$. Thus $T_-^\Gamma=2s(I_3\otimes LL^\dagger-|\omega_L\rangle\langle\omega_L|)$. Adding $S_-$ gives $I_{15}-C_W$, while $S_++T_+^\Gamma=I_{15}+C_W$ is immediate. This checks both signs, the coefficient two and the input-transpose convention. Finally $\beta=0$ gives $K_1=0$, $K_0=V$ an isometry, so every trace norm is preserved. For $0<\beta\leq1/2$, $0<a<1$ gives $a<\sqrt a$ exactly. $\square$

## 30. Attribution and the original all-class boundary

**Definition 30.1 (scope of the mathematical compositions).** The additional source-specific results are the independent-coefficient actual family and complete phase minimum (R.115)–(R.122), the full three-term output (R.123)–(R.126), the four-term same-input output (R.127)–(R.130), the exact imaginary-space obstruction (R.131)–(R.133), and the restricted-action dual and its actual sufficient-certificate family (R.134)–(R.142). The old $u=v$, $s_0=s_1=0$ family, common-Gram realization, inverse damping, orthogonal-support Jordan domain and recovery obstruction retain their existing owners (R.75), (R.89)–(R.112). The spectral, Pfaffian, Schatten-dual, real Hahn–Banach, Choi and decomposable-map steps are standard ingredients consumed in these particular statements. They are not additional general novelty claims.

The minimum trace-distance interface remains [G. Chiribella and K. Goswami, *Maximum and minimum causal effects of physical processes*, arXiv:2404.07683v3, Proposition 6, (14), PDF p.6; Section III.A, (24), PDF p.8](https://arxiv.org/pdf/2404.07683v3). It permits orthogonal-support density pairs, and forces both to be pure only for qubit input. Its classical illustration after Proposition 6 is not a quantum pure-pair counterexample. Corollary 7, (32), PDF p.10 is an approximate recovery bound with dimension-dependent and square-root losses; it supplies neither the model-specific $\sqrt a$ estimate nor a sharp all-encoder lower bound here.

The distinction between pure-pair and mixed-pair minimization has a primary quantum illustration in [T. Heinosaari, L. Mazzarella and M. M. Wolf, *Quantum tomography under prior information*, arXiv:1109.5478v3, Corollary 1 and Proposition 5, PDF p.8; Remark 2, PDF p.9](https://arxiv.org/pdf/1109.5478v3). In its nontrivial qutrit pure-state informationally complete case, the Hermitian measurement kernel is $\mathbb RT$ for invertible traceless Hermitian $T$. Writing $T=T_+-T_-$, $t=\operatorname{Tr}T_+=\operatorname{Tr}T_->0$, gives orthogonal-support densities $T_+/t,T_-/t$ with identical measurement output. On the other hand a difference of distinct pure states has rank at most two, so it cannot lie in that kernel. On the compact set of orthogonal pure pairs the output distance therefore has a strictly positive minimum, whereas the unrestricted orthogonal-support minimum is zero. Proposition 5's minimal construction has eight classical outcomes. This is an illustration outside the original $M_3\to M_5$ real phase class; it supplies no counterexample to G and is not a substitute for (R.135)'s complex norming-functional quantifier.

The exact all-prior trace-isometry structure remains [F. Ticozzi and L. Viola, *Quantum Information Encoding, Protection, and Correction from Trace-Norm Isometries*, arXiv:0912.0963v1, Definition 1, Lemma 1 and (4)–(8), PDF pp.2–3; Definitions 4–5 and (16), PDF p.7](https://arxiv.org/pdf/0912.0963v1). Its exact subsystem interface and the complex-CP exclusion of nonzero antiunitary blocks are consumed with the boundaries already stated in Definition 23.7. Its approximate section assumes closeness to an actual linear isometry. A lower Lipschitz bound on $\mathcal H_0$ alone does not furnish that premise or the sharp approximate coefficient. These narrow interfaces carry no exhaustive literature-search or global originality assertion.

**Definition 30.2 (unclosed branches and endpoint discipline).** Assumption 23.5 remains unproved and unrefuted on the entire feasible domain (R.108). In particular it still includes arbitrary noncanonical rank-two $B$, canonical rank-two $B$ with third columns outside (R.120), and arbitrary rank-three or rank-four common pairs without the displayed shared-witness structure. At half beta rank-two $B$ has a canonical frame, but the third-column issue persists. An actual outside-family example does not settle its witness problem, and none of these families is an exhaustive classification of G.

The original encoder's possible Kraus Choi rank up to nine, the normalized comparison's bound $\operatorname{rank}B\leq4$, and the changed-channel discrepancy are exactly Theorems 1.3 and 23.2–23.4, especially (R.101), (R.106) and (R.112). They are reused without replacing the original map by its comparison. For $q=1$ those maps coincide. For $q=0$ there is a direct cross zero witness and no division by $q$. For intermediate $q$, only the stated $\mathcal H_0$ inverse-damping argument transports witnesses; general inputs retain the $Y_{22}[D_\perp-(1-q)D^\sharp]$ term. The rank-nine original branch is not deleted by the rank-two, three or four comparison families above.

The tilted formulas use $\beta>0$ and hence $d>0$. They do not extend a positive-beta rank assertion to $\beta=0$, nor define a tilted vector when $\beta=v=0$. The original zero-beta sharp lower target is simply $\delta_N\geq0$, with its existing isometric upper example. For instance the separate endpoint Kraus list $K_0=(e_0,e_1,0)$, $K_1=(0,0,e_0)$ is TP and has the direct zero witness $E_{02}+E_{20}$; it need not use (R.117). The isometric endpoint of Theorem 29.2 instead has $m_0=1$. Both behaviors are compatible with the original endpoint target. The $p=0,1$ values in Sections 25–26 explicitly retain their dropped ranks.

The exact equivalence (R.135) does not equate pointwise lifts with the sufficient finite linear/decomposable system (R.137)–(R.139). Infeasibility of that system proves neither the existence nor the absence of the pointwise lifts, and proves neither G nor its negation. An exact feasible $s>\sqrt a$ on one actual normalized pair would imply $m_0(N)\geq s>\sqrt a$ and refute G. No such certificate or pair is supplied here. Even a refutation of G would leave open $m_{\min}(N)\leq\sqrt a$ and the possibility of another full-reference diamond lower certificate; it would not alone refute the original recovery target.

The unchanged original task in Definition 22.2 is to prove $\delta_N\geq1-\sqrt{1-\beta}$ for every actual original real-Kraus encoder, or exhibit an actual original-class encoder and one complex CPTP recovery with a rigorous strictly smaller unhalved full-reference diamond upper certificate. Neither alternative is settled by these families or the finite sufficient system. Their status is ordinary conditional finite-dimensional mathematics, not a kernel result. Physical uses still require the actual encoder, supplied inputs, common source-fiber membership, finite-history transport and native-word joint legality of the phase-gain volume; these mathematical frames, witnesses and certificates supply no native operations, input preparation, encoder/decoder apparatus or hardware resources. The larger complex encoder class remains separate.

## 追加锚（本行以下为增补区）

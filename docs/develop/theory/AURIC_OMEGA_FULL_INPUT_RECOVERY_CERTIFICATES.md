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

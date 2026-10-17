# Arithmetic holographic RT — continuation III

Continuation of [ARITHMETIC_HOLOGRAPHIC_RT_II.md](ARITHMETIC_HOLOGRAPHIC_RT_II.md), which continues [ARITHMETIC_HOLOGRAPHIC_RT.md](ARITHMETIC_HOLOGRAPHIC_RT.md). The section numbering and fixed maximally-correlated channel encodings are retained.

## 88. A path-free local quarter minimum for a party of Kraus rank at most three

This is a new consequence of the full original-channel comparison geometry in [section 86](ARITHMETIC_HOLOGRAPHIC_RT_II.md#86-local-quartic-stability-from-the-rank-two-ky-fan-minimum-manifold) and the all-disphenoid coefficient in [section 87](ARITHMETIC_HOLOGRAPHIC_RT_II.md#87-exact-anisotropic-quartic-coercivity-at-every-disphenoid-equality-pair). The proof is a uniform finite-dimensional neighborhood argument. It does not infer a neighborhood statement merely from the individual C² path limits of section 87.

The perturbed A channel may have arbitrary Kraus rank and both channels may leak into wrong output fibres. The perturbed B channel is required to have Kraus rank at most three. No path, differentiability, or choice of a continuous third Choi eigenvector is assumed. The unrestricted case, in which both local ranks may be larger, remains open.

### 88.1. The theorem

The logical input has basis |f,i〉, 1≤f≤4 and i∈{0,1}. Define the target channel ℱ:C⁴⊗C²→C⁴ by

\[
 \mathcal F(|f,i\rangle\langle f,j|)=\delta_{ij}|f\rangle\langle f|,
 \qquad
 \mathcal F(|f,i\rangle\langle g,j|)=\tfrac12|f\rangle\langle g|
 \quad(f\ne g).
\]

The fixed isometric encodings are V_in|f,i〉=|f,i〉⊗|f,i〉 and V_out|f〉=|f〉⊗|f〉, with encoding channels J_in(X)=V_in X V_in* and J_out(Y)=V_out Y V_out*. For original CPTP maps A,B:C⁸→C⁴ define

\[
 \delta(A,B)=\|(A\otimes B)\circ J_{\rm in}
                     -J_{\rm out}\circ\mathcal F\|_\diamond.
\]

The norm is unhalved and permits arbitrary references. A quarter-error pair means δ(A₀,B₀)=1/4. Kraus rank means the rank of the Choi matrix, equivalently the minimum pure Stinespring environment dimension.

Let (A₀,B₀) be any original quarter-error pair of channels C⁸→C⁴, with B₀ of Kraus rank two, as classified in [section 82](ARITHMETIC_HOLOGRAPHIC_RT_II.md#82-quarter-error-rigidity-minimal-kraus-product-and-the-complete-rank-two-party-family). For any channel B let J_B be its unnormalized Choi matrix, with Tr J_B=8, and define

\[
 \epsilon_2(B)=\sum_{j=3}^{32}\lambda_j(J_B),
 \qquad \lambda_1\ge\lambda_2\ge\cdots\ge0.
                                                               \tag{1}
\]

For every constant

\[
 0<\kappa<{35\over4096},                                  \tag{2}
\]

there is a neighborhood U of (A₀,B₀) in the space of original channels such that

\[
 \delta(A,B)\ge {1\over4}+\kappa\epsilon_2(B)^2
 \quad\text{for every }(A,B)\in U\text{ with }\operatorname{rank}J_B\le3.
                                                               \tag{3}
\]

Here δ is the original unhalved arbitrary-reference diamond error. The roles of A and B may be exchanged. The neighborhood can depend on the base equality pair and on κ. In particular rank-three B channels with positive Choi tail have strictly larger error than 1/4 in this neighborhood, irrespective of the nearby A channel's Kraus rank. Rank-two B channels retain the global lower bound 1/4.

This is a restricted local-minimum theorem. It makes no local-minimum assertion for unrestricted B rank and no global-optimum assertion. The constants in (2) are valid lower-bound coefficients; no sharpness claim for the complete diamond error is made.

### 88.2. Uniform old/new coordinates and the witness

Use the marker-aligned base coordinates from section 82. It is enough initially to work in the fixed finite A-environment dimension d≥4 and in B-environment dimension three, split into the old two dimensions and one new dimension. Write

\[
 V_B=U\sqrt{I-R^*R}\ \oplus\ R,
 \qquad U\in U(8),\quad R:\mathbb C^8\longrightarrow\mathbb C^4,
 \qquad r=\|R\|_F.                                      \tag{4}
\]

Every such pair with ‖R‖op<1 is a physical Stinespring isometry. Conversely, every nearby isometry with this old/new split has this form because its old square block W is invertible and its polar factor U satisfies W=U√(I−R*R).

Let x=(V_A,U) belong to the original comparison space
X=St(C⁸,C⁴⊗Cᵈ)×U(8). For chosen Stinespring isometries, let a_fi=(〈f|⊗I)V_A|f,i〉 and b_fi=(〈f|⊗I)V_B|f,i〉 be the correct-output environment records. Their forward Grams are G_(fi,gj)=〈a_fi,a_gj〉 and H_(fi,gj)=〈b_fi,b_gj〉, with inner products conjugate-linear in the first argument. Set K=G⊙H and let T be the 8×8 matrix with diagonal 2×2 blocks I₂ and off-diagonal blocks J₂/2. Define

\[
 f(x,R)=F(A,B)={1\over4}\Lambda_2(T-K).
 \qquad \delta(A,B)\ge\operatorname{Tr}(T-K)_+/4\ge f(x,R).
                                                               \tag{5}
\]

The original reference input has compression Kᵀ/8 on {|f,i〉_R⊗|ff〉_out}; its complementary positive trace is 1−Tr K/8. Keeping that trace proves (5), including arbitrary original output leakage and cross-sector coherences.

At the equality pair the top two eigenvalues of T−K are 1/2,1/2, separated from the others by at least 1/2, including boundary disphenoids. Thus f is real-analytic in a fixed neighborhood of (x₀,0). It is invariant under R↦−R, indeed under a common phase on the new Kraus vector. All Taylor estimates below are uniform after shrinking to the closure of a sufficiently small coordinate neighborhood. No new eigenvector regularity is used here.

Section 86 supplies a smooth embedded minimum manifold M in X, with f(m,0)=1/4, df_old=0, and old Hessian kernel exactly TM. Its normal Hessian is positive definite. All extra A-environment and original leakage directions are included in this assertion. In calibrated notation its points satisfy

\[
 C_f=S+\tfrac12WN_f,\quad \sum_fN_f=0,\quad
 S^*S=(\tfrac12-h/8)I_2,\quad W^*W=(h/2)I_2,\quad
 S^*W=i\beta I_2,                                       \tag{6}
\]

with h near 1/2 and β near zero. In (6), W denotes the coefficient matrix, not the old Stinespring block in the preceding paragraph.

The fixed-A_m witness property holds on the whole M. Put T_i=√2(S+(−1)^iW/2). Then T_i^*T_i=I₂ and a_fi=T_i conjugate(b_fi). Balance gives Σ_f|b_fi〉〈b_fi|=2I₂. If H_i^m is this tight fixed-bit Gram and H_i is any original B correct-output fixed-bit Gram, then H_i^m≤2I₄ and Tr H_i≤4. The rank-two projection P₀=(J₄/4)⊗I₂ therefore gives

\[
 \operatorname{Tr}(P_0K)=\tfrac14\sum_i\operatorname{Tr}(H_i^mH_i)\le4,
 \qquad \operatorname{Tr}(P_0T)=5,
 \qquad F(A_m,B)\ge1/4.                                 \tag{7}
\]

This proof includes complex marker overlaps and arbitrary original B leakage.

### 88.3. The exact quadratic noise kernel

For m∈M write B_i^m=[b_{1i},…,b_{4i}], a 2×4 matrix satisfying B_i^m(B_i^m)*=2I₂, and P_i^m=(B_i^m)*B_i^m/2. A new one-environment operator R is a 4×8 matrix. Its correct-output bit-i row is R_i=(r_{1i},…,r_{4i}); all other entries form R_wrong.

The degree-two coefficient of f(m,R) is exactly

\[
 L_m(R)={1\over8}\left(\|R_{\rm wrong}\|_F^2+
                   \sum_i\|R_i(I-P_i^m)\|_F^2\right).
                                                               \tag{8}
\]

To derive this, the old attenuation U_m√(I−R*R) contributes Tr(R*R)/8 to dF. The new correct Gram contributes −Σ_iTr(H_i^m R_i*R_i)/16=−Σ_i‖R_iP_i^m‖²/8. Their sum is (8). This uses only the same-bit tightness in (7), so h and β do not affect it.

Let K_m be the complex kernel of L_m in the Hilbert space of 4×8 matrices. It consists precisely of calibrated records

\[
 r_{fi}=L_i b_{fi},\qquad L_i\in\mathbb C^{1\times2},
 \quad i=0,1.                                           \tag{9}
\]

The orthogonal projection Π_m onto K_m is smooth in m: its correct rows are R_iP_i^m and its wrong entries vanish. Set

\[
 R_\flat=\Pi_mR,\quad R_\perp=(I-\Pi_m)R,\quad
 e=\|R_\perp\|_F,
 \quad S_R=L_0+L_1,\quad D_R=L_1-L_0.
                                                               \tag{10}
\]

The coefficients in (9) for R_flat are uniquely L_i=R_i(B_i^m)*/2. In particular

\[
 L_m(R)=e^2/8,\qquad
 r^2=e^2+\|S_R\|_F^2+\|D_R\|_F^2.                     \tag{11}
\]

The second identity follows from ‖R_flat‖²=2(‖L₀‖²+‖L₁‖²) and the parallelogram identity. The common coefficient S_R is an environment-gauge direction; it will be quantitatively controlled, not discarded.

### 88.4. Exact elimination of all old normal directions

Choose smooth tubular coordinates x=χ(m,n) near M, with n in a fixed local trivialization of the real normal bundle. Write f(m,n,R)=f(χ(m,n),R). At R=0, n=0 is a critical point and the normal Hessian is positive definite. The parameter-dependent implicit-function theorem gives a unique nearby solution

\[
 \partial_nf(m,n_*(m,R),R)=0,\qquad n_*(m,R)=O(r^2).
                                                               \tag{12}
\]

The estimate is uniform, because f is even in R, the forcing ∂_nf(m,0,R) is O(r²), and the inverse normal Hessian is uniformly bounded in a sufficiently small neighborhood. Shrink the normal-coordinate balls so their Hessians remain uniformly positive definite for all m and small R. Ordinary Taylor expansion along the segment from n_* to n then gives

\[
 f(m,n,R)\ge f(m,n_*(m,R),R)+a\|n-n_*(m,R)\|^2,
 \qquad a>0.                                            \tag{13}
\]

In particular no old tangent, including a larger A environment or output leakage, remains unminimized in this reduction.

The reduced smooth even function has the uniform expansion

\[
 f(m,n_*(m,R),R)=\tfrac14+L_m(R)+Q_m(R)+O(r^6),          \tag{14}
\]

where Q_m is a homogeneous real quartic polynomial in R, with coefficients smooth in m. To identify it, expand before minimization as
1/4+q_{H,m}(n)+L_m(R)+b_m(n,R)+q_{N,m}(R), with q_H quadratic in n, b linear in n and quadratic in R, and q_N quartic in R. Minimizing the first two n-dependent terms gives

\[
 Q_m(R)=\min_n\{q_{H,m}(n)+b_m(n,R)+q_{N,m}(R)\}.
                                                               \tag{15}
\]

There is no minimization over tangential motion in (12). On the flat kernel it is unnecessary: for fixed flat R the physical noise derivative L_m(R) is a nonnegative function on M with value zero, so its tangential differential is zero. Both the old Hessian and the mixed source therefore vanish on TM. Consequently (15) agrees, on K_m, with minimization over every old comparison tangent.

### 88.5. Gauge invariance of the flat quartic form

We need an identity on the whole nearby M, not just the classified base points:

\[
 Q_m(R_\flat)=Q_m(R_D),
 \quad (R_D)_{f0}=0,\quad (R_D)_{f1}=D_R b_{f1},
 \quad (R_D)_{\rm wrong}=0.                              \tag{16}
\]

Here the dimensions remain two old environment coordinates and one new coordinate. To prove (16), consider any smooth old comparison curve with x(t)=m+t²X+O(t⁴) in local coordinates and new sector tR_flat. The physical square-root parameterization (4) gives a coefficient of t⁴ equal to q_H(X)+b(X,R_flat)+q_N(R_flat), because R_flat lies in the quadratic kernel.

Apply the environment unitary exp(tΩ) with

\[
 \Omega=\begin{bmatrix}0&L_0^*\\-L_0&0\end{bmatrix}
                                                               \tag{17}
\]

on the old-two/new-one environment, identically on the output. The physical B channel is unchanged. The transformed new sector is t(R_flat−L₀U_m)+O(t³)=tR_D+O(t³), and the transformed old polar comparison tangent is X+Z for a fixed tangent Z depending on m,R_flat but not on X. The old and new parity in this construction gives no t² term in the new sector. The translation X↦X+Z is bijective on the full old tangent space.

Terms of order t³ in the new sector do not affect the t⁴ coefficient: the differential of the nonnegative quadratic form L_m at R_D∈K_m is zero. Likewise any tangential shift in the comparison point has zero mixed derivative, by the last paragraph of section 88.4. Thus minimization over all old tangents before and after this physical environment rotation gives (16). This argument uses a genuine unitary gauge of the physical channel, not error monotonicity under polar replacement.

At the base m₀, section 87 computes the right side of (16). If E=conjugate(D*D)=r₀I+r·σ and u_a are the squared disphenoid coordinates, then

\[
 Q_{m_0}(R_D)=\sum_a{(1-u_a)(7u_a-1)^2\over256u_a^2}r_a^2
       \ge {35\over4096}\|D\|_F^4.                     \tag{18}
\]

The last step uses that D has one row: E has rank at most one and |r|²=‖D‖⁴/4. This is precisely where the rank-three restriction is substantive.

Fix κ as in (2), and choose κ<c₁<35/4096. The construction D↦R_D is smooth in m and linear in D. By compactness of the unit sphere in C^{1×2}, continuity of Q_m and (18) give, after shrinking the m-neighborhood,

\[
 Q_m(R_\flat)\ge c_1\|D_R\|_F^4
 \quad\text{for every }m\text{ nearby and every }R_\flat\in K_m.
                                                               \tag{19}
\]

Homogeneity handles arbitrary D, including D=0. The exact gauge identity (16) is needed here: continuity alone would not control an arbitrary common L₀=L₁ component, which is a true zero mode.

Because Q_m is a smoothly varying quartic polynomial and Π_m is an orthogonal projection, there is a uniform finite C such that

\[
 |Q_m(R)-Q_m(R_\flat)|\le C e r^3.                      \tag{20}
\]

Combining (13)–(14), (19)–(20), and L_m=e²/8, then using Ce r³≤e²/16+4C²r⁶, gives a uniform estimate

\[
 f(m,n,R)\ge\tfrac14+e^2/16+c_1\|D_R\|_F^4-C_2r^6.
                                                               \tag{21}
\]

This holds for every nearby original comparison point and every small R. It is not yet a positive lower bound in the total tail, because the common gauge component could carry r. We next use the original Choi split to exclude that possibility quantitatively.

### 88.6. A uniform Choi/polar chart and the tail comparison

At B₀ the two nonzero Choi eigenvalues are 4,4. In a neighborhood there is a fixed spectral contour separating the largest two eigenvalues from the rest. Its rank-two spectral projection P(B) is smooth, regardless of degeneracy inside that two-dimensional cluster. Choose a smooth orthonormal frame E_B:C²→C³² for its range, aligned with the base Kraus vectors. Define the two old Choi vector columns by

\[
 C_W=E_B(E_B^*J_BE_B)^{1/2}.
                                                               \tag{22}
\]

The 2×2 matrix under the square root remains positive definite, so C_W is smooth in the channel coordinates. Its outer product is J_BP(B). When rank J_B≤3, the remaining matrix J_B(I−P(B)) is positive semidefinite of rank at most one. Choose any vector c_R with outer product equal to this remainder, or c_R=0 if it vanishes. No continuous choice of its phase or eigenvector is required. Reshape C_W and c_R as the old and new Kraus operators. Their Stinespring blocks W,R obey exactly

\[
 W^*W+R^*R=I_8,\qquad
 \langle K_{W,a},K_R\rangle_F=0\ (a=1,2),\qquad
 \|R\|_F^2=\epsilon_2(B).                               \tag{23}
\]

The middle identity follows from the orthogonality of the Choi spectral subspaces. At the base W is the square unitary Stinespring isometry; hence it stays invertible and its polar U is smooth. We have obtained (4) with an exact tail norm, uniformly even as ε₂ tends to zero and the rank drops.

For clarity define the row vector
Γ_V(R)_a=〈K_{V,a},K_R〉_F for any old-two-coordinate operator V. At the minimum point m associated to the actual comparison x=(V_A,U), the flat projection and tightness give

\[
 \Gamma_{U_m}(R)=2S_R.
                                                               \tag{24}
\]

Indeed the wrong outputs give zero, and on each correct bit the tight frame sends L_i to 2L_i. The perpendicular component has zero inner product with the common-gauge subspace, which is contained in K_m. Equivalently (24) follows directly by substituting L_i=R_i(B_i^m)*/2.

Use the exact Choi orthogonality Γ_W(R)=0. Cauchy–Schwarz and the smooth normal chart give

\[
 \begin{split}
 2\|S_R\|_F
  &=\|\Gamma_{U_m-W}(R)\|_F
       \le r\|U_m-W\|_F\\
  &\le r\{C_3\|n\|+r^2\}.
 \end{split}                                             \tag{25}
\]

For the last step, ‖U_m−U‖_F≤C₃‖n‖, and
‖U−W‖_F=‖I−√(I−R*R)‖_F≤‖R*R‖_F≤r². These bounds hold whenever ‖R‖op<1. They do not require the polar old Kraus vectors themselves to be Choi-orthogonal to R.

Choose η>0 so small that c₁(1−η)²>κ. By reducing the channel neighborhood, (25) gives ‖S_R‖²≤ηr². Therefore the exact decomposition (11) yields

\[
 q:=e^2+\|D_R\|_F^2=r^2-\|S_R\|_F^2\ge(1-\eta)r^2.
                                                               \tag{26}
\]

For r small enough that 2c₁r²≤1/16, put b=e². Since 0≤b≤q≤r²,

\[
 {e^2\over16}+c_1\|D_R\|_F^4
    ={b\over16}+c_1(q-b)^2
    \ge c_1q^2
    \ge c_1(1-\eta)^2r^4.                              \tag{27}
\]

Shrink the neighborhood once more so that C₂r²≤c₁(1−η)²−κ. Equations (21), (23), and (27) then prove

\[
 f(x,R)\ge\tfrac14+\kappa r^4
          =\tfrac14+\kappa\epsilon_2(B)^2.              \tag{28}
\]

All neighborhood choices are uniform inequalities on a local chart. There is no passage from pointwise path limits to a neighborhood assertion.

### 88.7. Arbitrary nearby A channels and the boundary of the result

For an arbitrary original A channel use the canonical Choi square-root Kraus decomposition in fixed environment dimension 32. It is continuous in J_A, including at rank changes. A fixed environment isometry aligns its base lift with the four-dimensional equality support. Thus every sufficiently nearby A channel has a lift in the Stinespring neighborhood used above with d=32. The old B lift from (22) is smooth, and its arbitrary-phase new vector has norm tending to zero by (23). Consequently all sufficiently nearby pairs of physical channels with rank J_B≤3 lie in the uniform chart to which (28) applies. Combining it with the original pinching consumer (5) proves (3).

The proof has retained all normal directions of the full original comparison space. In particular no extra A-environment direction, output leakage direction, or bit-frame phase has been silently omitted. The new one-dimensional B environment is a rank restriction on the physical channel, not a restriction to calibrated perturbations.

At rank four the new B sector can have two rows. Then D*D may be nonzero scalar, the coefficient in (18) vanishes, and the exact compensated-marker paths of section 87 give higher-rank quarter-attainers. Thus the strict tail conclusion (3) cannot be extended to rank four with the same positive tail term. This obstruction does not exhibit a subquarter channel and does not decide whether a weaker unrestricted local minimum holds. The unrestricted quarter-optimum problem remains open.

## 89. An unrestricted local quarter minimum from analytic descent at the scalar cone

This section proves a path-free local theorem for the original product channels, with arbitrary Kraus rank and original output leakage on both sides. It uses the full comparison Hessian theorem of [section 86](ARITHMETIC_HOLOGRAPHIC_RT_II.md#86-local-quartic-stability-from-the-rank-two-ky-fan-minimum-manifold), the all-disphenoid minimized coefficient of [section 87](ARITHMETIC_HOLOGRAPHIC_RT_II.md#87-exact-anisotropic-quartic-coercivity-at-every-disphenoid-equality-pair), and the flat-noise and gauge identities proved in [section 88](#88-a-path-free-local-quarter-minimum-for-a-party-of-kraus-rank-at-most-three). The analytic descent and scalar-cone remainder argument below are additional proof steps; nonnegative quartic coefficients alone would not imply the conclusion.

No unrestricted global optimum is asserted. The local center is any classified quarter-error pair with one party of Kraus rank two. The new theorem concerns all nearby channels, including ranks four and higher.

### 89.1. The local theorem and the original-channel witness

Let (A₀,B₀) be any original [section-82 quarter-error pair](ARITHMETIC_HOLOGRAPHIC_RT_II.md#82-quarter-error-rigidity-minimal-kraus-product-and-the-complete-rank-two-party-family) of CPTP maps C⁸→C⁴, with B₀ of Kraus rank two. Then there is a neighborhood U of (A₀,B₀) in the finite-dimensional space of channels such that

\[
 \delta(A,B)\ge\frac14\qquad ((A,B)\in U).                 \tag{1}
\]

Here δ is the original unhalved arbitrary-reference diamond error from the fixed four-fibre RT target. Neither perturbed party has a Kraus-rank restriction. The roles of A and B may be exchanged. This proves an unrestricted local minimum at these particular equality pairs, not a global minimum or a classification of all possible remote quarter-error pairs.

Use forward Grams of the correct-output records of the full original Stinespring isometries. Set K=G⊙H and let T have diagonal blocks I₂ and all off-diagonal blocks J₂/2. Define

\[
 f(A,B)=\frac14\Lambda_2(T-K),\qquad
 \delta(A,B)\ge\frac14\operatorname{Tr}(T-K)_+\ge f(A,B).
                                                               \tag{2}
\]

The first inequality follows from the normalized maximally entangled logical/reference input. Its correct joint reference/output compression is Kᵀ/8 on {|f,i〉_R⊗|ff〉_out}. Pinching retains the complementary positive trace 1−Tr K/8 and gives (‖K−T‖₁+8−Tr K)/8=Tr(T−K)₊/4. Thus wrong outputs and their cross-sector coherences have not been silently calibrated away.

At the base, the top two eigenvalues of T−K are 1/2,1/2 and the other six are at most zero, including boundary disphenoids. Hence f is real-analytic in a fixed neighborhood. It is enough to prove that f≥1/4 there on physical Stinespring isometries in fixed sufficiently large environments.

### 89.2. Analytic comparison coordinates and the flat kernel

Fix A-environment dimension d≥4 and B-environment dimension 2+p, where p≥2. Every nearby B-isometry has the unique old/new polar representation

\[
 V_B=U\sqrt{I-R^*R}\ \oplus\ R,
 \quad U\in U(8),\quad
 R:\mathbb C^8\longrightarrow\mathbb C^4\otimes\mathbb C^p.
                                                               \tag{3}
\]

Indeed its old square block is invertible near the base. Both its polar factor and the positive square root in (3) are real-analytic. The comparison point x=(V_A,U) belongs to
X=St(C⁸,C⁴⊗Cᵈ)×U(8).

Section 86 supplies a local minimum manifold M⊂X, with f(m,0)=1/4, df(m,0)=0, and old Hessian kernel exactly TM. Its normal Hessian is positive definite, with all A-environment and original leakage directions included. In calibrated notation its points are

\[
 \begin{gathered}
 C_f=S+\tfrac12 WN_f,\qquad \sum_fN_f=0,\qquad
 N_f=\overline{B_f}ZB_f^T,\quad Z=\operatorname{diag}(1,-1),\\
 S^*S=(\tfrac12-h/8)I_2,\quad W^*W=(h/2)I_2,\quad
 S^*W=i\beta I_2,\quad h\sim\tfrac12,\quad\beta\sim0.
 \end{gathered}                                             \tag{4}
\]

The manifold is real-analytic, not merely smooth: [S W] is a Stiefel frame times the positive square root of its positive-definite 4×4 scalar-block Gram; balance is a real-analytic regular constraint, whose differential is surjective because the four Bloch axes span three dimensions. The recovery of all these parameters is analytic. Choose an analytic normal frame locally and an analytic Stiefel polar retraction. The inverse function theorem then gives real-analytic coordinates x=χ(m,n), with n=0 precisely on M. In particular no analyticity of an unspecified nearest-point projection is assumed.

At m define the tight fixed-bit matrices

\[
 B_i^m=[b_{1i},\ldots,b_{4i}],\quad B_i^m(B_i^m)^*=2I_2,
 \quad P_i^m=(B_i^m)^*B_i^m/2.                            \tag{5}
\]

For each new environment coordinate, extract the four correct-output bit-i entries of R; together they form a p×4 matrix R_i. All other entries form R_wrong. The exact quadratic noise coefficient is

\[
 L_m(R)=\frac18\left(\|R_{\rm wrong}\|_F^2+
                    \sum_i\|R_i(I-P_i^m)\|_F^2\right).
                                                               \tag{6}
\]

This is the rowwise extension of section 88: the old attenuation contributes Tr(R*R)/8 and the new correct Gram contributes −Σ_i‖R_iP_i^m‖²/8. Its complex kernel consists exactly of calibrated records r_fi=L_i b_fi with L_i∈C^{p×2}.

Let Π_m be the analytic orthogonal projection onto this kernel. For an arbitrary R, its kernel coefficients are L_i=R_i(B_i^m)*/2. Put

\[
 S_R=L_0+L_1,\qquad D_R=L_1-L_0,\qquad
 R_\perp=(I-\Pi_m)R.
                                                               \tag{7}
\]

Then L_m(R)=‖R_perp‖²/8 and ‖R‖²=‖R_perp‖²+‖S_R‖²+‖D_R‖². The p×2 matrix S_R is a physical environment-gauge coordinate. We next remove it exactly, rather than treating it as a small remainder.

### 89.3. An exact common-component-zero gauge slice

For Z∈C^{p×2}, apply the physical B-environment unitary

\[
 \exp\Omega(Z),\qquad
 \Omega(Z)=\begin{bmatrix}0&-Z^*\\Z&0\end{bmatrix},       \tag{8}
\]

identically on each output. Re-form the old polar unitary U′ and new block R′, set x′=(V_A,U′), and let m′ be the analytic m-coordinate of x′. Define the p×2 real-analytic map Φ(Z;x,R)=S_{R′}, where the latter coefficients are extracted relative to m′.

At x=m and R=0, Φ(0;m,0)=0 and

\[
 d_Z\Phi(0;m,0)[Z]=2Z.                                  \tag{9}
\]

To see the derivative, the old block has no linear change and the new block is ZU_m. Its correct records are Zb_fi, so L₀=L₁=Z. Changes of m′ make no first-order contribution because R′=0 at the evaluation point. The real-analytic inverse function theorem gives, for every nearby (x,R), a unique small Z producing S_{R′}=0. This is a gauge of the same physical channel and leaves A unchanged. No physical channel transfer or error-monotone polar replacement is asserted.

The construction is equivariant under a residual new-environment unitary V∈U(p). The transformation R↦(I₄⊗V)R leaves U and x unchanged, and sends S_R,D_R to VS_R,VD_R. Moreover Ω(VZ)=diag(I₂,V)Ω(Z)diag(I₂,V)*. Thus Φ(VZ;x,VR)=VΦ(Z;x,R), and uniqueness makes the solved gauge equivariant.

On this exact slice write D=D_R. Its flat part has records

\[
 r_{f0}=-\tfrac12 D b_{f0},\qquad
 r_{f1}= \tfrac12 D b_{f1}.                              \tag{10}
\]

Choose an analytic orthonormal complex frame for the complement of Π_m on the one-new-coordinate space, and use the same frame in every new row. This identifies R_perp with Q∈C^{p×28}, isometrically and U(p)-equivariantly. Hence the gauge-fixed physical tuples have exact analytic coordinates (m,n,D,Q); every sufficiently nearby tuple has such a representation. The residual action is

\[
 (m,n,D,Q)\longmapsto(m,n,VD,VQ).                         \tag{11}
\]

Neither the gauge choice nor the frame for Q changes the fixed target bit basis.

### 89.4. Simultaneous minimization of all genuinely normal variables

Set y=(n,Q), viewed as a real vector. At D=0,y=0 the Hessian in y is positive definite: its n-block is the full old normal Hessian; its Q-block is the positive quadratic form ‖Q‖²/8; there is no mixed n,Q block because f is invariant under simultaneous sign reversal of all new records. The kernel identities in (6) also give no mixed y,D Hessian block.

The analytic implicit-function theorem, followed by uniform normal convexity, supplies a unique analytic critical point y_*(m,D), with

\[
 f(m,y,D)\ge \psi(m,D)+a\|y-y_*(m,D)\|^2,
 \qquad \psi(m,D)=f(m,y_*(m,D),D),\quad a>0.              \tag{12}
\]

All estimates hold on a fixed sufficiently small product neighborhood. In particular they are uniform neighborhood estimates, not limits along chosen paths.

Uniqueness and (11) imply

\[
 n_*(m,VD)=n_*(m,D),\quad Q_*(m,VD)=VQ_*(m,D),\quad
 \psi(m,VD)=\psi(m,D).                                  \tag{13}
\]

Differentiation at D=0 and the absent mixed Hessian give dy_*/dD=0. The sign symmetry then gives n_*=O(‖D‖²) and Q_*=O(‖D‖³). Consequently minimizing Q has no effect on the degree-four coefficient. At the base the degree-four coefficient of ψ is exactly the section-87 minimized form, with D equal to the difference in (7):

\[
 \psi(m_0,D)=\frac14+\sum_{a=1}^3c(u_a)r_a^2+O(\|D\|^6),
 \quad \overline{D^*D}=r_0I_2+\sum_ar_a\sigma_a,
 \quad c(u)=\frac{(1-u)(7u-1)^2}{256u^2}.
                                                               \tag{14}
\]

Here u_a≥2/7 and Σu_a=1, so c(u_a)≥35/1024. The use of the symmetric records (10), instead of the section-87 records 0,D b_f1, is justified by the exact order-four gauge identity of section 88. Its proof works verbatim with a p×2 common coefficient in (8); it translates the full old tangent space bijectively, and terms of order three in the new amplitude do not affect the quartic coefficient on the quadratic kernel. No normal, leakage, or extra A direction is left outside the minimization in (12).

### 89.5. Analytic descent through D↦D*D, including its singular vertex

We prove the precise invariant-analytic fact needed here. Let ψ(m,D) be jointly real-analytic near (m₀,0), for D∈C^{p×2}, p≥2, and invariant under U(p) acting on the left. Then there is a jointly real-analytic function g(m,E), defined for all Hermitian 2×2 matrices E in an open neighborhood of zero, such that

\[
 \psi(m,D)=g(m,D^*D).                                    \tag{15}
\]

In particular the domain of g is not restricted to the singular positive-semidefinite cone.

To prove this, complexify D and its conjugate to independent p×2 matrices Z,W. The convergent power series of ψ groups into homogeneous polynomials. Scalar unitary invariance forces each surviving term to have equal degree k in Z and W. Each such polynomial P_k is U(p)-invariant under (Z,W)↦(VZ,bar(V)W).

The infinitesimal action of the skew-Hermitian matrices annihilates P_k. Its complex-linear extension is the action of all of gl(p,C), since the complex span of the skew-Hermitian matrices is gl(p,C). Exponentiation and connectedness of GL(p,C) therefore give invariance under (Z,W)↦(AZ,A^{-T}W).

Let J=[I₂;0]. On the dense set where Z has rank two and WᵀZ is invertible, choose A taking Z to J. The first two rows of the transformed W are (WᵀZ)ᵀ. The stabilizer of J consists of blocks [[I₂,C],[0,B]]; its inverse-transpose action can remove every remaining row of W because the first two rows form an invertible matrix. Thus the transformed pair is exactly (J,[Eᵀ;0]), where E=WᵀZ. It follows that

\[
 P_k(Z,W)=q_k(W^TZ),\qquad
 q_k(E):=P_k(J,[E^T;0]),                                 \tag{16}
\]

first on that dense set and hence as a polynomial identity everywhere. Each q_k is homogeneous of degree k. This argument includes p=2, for which there are no remaining rows to remove.

It remains essential to prove convergence. Choose a fixed nonzero complex number t small enough that Z=tJ lies strictly inside the convergence neighborhood of the complexified series. For E sufficiently small, W=t^{-1}[Eᵀ;0] also lies inside that neighborhood. Equal bidegrees give

\[
 P_k(tJ,t^{-1}[E^T;0])=q_k(E).                           \tag{17}
\]

Therefore Σ_k q_k(E) converges normally on a full complex neighborhood of E=0, uniformly also on a smaller m-neighborhood. It defines the analytic g. Substitution in the original convergent series proves (15). Its restriction to Hermitian E is real: each homogeneous coefficient is real on positive-definite Hermitian E by the original reality of ψ, and thus on all Hermitian E by a real polynomial identity. This proves analytic descent and derivative control at the vertex, rather than appealing to smooth invariance alone.

Apply this lemma to (13). From (14), the quadratic part of g(m₀,E) on traceless Hermitian E is

\[
 q(E)=\sum_ac(u_a)r_a^2
     \ge\frac{35}{2048}\|E\|_F^2,
 \qquad \overline E=\sum_ar_a\sigma_a,\quad\operatorname{Tr}E=0.
                                                               \tag{18}
\]

### 89.6. Exact stationarity on every nearby scalar cone

Fix any nearby m∈M and D with D*D=λI₂, λ≥0 small. In (10), the two records of each fibre are orthogonal with squared norms λ/4. Different fibres have different output labels. Hence

\[
 R^*R=\frac\lambda4 I_8,\qquad
 V_B=\sqrt{1-\lambda/4}\,U_m\ \oplus\ R.                \tag{19}
\]

When λ>0 write D=√λ J_D with J_D*J_D=I₂. This B channel has the same qubit core b_fi in two isometric environment copies, with normalized bit markers of overlap

\[
 \tau=1-\lambda/2.                                      \tag{20}
\]

For m define T_i=√2(S+(−1)^iW/2). Equations (4) give T_i^*T_i=I₂ and T₀^*T₁=ηI₂, with η=1−h/2−2iβ. Thus a_fi=T_i conjugate(b_fi). The fixed-bit Gram of each party is a rank-two tight-frame Gram with nonzero eigenvalues 2,2, regardless of η and λ. The cross-bit product entries are ητ|〈b_f0,b_g1〉|².

Let P₀=(J₄/4)⊗I₂. Tightness gives row and column sums two for each matrix of squared overlaps, including the cross-bit one. Hence P₀ is invariant under T−K, and its compression in the two uniform bit vectors is

\[
 \begin{bmatrix}
  1/2&3/2-2\eta\tau\\
  3/2-2\overline\eta\tau&1/2
 \end{bmatrix}.                                         \tag{21}
\]

Its trace is one. The top-cluster gap persists uniformly near the original base, so (21) is still the top two-dimensional cluster. Consequently f=1/4 for every nearby m and every sufficiently small scalar D*D. This assertion includes complex marker overlaps; no restriction β=0 is used.

These points are stationary in every original-channel Stinespring direction. Indeed, if either party is fixed at such a point, its two fixed-bit Grams H_i satisfy H_i≤2I₄. For any original other party with correct-bit Grams G_i, positivity and Tr G_i≤4 give

\[
 \operatorname{Tr}(P_0K)
   =\frac14\sum_i\operatorname{Tr}(G_iH_i^T)\le4,
 \quad \operatorname{Tr}(P_0T)=5,
 \quad f\ge\frac14.                                    \tag{22}
\]

Equality at the point and differentiability imply zero derivative in each party separately, hence in the full product of Stinespring manifolds. This includes arbitrary original leakage and larger A environments.

In the slice coordinates the scalar points have y=0 exactly. By the uniqueness of the normal critical point in (12),

\[
 y_*(m,D)=0,\qquad \psi(m,D)=\frac14
      \quad\text{whenever }D^*D=\lambda I_2.             \tag{23}
\]

For λ>0 the derivative of D↦D*D at D=√λ J_D is onto the real space of Hermitian 2×2 matrices: use δD=J_D H/(2√λ) for a prescribed Hermitian H. Full stationarity, (15), and the chain rule therefore imply

\[
 g(m,\lambda I_2)=\frac14,\qquad d_Eg(m,\lambda I_2)=0.
                                                               \tag{24}
\]

The same identities at λ=0 follow by continuity. Thus the required vanishing of the reduced gradient is proved on every nearby scalar ray, not inferred from the existence of a few equality paths.

### 89.7. A uniform anisotropy remainder estimate and local positivity

Fix any number 0<κ<35/2048. By (18), joint analyticity, and continuity of the Hessian, shrink the m,E-neighborhood so that for every traceless Hermitian H,

\[
 \frac12 d_E^2g(m,E)[H,H]\ge\kappa\|H\|_F^2.             \tag{25}
\]

For a physical D put E=D*D, λ=Tr(E)/2 and E₀=E−λI₂. The segment λI₂+sE₀, 0≤s≤1, remains inside the chosen neighborhood. Taylor's formula with integral remainder based at the scalar point, using both identities in (24), gives the exact estimate

\[
 \begin{split}
 \psi(m,D)-\frac14
  &=\int_0^1(1-s)\,
      d_E^2g(m,\lambda I_2+sE_0)[E_0,E_0]\,ds\\
  &\ge\kappa\|D^*D-\tfrac12\operatorname{Tr}(D^*D)I_2\|_F^2.
 \end{split}                                             \tag{26}
\]

Together with (12), this proves the uniform gauge-slice bound

\[
 f(m,y,D)\ge\frac14+a\|y-y_*(m,D)\|^2
       +\kappa\|D^*D-\tfrac12\operatorname{Tr}(D^*D)I_2\|_F^2.
                                                               \tag{27}
\]

This is the needed remainder control relative to the scalar cone. An uncontrolled O(‖D‖⁶) term has not been dropped or absorbed into a quartic expression that vanishes there. Instead the exact scalar value and first derivative force the full remainder to be quadratic in the anisotropy.

The local zero set of this witness is exactly y=0 with D*D scalar, by (23) and (27). It is a set of witness minima; the full diamond equality set is a subset, since M allows additional complex marker parameters. If desired, (27) also implies a quartic distance bound to this witness-minimum set in these local coordinates. Indeed, if the singular values of D are s₁,s₂, its squared distance to the scalar-Gram cone is (s₁−s₂)²/2, whereas the squared anisotropy is (s₁²−s₂²)²/2 and is at least twice the fourth power of that distance. The smooth y_* vanishes on the cone, so it introduces only a bounded local Lipschitz factor in this distance comparison.

### 89.8. All physical ranks, exact quarter paths, and the global boundary

For an arbitrary original channel use the canonical Choi square-root Kraus decomposition, in fixed environment dimension 32. It is continuous at rank changes. A fixed environment unitary aligns the base support of B with the old two coordinates and embeds A's rank-four base support in its 32 coordinates. Thus every sufficiently nearby physical channel pair has lifts in the above Stinespring neighborhood with d=32 and p=30. The old B square block remains invertible. The exact gauge slice in section 89.3 then applies. No spectral eigenvector selection, differentiable path, Choi-rank restriction, or calibration of the physical channels is needed. Combining (27) with (2) proves (1).

There are genuine higher-rank quarter-attainers on the scalar cone. Start with a classified balanced qubit frame and original marker overlap η=3/4. Use the scalar B markers from (19)–(20) and change A's scalar overlap to (3/4)/τ. For small λ≥0 this is a permissible overlap of normalized marker vectors. The product Gram K is then exactly the original equality Gram, so the entire original reference-sensitive channel error remains 1/4. This explains the scalar zero modes without discarding them. It does not make all points in the larger witness-minimum manifold full diamond attainers.

The proof is local at every section-82 equality member and includes its boundary disphenoids, because the spectral gap, balance regularity, old normal coercivity, and positive coefficient bound hold there. It establishes no lower bound of 1/4 for arbitrary distant product channels. The unrestricted global quarter-optimum problem remains open.

## 90. An exact qutrit product separating global Gram certificates from diamond error

**Proposition 90.1 (exact global certificate limitations; repo-derived).** There are original CPTP channels A,B:C⁸→C⁴, both calibrated on the four fixed fibres and both of Kraus rank three, for which the forward record Grams G,H satisfy Λ₂(T−G⊙H)=(1+√7)/4<1 and ‖G⊙H−T‖₁=(1+√7)/2<2, while the original unhalved arbitrary-reference diamond error is δ(A,B)=(1+2√2)/7>1/2. Here T has diagonal blocks I₂ and off-diagonal blocks J₂/2, and Λ₂ denotes the sum of the two largest eigenvalues. Thus these two proposed unrestricted global Gram inequalities cannot furnish a universal quarter diamond lower bound.

This proposition concerns the limitations of these specific certificates. It does not give a product with diamond error below 1/4. The [local quarter-minimum theorem](#89-an-unrestricted-local-quarter-minimum-from-analytic-descent-at-the-scalar-cone) has its stated neighborhood hypothesis, and the unrestricted global quarter-optimum problem remains open.

### 90.1. Original physical channels and the complete product Gram

**Proof.** Let e₀,e₁,e₂ be the standard basis of C³ and put u=(e₁+e₂)/√2. Define four local orthonormal two-frames by

\[
 \begin{array}{ll}
 b_{10}=(e_0+e_1)/\sqrt2,&b_{11}=(e_0-e_1)/\sqrt2,\\
 b_{20}=(e_0+iu)/\sqrt2,&b_{21}=(e_0-iu)/\sqrt2,\\
 b_{30}=u,&b_{31}=e_0,\\
 b_{40}=(e_0+e_2)/\sqrt2,&b_{41}=(e_0-e_2)/\sqrt2.
 \end{array}                                               \tag{1}
\]

Set a_fi=conjugate(b_fi). On the eight-dimensional local input with fixed basis |f,i〉, define Stinespring isometries

\[
 V_A|f,i\rangle=|f\rangle\otimes a_{fi},\qquad
 V_B|f,i\rangle=|f\rangle\otimes b_{fi}.                    \tag{2}
\]

Each within-fibre frame in (1) is orthonormal, and different fibres in (2) have orthogonal output labels. Hence V_A*V_A=V_B*V_B=I₈. Tracing the C³ environments gives original CPTP channels A,B:C⁸→C⁴. The environment records span C³. The associated three Kraus operators are linearly independent, because a linear relation between them annihilates every record; thus each physical channel has Kraus rank exactly three. Equivalently the local frame operator has eigenvalues 4,3,1.

Let H be the forward Gram of the b records, G=conjugate(H), and K=G⊙H. All 2×2 diagonal blocks of G,H are I₂, and K_fi,gj=|〈b_fi,b_gj〉|². In the ordered basis (10,11,20,21,30,31,40,41), the entire product Gram is

\[
 K=\frac18
 \begin{bmatrix}
 8&0&3&3&2&4&2&2\\
 0&8&3&3&2&4&2&2\\
 3&3&8&0&4&4&3&3\\
 3&3&0&8&4&4&3&3\\
 2&2&4&4&8&0&2&2\\
 4&4&4&4&0&8&4&4\\
 2&2&3&3&2&4&8&0\\
 2&2&3&3&2&4&0&8
 \end{bmatrix}.                                           \tag{3}
\]

The target T has diagonal blocks I₂ and off-diagonal blocks J₂/2. Therefore its full difference from this product Gram is

\[
 L:=T-K=\frac18
 \begin{bmatrix}
 0&0&1&1&2&0&2&2\\
 0&0&1&1&2&0&2&2\\
 1&1&0&0&0&0&1&1\\
 1&1&0&0&0&0&1&1\\
 2&2&0&0&0&0&2&2\\
 0&0&0&0&0&0&0&0\\
 2&2&1&1&2&0&0&0\\
 2&2&1&1&2&0&0&0
 \end{bmatrix}.                                           \tag{4}
\]

No plus/minus or cross-fibre block is omitted.

### 90.2. Complete spectrum and the two global certificate limitations

In the logical coefficient space define orthonormal vectors
c₁=(|1,0〉+|1,1〉)/√2, c₂=(|2,0〉+|2,1〉)/√2, c₃=|3,0〉, c₄=(|4,0〉+|4,1〉)/√2. The orthogonal complement of their span is in ker L. In this four-dimensional span, L is the matrix

\[
 M=\begin{bmatrix}
 0&1/4&\sqrt2/4&1/2\\
 1/4&0&0&1/4\\
 \sqrt2/4&0&0&\sqrt2/4\\
 1/2&1/4&\sqrt2/4&0
 \end{bmatrix}.                                           \tag{5}
\]

The vector t=(c₁−c₄)/√2 has eigenvalue −1/2, and z=(−√2c₂+c₃)/√3 has eigenvalue zero. On the remaining orthonormal pair r=(c₁+c₄)/√2 and w=(c₂+√2c₃)/√3 the matrix is

\[
 \begin{bmatrix}1/2&\sqrt6/4\\\sqrt6/4&0\end{bmatrix},
 \qquad \lambda_\pm=\frac{1\pm\sqrt7}{4}.                \tag{6}
\]

Normalized eigenvectors for λ_± are (λ_±r+(√6/4)w)/√(λ_±²+3/8). Together with t, z, the three minus-bit vectors of fibres 1,2,4, and |3,1〉, this is a complete orthonormal eigenbasis. In particular

\[
 \det(sI_8-L)
   =\frac{s^5(2s+1)(8s^2-4s-3)}{16},\qquad
 \operatorname{spec}(L)=
 \left\{\frac{1+\sqrt7}{4},\frac{1-\sqrt7}{4},-\frac12,0^{\times5}\right\}.
                                                               \tag{7}
\]

There is exactly one positive eigenvalue. Consequently

\[
 F(A,B):=\frac14\Lambda_2(L)=\frac{1+\sqrt7}{16}<\frac14,
 \qquad
 \|G\odot H-T\|_1=\frac{1+\sqrt7}{2}<2.                 \tag{8}
\]

The inequalities follow from √7<3. Since Tr L=0, the normalized maximally entangled logical/reference input has unhalved error ‖L‖₁/8=(1+√7)/16. It is therefore below 1/4 for this pair. This input-specific value is not the diamond error.

### 90.3. A normalized coherent input gives error one half

Let the fixed logical input encoding be |f,i〉↦|f,i〉_A⊗|f,i〉_B, and let the target output encoding be |f〉↦|ff〉. The original product and target are calibrated into that output code. For a coefficient matrix C define the logical map

\[
 \mathcal M_C(|f,i\rangle\langle g,j|)
      =C_{fi,gj}|f\rangle\langle g|.                      \tag{9}
\]

Because the product Gram (3) is real symmetric, the original encoded channel difference is exactly −M_L followed by the output encoding. The usual forward-Gram transpose therefore causes no convention change here.

The normalized no-reference input

\[
 |\psi_0\rangle=\frac12
 (|1,0\rangle+|1,1\rangle+|4,0\rangle+|4,1\rangle)
                                                               \tag{10}
\]

has output difference −(|1〉〈4|+|4〉〈1|)/4, and hence unhalved trace norm 1/2. The output encoding preserves this norm. Thus δ(A,B)≥1/2 already, despite both inequalities in (8).

### 90.4. Exact arbitrary-reference diamond error

The full norm can also be computed, without restricting the reference. Set

\[
 \mu=\frac1{2(2\sqrt2-1)},\qquad
 v=c_1+\frac1{\sqrt2}c_2+c_3+c_4,\qquad
 Z=2\mu vv^*-L.                                         \tag{11}
\]

We claim Z≥±L. The inequality Z+L≥0 is immediate. For the other one it is enough to check μvv*−L≥0. This matrix vanishes on ker L, equals 1/2 on t, and in the r,w coordinates of section 90.2 is

\[
 \begin{bmatrix}
 2\mu-1/2&\sqrt3\mu-\sqrt6/4\\
 \sqrt3\mu-\sqrt6/4&3\mu/2
 \end{bmatrix}.                                         \tag{12}
\]

Both diagonal entries are positive and its determinant is zero, using μ=1/[2(2√2−1)]. Hence (12) is positive semidefinite, proving the claim. Since every diagonal fibre block of L is zero,

\[
 Z_{ff}=2\mu v_fv_f^*\le2\mu I_2;
 \qquad (\|v_1\|^2,\|v_2\|^2,\|v_3\|^2,\|v_4\|^2)
          =(1,1/2,1,1).                                 \tag{13}
\]

For any positive-semidefinite coefficient matrix C, the map M_C is completely positive: its Choi matrix is an isometric embedding of C on {|f,i〉_reference⊗|f〉_output}. Thus Z±L≥0 imply M_Z±M_L are completely positive. Moreover (13) says M_Z*(I)≤2μI₈; explicitly this adjoint effect is the block-diagonal matrix with blocks Z_ffᵀ, which obey the same bound.

For every normalized positive reference/input state ρ, set X=(id⊗M_L)(ρ), Y=(id⊗M_Z)(ρ). Then −Y≤X≤Y and Y≥0. If P₊ and P₋ are the positive and negative spectral projections of X, the order bounds give ‖X‖₁≤Tr((P₊+P₋)Y)≤Tr Y≤2μ. This is a bound on the actual 8→4 map, valid for every reference dimension. To pass from states to the defining diamond-norm optimization, first use the Jordan decomposition of any Hermitian input Q to obtain ‖(id⊗M_L)(Q)‖₁≤2μ‖Q‖₁. For a general input X, apply that bound after adjoining one reference qubit to the Hermitian dilation [[0,X],[X*,0]]/2; its trace norm is ‖X‖₁, and the output dilation has trace norm ‖(id⊗M_L)(X)‖₁. Thus δ(A,B)≤2μ for the full diamond norm.

For a matching lower bound put

\[
 q=\frac{\sqrt2}{2\sqrt2-1},\qquad
 p=(q/2,0,1-q,q/2),\qquad
 |\psi\rangle=\sqrt{p_1}c_1+\sqrt{p_3}c_3+\sqrt{p_4}c_4.
                                                               \tag{14}
\]

The numbers p_f are nonnegative and sum to one. Thus |ψ〉 is a normalized logical input with no reference. Its output difference is minus D_p M D_p, where D_p=diag(√p₁,…,√p₄) and M is (5). Direct substitution gives (Mp)_f=μ at every f for which p_f>0. Hence the unit vector (√p_f)_f is an eigenvector of D_p M D_p with eigenvalue μ. Congruence cannot increase the number of positive eigenvalues, so this matrix has exactly one positive eigenvalue, and its trace is zero. Its trace norm is therefore 2μ, attaining the upper bound. We have proved

\[
 \boxed{\displaystyle
 \delta(A,B)=2\mu=\frac1{2\sqrt2-1}=\frac{1+2\sqrt2}{7}>\frac12.}
                                                               \tag{15}
\]

This exact full-reference value makes the distinction from (8) quantitative.

### 90.5. Scope of the certificate obstruction

**Corollary 90.2.** Neither Λ₂(T−G⊙H)≥1 nor ‖G⊙H−T‖₁≥2 holds for all original product channels, even when both local record matrices consist of four exact orthonormal two-frames. The two assertions remain false when restricted to pairs of Kraus ranks exactly (3,3).

**Proof.** The product Gram in (3) comes from the original isometries (2), and (8) violates both assertions. In particular no relaxation to independently chosen contraction blocks is needed.

The [rank-two-party lower bounds](ARITHMETIC_HOLOGRAPHIC_RT_II.md#81-a-subnormalized-centroid-support-witness-for-original-local-environment-bounds), [rank-two-party equality classification](ARITHMETIC_HOLOGRAPHIC_RT_II.md#82-quarter-error-rigidity-minimal-kraus-product-and-the-complete-rank-two-party-family), and subsequent one-sided, qubit-core, curvature and local results retain their stated hypotheses. Both parties in (2) have rank three, so the example lies outside the rank-two-party hypothesis. Section 89 supplies a lower bound in a neighborhood of the classified rank-two-side equality pairs, whereas (8) disproves an unrestricted global extension of the witness. Moreover the full diamond error (15) exceeds 1/4, so this example does not violate that local diamond lower bound even if tested without reference to its neighborhood hypothesis.

For this pair, the normalized maximally entangled logical/reference input gives (1+√7)/16, while the coherent inputs (10) and (14) give respectively 1/2 and (1+2√2)/7. Thus a global quarter proof must retain sufficient input optimization, or a different full-reference dual bound, to distinguish these values. No conclusion about the existence of a subquarter original product follows from the failure of the two Gram certificates.

## 91. Adaptive original-channel witnesses and an obstruction to all two-fibre tests

The separation in section 90 leaves open whether the uniform-reference witness becomes sufficient after adding every two-fibre coherent test. This section gives an exact physical counterexample to that stronger assertion. It also derives an input-adaptive correct-output witness that includes both tests, retains original leakage, and equals the full diamond norm when the original channels are calibrated. The unrestricted global quarter optimum remains open.

### 91.1. Original channels, forward Grams, and the adaptive theorem

The logical input has orthonormal basis |f,i〉, 1≤f≤4 and i∈{0,1}. The target channel ℱ:C⁸→C⁴ is

\[
 \mathcal F(|f,i\rangle\langle f,j|)=\delta_{ij}|f\rangle\langle f|,
 \qquad
 \mathcal F(|f,i\rangle\langle g,j|)=\tfrac12|f\rangle\langle g|
 \quad(f\ne g).
                                                               \tag{1}
\]

Keep the fixed correlated encodings V_in|f,i〉=|f,i〉⊗|f,i〉 and V_out|f〉=|f〉⊗|f〉, with encoding channels J_in and J_out. For arbitrary original CPTP maps A,B:C⁸→C⁴, put

\[
 \delta(A,B)=\|(A\otimes B)\circ J_{\rm in}
                    -J_{\rm out}\circ\mathcal F\|_\diamond.
                                                               \tag{2}
\]

The norm is unhalved and permits arbitrary reference systems and arbitrary operator inputs in its definition. No Kraus-rank bound or output-support restriction is imposed unless stated.

Choose Stinespring isometries V_A,V_B and define their correct-output records

\[
 a_{fi}=(\langle f|\otimes I)V_A|f,i\rangle,
 \qquad b_{fi}=(\langle f|\otimes I)V_B|f,i\rangle.
                                                               \tag{3}
\]

Let G,H be their forward Grams, with inner products conjugate-linear in the first argument, and put K=G⊙H. Let T have diagonal blocks I₂ and off-diagonal blocks J₂/2, and set L=T−K. The original encoded product uses the transpose of this forward Gram.

Define the compact set of fibre-block densities and the adaptive value

\[
 \begin{split}
 \mathcal D&=\{\rho=\bigoplus_{f=1}^4\rho_f:
                \rho_f\ge0,\ \sum_f\operatorname{Tr}\rho_f=1\},\\
 \mathcal B(L)&=\max_{\rho\in\mathcal D}
              2\operatorname{Tr}(\sqrt\rho L\sqrt\rho)_+.
 \end{split}                                             \tag{4}
\]

Here X₊ denotes the positive part of a Hermitian matrix X.

**Theorem 91.1.** For the original channels in (2), including arbitrary output leakage,

\[
 \delta(A,B)\ge\mathcal B(L).                            \tag{5}
\]

If both original channels are fibre-calibrated, meaning that V_A|f,i〉=|f〉⊗a_fi and V_B|f,i〉=|f〉⊗b_fi, then

\[
 \delta(A,B)=\mathcal B(L)
       =\max_{\rho\in\mathcal D}\|\sqrt\rho L\sqrt\rho\|_1.
                                                               \tag{6}
\]

In this calibrated case a reference of dimension at most two attains the diamond norm. The leakage-safe construction proving (5) uses a tagged reference and makes no corresponding reference-qubit assertion for arbitrary leaking channels.

The value in (4) has the exact primal and dual descriptions

\[
 \begin{split}
 \mathcal B(L)
   &=\max\{2\operatorname{Tr}(LW):\rho\in\mathcal D,
                                      \ 0\le W\le\rho\}\\
   &=\min\{t:Y\ge0,\ Y\ge2L,\ Y_{ff}\le tI_2
                                      \text{ for every }f\}.
 \end{split}                                             \tag{7}
\]

Both optima are attained. Under calibration the dual is equivalently

\[
 \mathcal B(L)=\min\{t:Z\ge L,\ Z\ge-L,
                              \ Z_{ff}\le tI_2\ \forall f\}.
                                                               \tag{8}
\]

Without calibration, the substitution Z=Y−L gives (Z+L)_ff≤tI₂, not the block constraint in (8).

### 91.2. Proof with the original leakage retained

The correct-output column map from either input fibre is a contraction, since it is a coordinate projection of the original Stinespring isometry restricted to that fibre. Thus G_ff,H_ff≤I₂. Positivity of Schur multiplication by H_ff gives

\[
 0\le K_{ff}\le I_2\odot H_{ff}
                 =\operatorname{diag}(H_{ff})\le I_2,
 \qquad L_{ff}\ge0.                                    \tag{9}
\]

These are properties of the actual channels, not a sufficient physical completion criterion for independently specified blocks.

Fix ρ∈𝒟 and set Q=√ρ. Use the normalized logical/reference state

\[
 |\Psi_\rho\rangle=\sum_{x,r}Q_{xr}|r\rangle_R\otimes|x\rangle,
 \qquad x=(f,i),\quad r=(g,j).
                                                               \tag{10}
\]

Its squared norm is Trρ=1. Since Q is fibre-block diagonal, every nonzero term has f=g. Project the reference and original physical output onto

\[
 P=\operatorname{span}\{|f,j\rangle_R\otimes|ff\rangle_{\rm out}:
                              1\le f\le4,\ j\in\{0,1\}\}.
                                                               \tag{11}
\]

In this orthonormal support, direct contraction of (10) gives target matrix (QTQ)ᵀ and actual compressed matrix (QKQ)ᵀ. The formulas hold for complex Q and K. The target lies entirely in P and has trace TrρT=1. The reference-fibre tag prevents wrong-output records from a different input fibre from entering this compression.

Pinch the difference into P and its orthogonal complement. The complementary actual block is positive with trace 1−TrρK. Transposition preserves trace norm, and pinching is trace-norm contractive on Hermitian matrices. Consequently

\[
 \begin{split}
 \delta(A,B)
   &\ge\|QLQ\|_1+1-\operatorname{Tr}(\rho K)\\
   &=\|QLQ\|_1+\operatorname{Tr}(QLQ)
     =2\operatorname{Tr}(QLQ)_+.
 \end{split}                                             \tag{12}
\]

Maximizing proves (5). In particular the complementary population has not been discarded, and no calibration or trace-zero assumption was used.

### 91.3. Exact calibrated norm and the reference dimension

For a coefficient matrix C define

\[
 \mathcal M_C(|f,i\rangle\langle g,j|)
       =C_{fi,gj}|f\rangle\langle g|.
                                                               \tag{13}
\]

At calibration the target-minus-product logical map is exactly ℳ_(Lᵀ), followed by the fixed output isometry. Consider any normalized pure reference/input state

\[
 |\psi\rangle=\sum_{f,i}|r_{fi}\rangle_R\otimes|f,i\rangle,
 \qquad \sum_{f,i}\|r_{fi}\|^2=1,
                                                               \tag{14}
\]

with no restriction on its reference dimension. Set V|f,i〉=|r_fi〉⊗|f〉. Its output difference is VLᵀV*, and

\[
 V^*V=S=\bigoplus_f S_f,\qquad
 (S_f)_{ij}=\langle r_{fi},r_{fj}\rangle,
 \qquad \operatorname{Tr}S=1.
                                                               \tag{15}
\]

The output labels force this block structure regardless of cross-fibre reference overlaps. Polar decomposition V=U√S preserves the nonzero spectrum on the support of S, including when S is singular. With ρ=Sᵀ it follows that

\[
 \|VL^TV^*\|_1
     =\|\sqrt S L^T\sqrt S\|_1
     =\|\sqrt\rho L\sqrt\rho\|_1,
 \qquad \rho\in\mathcal D.
                                                               \tag{16}
\]

Conversely, each 2×2 block ρ_fᵀ is the Gram of two vectors in C². All four factorizations may use the same reference C², because their cross-fibre overlaps do not enter (15). The resulting state (14) is normalized and realizes the value associated with ρ. Thus every value on the right of (6), including its maximum, is attainable with a reference qubit.

To pass from normalized states to the defining diamond norm, convexity first handles mixed positive inputs. A uniform bound for positive inputs and arbitrary references extends to Hermitian inputs by Jordan decomposition. For an arbitrary operator X, apply that Hermitian bound to

\[
 \frac12\begin{bmatrix}0&X\\X^*&0\end{bmatrix}
                                                               \tag{17}
\]

on one additional reference qubit. The dilation's input trace norm is ‖X‖₁ and its output trace norm equals the original output norm on X. This proves the full operator-input upper bound. Finally L_ff=0 at calibration, so TrρL=0 for every ρ∈𝒟 and the trace norm in (6) equals twice the positive-part trace. This proves (6).

Rank-one blocks ρ_f correspond exactly to scalar reference vectors, hence to pure no-reference inputs. This observation does not imply that rank-one blocks always maximize (6).

### 91.4. Primal, dual, and exact certificates

If 0≤W≤ρ, then W annihilates kerρ. Inverting √ρ on its support gives W=√ρ E√ρ with 0≤E≤I. Conversely every such E gives a feasible W. Standard positive-part duality therefore gives

\[
 \max_{0\le W\le\rho}\operatorname{Tr}(LW)
       =\operatorname{Tr}(\sqrt\rho L\sqrt\rho)_+,
                                                               \tag{18}
\]

proving the primal in (7).

The positive-semidefinite multiplier Y for ρ−W≥0 must satisfy Y≥0. Finiteness of the Lagrangian over W≥0 requires Y≥2L, and finiteness over block-diagonal ρ≥0 with trace one requires Y_ff≤tI₂. Thus the dual is exactly the second line of (7). The primal has a relative strictly feasible point ρ=I₈/8, W=I₈/16. The dual is strictly feasible with Y=cI₈, c>2‖L‖op, and t>c. Finite-dimensional semidefinite strong duality applies. The primal feasible set is compact. For the dual, bounded t and Y≥0 bound every diagonal entry and hence every matrix entry, so a bounded minimizing sequence has a feasible convergent subsequence. Both optima are attained.

For any feasible primal and dual tuples the exact gap is

\[
 \begin{split}
 t-2\operatorname{Tr}(LW)
  &=\sum_f\operatorname{Tr}[(tI_2-Y_{ff})\rho_f]\\
  &\quad+\operatorname{Tr}[Y(\rho-W)]
       +\operatorname{Tr}[(Y-2L)W].
 \end{split}                                             \tag{19}
\]

Each term is nonnegative. Matching feasible values therefore certify the optimum without approximation.

Under calibration, Z=Y−L satisfies Z≥±L and Z_ff=Y_ff, giving (8). This has a direct completely-positive interpretation. The Choi matrix of ℳ_C is the isometric embedding of C on {|f,i〉_reference⊗|f〉_output}, so C≥0 implies ℳ_C is CP. Thus Z±L≥0 make ℳ_Z±ℳ_L CP, and ℳ_Z*(I) has diagonal fibre blocks Z_ffᵀ≤tI₂. For the actual forward-Gram map use Zᵀ,Lᵀ, which preserve these inequalities. For any normalized positive reference/input state its error output X and majorant output Y′ obey −Y′≤X≤Y′ and TrY′≤t. The positive and negative spectral projections of X give ‖X‖₁≤TrY′. The Jordan and dilation argument of (17) then supplies the full diamond upper bound. This interpretation does not turn the calibrated formula (8) into an upper bound for the original leaking maps.

### 91.5. Uniform-reference and complete two-fibre tests

Taking ρ=I₈/8 in (4) gives Tr(L₊)/4. For any pair f≠g, choose unit vectors u,v such that u*L_fg v=‖L_fg‖op and take ρ_f=uu*/2, ρ_g=vv*/2, with other blocks zero. The nonzero compression of √ρL√ρ has off-diagonal entries ‖L_fg‖op/2 and nonnegative diagonal entries by (9). Adding the latter cannot decrease positive-part trace. Hence

\[
 \mathcal B(L)\ge
 \max\left\{\tfrac14\operatorname{Tr}L_+,
                     \max_{f<g}\|L_{fg}\|_{\rm op}\right\}.
                                                               \tag{20}
\]

At calibration the two selected diagonal entries vanish. More strongly, for calibrated channels the entire restriction of the original difference map to the sum of two input fibres has diamond norm exactly ‖L_fg‖op, allowing arbitrary references and arbitrary within-fibre bit amplitudes.

For completeness, write D=L_fg and q=‖D‖op. For q>0 the coefficient matrix

\[
 \begin{bmatrix}I_2&D/q\\D^*/q&I_2\end{bmatrix}\ge0
                                                               \tag{21}
\]

defines a CPTP two-fibre coefficient-collapse channel. Composing it with the output off-diagonal map O(X)=(X−σ_zXσ_z)/2 gives the two-fibre difference divided by q, up to the forward-Gram transpose. The diamond norm of O is one: the two-unitary-channel triangle inequality gives the upper bound, and |+〉 attains it. Singular vectors of D give a normalized equal-weight two-fibre input with output coherences q/2 and hence trace norm q. This proves the exact norm identity; q=0 is immediate. The fixed correlated output isometry preserves the norm. This is the two-fibre identity of [section 65](ARITHMETIC_HOLOGRAPHIC_RT_II.md#65-exact-unrestricted-common-channel-projection-for-two-collapsed-fibres), here used for the actual restricted channels.

### 91.6. A physical trine-qutrit family

Let 0≤t≤1, let e₀,e₁,e₂ be an orthonormal basis of C³, and put ω=(−1+i√3)/2. For j=0,1,2 define

\[
 \begin{split}
 u_j&=\sqrt{1-t}\,e_1+\sqrt t\,\omega^j e_2,\\
 b_{j+1,0}&=(e_0+u_j)/\sqrt2,
 &b_{j+1,1}&=(e_0-u_j)/\sqrt2,\\
 b_{4,0}&=e_2,&b_{4,1}&=e_0,
 \qquad a_{fi}=\overline{b_{fi}}.
 \end{split}                                             \tag{22}
\]

Use the original isometries V_A|f,i〉=|f〉⊗a_fi and V_B|f,i〉=|f〉⊗b_fi. Each within-fibre pair is orthonormal, and different fibres have distinct output labels, so these are genuine CPTP maps C⁸→C⁴. They are calibrated by construction. Their record frame operators are

\[
 \sum_{f,i}b_{fi}b_{fi}^*
      =\operatorname{diag}(4,3(1-t),1+3t),
                                                               \tag{23}
\]

and the same matrix for a. For 0<t<1 the records span C³. A linear dependence among the three environment-indexed Kraus operators would annihilate every record; hence both local Kraus ranks are exactly three.

The product Gram is real with entries K_fi,gj=|〈b_fi,b_gj〉|². Its diagonal blocks are I₂. For distinct outer fibres f,g≤3 and for f≤3 its remaining blocks are

\[
 \begin{split}
 K_{fg}&=\begin{bmatrix}a&b\\b&a\end{bmatrix},
 &a&=1-\tfrac32t+\tfrac34t^2,
 &b&=\tfrac34t^2,\\
 K_{f4}&=\begin{bmatrix}t/2&1/2\\t/2&1/2\end{bmatrix},
 &K_{4f}&=K_{f4}^*.
 \end{split}                                             \tag{24}
\]

These formulas specify the entire Gram. For example 〈u_j,u_k〉=1−t+tω^(k−j), and the outer entries are |1±〈u_j,u_k〉|²/4.

Define outer plus and minus inputs c_f=(|f,0〉+|f,1〉)/√2 and d_f=(|f,0〉−|f,1〉)/√2, for f=1,2,3. In the full orthonormal ordered basis

\[
 (c_1,c_2,c_3,|4,0\rangle;
                  d_1,d_2,d_3,|4,1\rangle)
                                                               \tag{25}
\]

the complete matrix L=T−K becomes M⊕N, where

\[
 \begin{gathered}
 M=\begin{bmatrix}r(J_3-I_3)&h\mathbf1_3\\
                         h\mathbf1_3^*&0\end{bmatrix},
 \qquad N=s(J_3-I_3)\oplus0,\\
 r=\tfrac32t(1-t),\qquad h=(1-t)/\sqrt2,
 \qquad s=\tfrac32t-1.
 \end{gathered}                                           \tag{26}
\]

In particular all mixed plus/minus coefficients vanish. The decomposition is unitary and omits no input coordinate or cross block.

### 91.7. Exact full-reference norm of the family

**Theorem 91.2.** The original channels (22) have exact error

\[
 \delta(t)=\max\{D_+(t),\tfrac43|\tfrac32t-1|\},
                                                               \tag{27}
\]

where

\[
 D_+(t)=
 \begin{cases}
 (1-t)/(\sqrt2-t),&0\le t\le1/\sqrt2,\\
 2t(1-t),&1/\sqrt2\le t\le1.
 \end{cases}
                                                               \tag{28}
\]

Consequently

\[
 \min_{0\le t\le1}\delta(t)
      =2\sqrt{2/3}-\tfrac43>\tfrac14,
 \qquad t_{\min}=\sqrt{2/3}.
                                                               \tag{29}
\]

**Proof.** The coefficient map for (26) kills cross-sector input blocks. Each sector has one coordinate for each of the four output labels, so its restriction is a scalar Schur multiplier with kernel M or N. For a positive reference/input state, the two principal sector blocks are positive and their traces sum to one. The triangle inequality bounds the total output error by the larger sector norm, even though their outputs share the same output space. An input wholly in one sector attains its sector norm. The state-to-operator argument in (17) makes this a full diamond-norm reduction.

We compute the plus-sector norm directly. For r,h≥0 the spectrum of M is

\[
 -r,\ -r,\ r+\sqrt{r^2+3h^2},\ r-\sqrt{r^2+3h^2}.
                                                               \tag{30}
\]

In particular M has at most one positive eigenvalue. The needed norm is

\[
 \|\operatorname{Schur}_M\|_\diamond=
 \begin{cases}
 4r/3,&h\le2r/3,\\
 3h^2/(3h-r),&h\ge2r/3,
 \end{cases}
                                                               \tag{31}
\]

with the zero matrix treated separately.

First suppose r>0 and h≤2r/3. Set d=4r/3, v=(1,1,1,3h/(2r))ᵀ and Y=dvv*. Then

\[
 Y\ge0,\qquad
 Y-2M=2r(I_3-J_3/3)\oplus(3h^2/r)\ge0.
                                                               \tag{32}
\]

The diagonal of Y is (d,d,d,3h²/r), bounded by d precisely because h≤2r/3. Thus Z=Y−M dominates ±M and its diagonal is at most d. The CP argument in section 91.4, with one coordinate per fibre, proves the arbitrary-reference upper bound d. The normalized uniform input on the three outer coordinates has output M_outer/3, with eigenvalues 2r/3,−r/3,−r/3. Its trace norm is d. This includes h=0; the separate r=h=0 case is immediate.

Next suppose h>0 and h≥2r/3. Put d=3h²/(3h−r) and Y=dJ₄. On the outer sum-zero space Y−2M is 2rI. On the outer-uniform and central coordinates it is

\[
 \begin{bmatrix}
 3d-4r&\sqrt3(d-2h)\\
 \sqrt3(d-2h)&d
 \end{bmatrix}.
                                                               \tag{33}
\]

This matrix has determinant zero and 3d−4r=(3h−2r)²/(3h−r)≥0; since d>0, it is positive semidefinite. Hence Y≥0, Y≥2M, and its diagonal is d. The same CP argument gives the upper bound d.

For a matching input set

\[
 q=\frac{3h}{2(3h-r)},\qquad
 p=(q/3,q/3,q/3,1-q),\qquad
 |\psi_p\rangle=\sum_f\sqrt{p_f}|f\rangle.
                                                               \tag{34}
\]

The regime h≥2r/3 ensures 0≤q≤1. At every index with p_f>0 one has (Mp)_f=d/2. Thus (√p_f)_f is an eigenvector of diag(√p)Mdiag(√p) with eigenvalue d/2. Congruence cannot increase its number of positive eigenvalues, and its trace is zero. Its trace norm is therefore d, proving (31), including the common boundary of its regimes.

The minus-sector norm is 4|s|/3: the uniform outer input attains it, and (32) with r=|s| and h=0 gives the upper bound; reversing the sign of a kernel does not change its norm. For t<1 the inequality h≤2r/3 in (26) is equivalent to t≥1/√2. Substitution gives (27)–(28), with t=1 handled by M=0.

On [0,1/√2] the first expression in (28) decreases to √2−1. On [1/√2,1] the plus-sector value 2t(1−t) decreases, whereas the minus-sector value 2t−4/3 increases. They meet at t=√(2/3), with value (29), below √2−1. Finally 2√(2/3)>19/12, as is seen by squaring positive sides, so (29) is strictly larger than 1/4. This proves the theorem.

### 91.8. Failure of the uniform witness together with every complete two-fibre test

**Corollary 91.3.** For every parameter

\[
 \frac{1+1/\sqrt3}{2}<t<\frac56,
                                                               \tag{35}
\]

the original rank-(3,3) channels (22) satisfy

\[
 \max\left\{\tfrac14\operatorname{Tr}L_+,
              \max_{f<g}\|L_{fg}\|_{\rm op}\right\}<\frac14.
                                                               \tag{36}
\]

Each pair norm here is the full arbitrary-reference diamond norm of the original error map restricted to those two input fibres. Nevertheless the full original error is (27) and is always at least the strictly superquarter quantity (29).

**Proof.** Equations (26) and (30) give

\[
 \operatorname{Tr}L_+
     =2|s|+r+\sqrt{r^2+3h^2},\qquad
 \max_{f<g}\|L_{fg}\|_{\rm op}=\max\{r,|s|,h\}.
                                                               \tag{37}
\]

Indeed an outer-pair block has eigenvalues r,s, while an outer-central block has singular values h,0. Throughout (35), r<1/4, 0<s<1/4 and h<1/4. Since 2/3<t<1, the comparison TrL₊<1 is equivalent, after dividing by 1−t, to

\[
 \sqrt{9t^2/4+3/2}<3-3t/2.
                                                               \tag{38}
\]

Its right side is positive. The difference of the squared right and left sides is 15/2−9t, so (38) is equivalent to t<5/6. This proves (36). Calibration and section 91.5 give the complete two-fibre interpretation, and Theorem 91.2 gives the stated full error.

### 91.9. A rational-Gram member and matching exact certificates

At t=4/5, formula (22) uses u_j=(e₁+2ω^j e₂)/√5. Its frame operator is diag(4,3/5,17/5), and (24) becomes

\[
 K_{fg}=\frac1{25}\begin{bmatrix}7&12\\12&7\end{bmatrix}
 \quad(f\ne g\le3),\qquad
 K_{f4}=\begin{bmatrix}2/5&1/2\\2/5&1/2\end{bmatrix}.
                                                               \tag{39}
\]

Here r=6/25, s=1/5 and h=1/(5√2). The complete spectrum of L is

\[
 \left\{\frac{12+7\sqrt6}{50},\frac25,
         \frac{12-7\sqrt6}{50},
         -\frac6{25},-\frac6{25},-\frac15,-\frac15,0\right\}.
                                                               \tag{40}
\]

Thus the normalized maximally entangled logical/reference input has exact error

\[
 \frac{\|L\|_1}{8}
   =\frac{\operatorname{Tr}L_+}{4}
   =\frac{32+7\sqrt6}{200}<\frac14,
 \qquad
 \max_{f<g}\|L_{fg}\|_{\rm op}=\frac6{25}<\frac14.
                                                               \tag{41}
\]

The first equality uses the full correct-support Choi embedding and TrL=0. Its strict comparison follows from 294<324. The uniform value exceeds 6/25 because 294>256, so the maximum in (36) at this member is exactly (32+7√6)/200.

A normalized no-reference state on three outer fibres is

\[
 |\psi\rangle=\frac{c_1+c_2+c_3}{\sqrt3}
             =\frac1{\sqrt6}\sum_{f=1}^3
                                      (|f,0\rangle+|f,1\rangle).
                                                               \tag{42}
\]

Its target-minus-product output, represented on the outer output code, is (r/3)(J₃−I₃). Its eigenvalues are 4/25,−2/25,−2/25, so its unhalved trace norm is 8/25. There is no omitted output block because the actual maps are calibrated.

For an explicit arbitrary-reference upper certificate in (8), use the basis (25) and define

\[
 \begin{gathered}
 Y_+=\frac8{25}vv^*,\qquad
 v=(1,1,1,5\sqrt2/8)^T,\\
 Y_-=\frac4{15}ww^*,\qquad w=(1,1,1,0)^T,\\
 Y_+-2M=\frac{12}{25}(I_3-J_3/3)\oplus\frac14,\qquad
 Y_--2N=\frac25(I_3-J_3/3)\oplus0.
 \end{gathered}                                           \tag{43}
\]

Both Y matrices and both displayed residuals are positive semidefinite. Let Z=(Y₊−M)⊕(Y₋−N), returned to the original bit basis. Then Z≥±L. Each original outer 2×2 fibre block of Z has eigenvalues (8/25,4/15), and the central block is diag(1/4,0). Hence Z_ff≤(8/25)I₂ for every original fibre. This supplies the upper bound 8/25 for all reference and operator inputs, matching (42). Therefore

\[
 \boxed{\delta(A,B)=\mathcal B(L)=\frac8{25}.}
                                                               \tag{44}
\]

There is also an explicit zero-gap primal certificate for (7). Set

\[
 \rho=\frac13\sum_{f=1}^3|c_f\rangle\langle c_f|,
 \qquad W=\frac13|\psi\rangle\langle\psi|,
 \qquad Y=Z+L,\qquad t=\frac8{25}.
                                                               \tag{45}
\]

Then ρ∈𝒟, 0≤W≤ρ and 2Tr(LW)=8/25. The dual tuple is feasible by (43), and all three nonnegative terms in (19) vanish. The adaptive optimizer here is a three-fibre no-reference input, whereas the complete uniform and every two-fibre tests in (41) remain below quarter.

### 91.10. Scope and mathematical attribution

Theorem 91.1 is an original-channel lower bound that keeps the complementary leakage population. Its equality and reference-qubit conclusions require calibration of the actual channels. Theorem 91.2 and Corollary 91.3 concern explicitly constructed physical products, so they require no independent-block completion or error-monotone calibration replacement.

This refutes the proposed global sufficiency of the uniform positive-trace witness even after adjoining every complete two-fibre restricted diamond norm. It does not produce a subquarter product: the entire family has minimum (29). The [rank-two-party equality classification](ARITHMETIC_HOLOGRAPHIC_RT_II.md#82-quarter-error-rigidity-minimal-kraus-product-and-the-complete-rank-two-party-family) and the unrestricted local theorem of section 89 retain their hypotheses and conclusions. The unrestricted original-channel optimum remains in [√3−3/2,1/4]; neither a global quarter lower bound nor a calibrated reduction of arbitrary leaking pairs follows from this section.

The correct-output adaptive reduction and the explicit trine-family application are derived above for this fixed encoding. Positive-part duality, polar decomposition, Choi positivity, Stinespring representations, and finite-dimensional semidefinite strong duality are standard ingredients; see [Watrous, The Theory of Quantum Information, Chapters 1–3](https://cs.uwaterloo.ca/~watrous/TQI/) and, for channel norms, [Chapter 3](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf). The two-fibre norm identity is the existing section-65 result, proved again in the notation needed for its present consumer. These ingredients are not asserted to be new general norm theory. The new obstruction is the actual common-channel family and its simultaneous failure of all the stated restricted certificates.

## 92. Common adaptive stresses and support exclusions at doubly rank-seven minima

### 92.1. Physical domain and the attained Gram optimization

Retain the original local CPTP maps A,B:C⁸→C⁴, input labels x=(f,i) with f=1,...,4 and i=0,1, correlated encoding |x〉↦|xx〉, and output encoding |f〉↦|ff〉 from section 91. The target forward coefficient matrix T has T_ff=I₂ and T_fg=J₂/2 for f≠g. The error is the unhalved diamond norm with arbitrary references.

The [physical calibration theorem](ARITHMETIC_HOLOGRAPHIC_RT_II.md#72-exact-physical-calibration-reduction-for-collapsed-fibre-channels) permits calibration when taking the unrestricted global minimum. It preserves the product structure and does not increase the error, but may enlarge either local environment. It is not a rank-preserving replacement of an arbitrary leaking pair. The calibrated Gram domain and the adaptive witness domain are

\[
 \begin{split}
 \mathcal E&=\{G\in\operatorname{Herm}(8):G\ge0,
                                      \ G_{ff}=I_2\},\\
 \mathcal C&=\{(\rho,W):\rho=\bigoplus_f\rho_f\ge0,
                      \ \operatorname{Tr}\rho=1,\ 0\le W\le\rho\}.
 \end{split}                                                   \tag{1}
\]

Every G,H∈ℰ is physically realized by calibrated local channels: factor each as the Gram of eight records, whose two records in each fibre are orthonormal, and use |f,i〉↦|f〉⊗a_fi on the first side and similarly on the second. The local Choi ranks equal rank G and rank H. With the forward-Gram transpose convention already incorporated as in section 91, the exact error is

\[
 F(G,H)=\max_{(\rho,W)\in\mathcal C}
               2\operatorname{Tr}[(T-G\odot H)W].             \tag{2}
\]

Both sets in (1) are compact. Thus F is continuous and has a minimum on ℰ×ℰ, equal to the unrestricted original-channel minimum by the calibration theorem. The local assertions below concern local minima on this full calibrated Gram domain. They are not assertions about every competitor of the same rank, nor do they transfer local minimality through a rank-changing calibration.

### 92.2. One norming witness for both Gram faces

**Theorem 92.1.** If (G,H) is a local minimum of F, there is one feasible pair (ρ,W)∈𝒞 that attains (2) and simultaneously satisfies

\[
 \begin{aligned}
 \operatorname{Tr}(C_A G')&\le\operatorname{Tr}(C_A G)
                                      &&(G'\in\mathcal E),\\
 \operatorname{Tr}(C_B H')&\le\operatorname{Tr}(C_B H)
                                      &&(H'\in\mathcal E),\\
 C_A&=2(\overline H\odot W),\qquad
 C_B=2(\overline G\odot W).
 \end{aligned}                                                   \tag{3}
\]

Consequently Hermitian 2×2 blocks Λ_A,f,Λ_B,f can be chosen so that

\[
 \begin{aligned}
 P_A&=\bigoplus_f\Lambda_{A,f}-C_A\ge0,
       &P_AG=GP_A&=0,\\
 P_B&=\bigoplus_f\Lambda_{B,f}-C_B\ge0,
       &P_BH=HP_B&=0.
 \end{aligned}                                                   \tag{4}
\]

The same W appears in both equations. If 0<F(G,H)<1/2, both stresses are nonzero and both Grams are singular.

**Proof.** Put L=T−G⊙H and t=F(G,H). The set

\[
 \mathcal A=\{(\rho,W)\in\mathcal C:
                          2\operatorname{Tr}(LW)=t\}          \tag{5}
\]

is a nonempty compact convex exposed face. For arbitrary G′,H′∈ℰ, let D_G=G′−G and D_H=H′−H. The feasible joint segment has exact coefficient expansion

\[
 T-(G+sD_G)\odot(H+sD_H)
   =L-s(D_G\odot H+G\odot D_H)-s^2D_G\odot D_H.                \tag{6}
\]

Uniformity over compact 𝒞 gives the one-sided derivative

\[
 \left.\frac{d}{ds}\right|_{0+}F(G+sD_G,H+sD_H)
   =\max_{(\rho,W)\in\mathcal A} b(W;G',H'),
 \quad
 b=-2\operatorname{Tr}[(D_G\odot H+G\odot D_H)W].              \tag{7}
\]

Indeed every active witness gives the lower derivative bound. For the upper bound choose a maximizer at each s>0 and pass to a convergent subsequence as s decreases to zero. Its limit is active by continuity. Its value at s=0 is at most t, and (6) supplies the upper derivative bound. This argument does not require a unique norming witness or differentiability of F.

Local minimality makes the maximum in (7) nonnegative for every feasible pair. There is a single point of 𝒜 for which b≥0 for all such pairs. To prove this directly, suppose the corresponding closed half-spaces had empty intersection in 𝒜. Compactness would give finitely many pairs whose half-spaces already have empty intersection. Their compact convex vector image under b is disjoint from the nonnegative orthant. Strict separation gives nonnegative coefficients λ_j, summing to one, for which the maximum of the corresponding weighted sum of b is negative. The separating coefficients are nonnegative because the orthant is unbounded in each positive coordinate. Averaging the feasible pairs with these λ_j contradicts (7), since b is affine in the pair. This proves the common-witness assertion. Set H′=H or G′=G to obtain the two support inequalities in (3).

For Hermitian D,H,W, the precise coefficient identity is

\[
 \operatorname{Tr}[(D\odot H)W]
    =\operatorname{Tr}[D(\overline H\odot W)].                 \tag{8}
\]

The (y,x) entry of the second factor on the right is H_xy W_yx, which verifies both the conjugation and the sign in (3). The matrices C_A,C_B are positive by the Schur product theorem.

For any Hermitian C, the support problem max{Tr(CX):X∈ℰ} has dual

\[
 \min\left\{\sum_f\operatorname{Tr}\Lambda_f:
                    \bigoplus_f\Lambda_f-C\ge0\right\}.       \tag{9}
\]

The primal has strictly feasible X=I₈ and bounded optimum; a sufficiently large scalar diagonal matrix is strictly dual feasible. Semidefinite strong duality and attainment apply. At equality the positive primal and slack matrices satisfy Tr(PX)=0, hence PX=XP=0. Applying this to both support problems proves (4).

The matrix-unit test gives

\[
 |1/2-G_{xy}H_{xy}|\le t
                 \qquad(x,y\text{ in different fibres}).     \tag{10}
\]

If 0<t<1/2, every cross-fibre entry of G and H is nonzero. If P_A=0, the off-diagonal fibre blocks of (4) then force W_fg=0 for every f≠g. Since L_ff=0, this would give t=2Tr(LW)=0. Thus P_A≠0 and similarly P_B≠0. Equation (4) proves singularity and, more precisely,

\[
 \operatorname{rank}G+\operatorname{rank}P_A\le8,
 \qquad
 \operatorname{rank}H+\operatorname{rank}P_B\le8.               \tag{11}
\]

This concludes the proof.

### 92.3. Algebraic identities and the hypothetical subquarter minimum

The common stress equations determine all block multipliers:

\[
 \begin{aligned}
 \Lambda_{A,f}&=(C_AG)_{ff},&
 \Lambda_{B,f}&=(C_BH)_{ff},\\
 (P_A)_{ff}&=2\sum_{g\ne f}(\overline{H_{fg}}\odot W_{fg})G_{gf},&
 (P_B)_{ff}&=2\sum_{g\ne f}(\overline{G_{fg}}\odot W_{fg})H_{gf}.
 \end{aligned}                                                   \tag{12}
\]

They also give the trace identities

\[
 \begin{split}
 \sum_f\operatorname{Tr}\Lambda_{A,f}
   &=\sum_f\operatorname{Tr}\Lambda_{B,f}
     =2\operatorname{Tr}[(G\odot H)W],\\
 p:=\operatorname{Tr}P_A=\operatorname{Tr}P_B
   &=2\operatorname{Tr}[(T-I_8)W]-t.
 \end{split}                                                   \tag{13}
\]

For 0<t<1/2, p>0. The identities follow by multiplying (4) by G or H, taking diagonal blocks, and using G_ff=H_ff=I₂. In particular the computed blocks in (12) must be Hermitian; this is not an additional automatic property of an arbitrary triple G,H,W.

If the unrestricted original-channel minimum were below 1/4, its attained calibrated minimizer would have both ranks in {3,4,5,6,7}. The upper bound follows from Theorem 92.1; the lower bound follows from the [rank-two-party lower bound](ARITHMETIC_HOLOGRAPHIC_RT_II.md#81-a-subnormalized-centroid-support-witness-for-original-local-environment-bounds). This is a statement about an attained hypothetical minimum, not every subquarter competitor.

Such a minimizer would satisfy (1)–(4), (10)–(13), and the full adaptive dual conditions from section 91:

\[
 Y\ge0,\quad Y\ge2L,\quad Y_{ff}\le tI_2,\quad
                 t=2\operatorname{Tr}(LW),\quad0<t<1/4.       \tag{14}
\]

Equivalently, feasible primal and dual variables have the complementary relations

\[
 Y(\rho-W)=0,\qquad (Y-2L)W=0,\qquad
                       (tI_2-Y_{ff})\rho_f=0.                 \tag{15}
\]

These follow term by term from the nonnegative gap identity in section 91. They are finite real algebraic and positive-semidefinite conditions after separating real and imaginary parts. Stress stationarity alone is not a sufficient condition for a minimum, and no extreme-point rank reduction is inferred from convexity of a one-party objective.

### 92.4. Exact active support when both ranks are seven

**Theorem 92.2.** Suppose (G,H) is a calibrated local minimum, rank G=rank H=7, and 0<t=F(G,H)<1/2. Its common stresses have rank one, say P_A=aa* and P_B=bb*. Their coordinate supports coincide in a set S meeting at least two fibres. Every common norming density and witness is supported on S and has strictly positive diagonal entries on S. For one such stress pair there is a diagonal unitary D on S with

\[
 H_S=D^*G_SD,\qquad
 \operatorname{rank}G_S=\operatorname{rank}H_S=|S|-1.           \tag{16}
\]

A reciprocal diagonal phase change preserving the full product G⊙H makes G_S=H_S and the two kernel lines coincide. The adaptive norm of the principal input restriction to S is exactly t. This does not assert that S is the whole input or that the full Grams coincide outside S.

**Proof.** The nonzero stresses in (4) are supported in one-dimensional kernels, so they have rank one. Neither a nor b can be supported in only one fibre, because its diagonal Gram block is I₂. Across different fibres, (4) reads

\[
 2\overline{H_{xy}}W_{xy}=-a_x\overline{a_y},\qquad
 2\overline{G_{xy}}W_{xy}=-b_x\overline{b_y}.                    \tag{17}
\]

For x∈supp(a), choose y∈supp(a) in another fibre. Nonzero cross entries and (17) imply W_xy≠0 and then b_x≠0. Reversing parties proves equality of supports.

If x∉S, (17) gives W_xy=0 for every y in a different fibre. Delete coordinate x with a fibre-block projection Q. The compressed pair QρQ,QWQ is feasible except that its density has trace 1−ρ_xx. Its objective is still t, because L has zero fibre blocks and all discarded cross entries of W vanish. If ρ_xx>0, normalizing by 1−ρ_xx would increase the value above t. The denominator is positive since t>0. Thus ρ_xx=0; positivity and 0≤W≤ρ make the corresponding rows and columns of both matrices vanish. Conversely each x∈S has a nonzero cross entry W_xy by (17), so W_xx>0 and ρ_xx>0. This argument applies to every common norming witness, since the two kernel lines and their supports are fixed.

For x∈S put c_x=a_x/b_x and D=diag(c_x). Dividing (17), and retaining the unit diagonals and zero within-fibre off-diagonals, gives

\[
 H_S=D^*G_SD+\operatorname{diag}(1-|c_x|^2).                    \tag{18}
\]

Since Db_S=a_S, G_Sa_S=0 and H_Sb_S=0, equation (18) forces (1−|c_x|²)b_x=0. Every b_x on S is nonzero, hence D is unitary and (16)'s first identity holds. If z∈ker G_S, its extension by zero has quadratic form zero against G. Positivity puts that extension in the one-dimensional ker G. Thus ker G_S=span(a_S), proving its rank; the other side is identical.

Choose diagonal unitary E on S with E²=D and extend it by arbitrary unit phases elsewhere. Then

\[
 G'=E^*GE,\qquad H'=EHE^*,\qquad
 G'\odot H'=G\odot H,\qquad G'_S=H'_S.                        \tag{19}
\]

The transformed kernel vectors E*a and Eb coincide because a=Db=E²b. This reciprocal phase transformation is a homeomorphism of ℰ×ℰ and preserves F and local minimality. Finally the norming ρ,W are supported on S. Conversely any feasible principal witness extends by zeros to a full feasible witness. These two observations give equality of the principal adaptive norm and t, completing the proof.

### 92.5. Fixed-direction second-order selection

Work in the gauge (19). Let a span the common full kernel, with support S. In addition to the active face 𝒜 from (5), define the nonempty compact convex common-witness subset

\[
 \mathcal A_0=\{(\rho,W)\in\mathcal A:
                b(W;G',H')\ge0\text{ for all }G',H'\in\mathcal E\}.
                                                                  \tag{20}
\]

No face property of 𝒜₀ is required. For every point of 𝒜₀, its first stress equals αaa* for some α>0. Positivity of α follows exactly as in Theorem 92.1; α=0 would force the norming value to vanish. Hence, on cross-fibre coordinates of S,

\[
 W_{xy}=-\frac{\alpha a_x\overline{a_y}}
                         {2\overline{G_{xy}}}.                 \tag{21}
\]

The gauge and kernel vector here are fixed, independently of the witness.

For a Hermitian D supported on S with D_ff=0 and Da=0, both G+sD and H−sD are positive for sufficiently small real s: they preserve the kernels and the Grams are positive definite on the orthogonal kernel complements. The first-order product change vanishes because G_S=H_S. A necessary second-order condition is

\[
 \text{for each fixed }D,\quad
 \exists(\rho,W)\in\mathcal A_0:
                Q_W(D):=2\operatorname{Tr}[(D\odot D)W]\ge0.    \tag{22}
\]

Here is the selection proof, including the quantifier order. Fix D and R>0. For arbitrary G′,H′∈ℰ put U=R(G′−G), V=R(H′−H). The paths

\[
 G_s=G+sD+s^2U,\qquad H_s=H-sD+s^2V                            \tag{23}
\]

are feasible for sufficiently small s. For example G_s=(1−Rs²)[G+sD/(1−Rs²)]+Rs²G′ is a convex combination of feasible Grams. Their coefficient difference expands as

\[
 T-G_s\odot H_s
   =L+s^2(D\odot D-U\odot H-G\odot V)+O(s^3).                 \tag{24}
\]

The compact-max argument of (7), now at scale s², and local minimality give

\[
 \max_{(\rho,W)\in\mathcal A}
       [Q_W(D)+R b(W;G',H')]\ge0
                         \quad\text{for every }G',H'\in\mathcal E.
                                                                  \tag{25}
\]

The same finite separation argument used after (7) applies only to the affine variables G′,H′ and the active witnesses. It supplies a point (ρ_R,W_R)∈𝒜 satisfying Q_(W_R)(D)+R b(W_R;G′,H′)≥0 for all feasible pairs. Choosing the base pair shows Q_(W_R)(D)≥0. Compactness bounds this quadratic value uniformly. Along a convergent subsequence as R tends to infinity, the inequalities give b(W_*;G′,H′)≥0 for every fixed pair and Q_(W_*)(D)≥0. The limiting pair belongs to 𝒜₀, proving (22).

The direction D is fixed throughout this minimax step. Equation (22) does not assert one witness whose quadratic form is nonnegative for every direction. Nor does negativity for one arbitrarily chosen active witness imply descent of F. The next argument uses the stronger proportionality of all the forms indexed by 𝒜₀.

### 92.6. A quantitative support exclusion from quadratic inertia

**Theorem 92.3.** Under the hypotheses of Theorem 92.2, put d_f=|S∩{(f,0),(f,1)}|, n=|S|, and m=Σ_(f<g)d_fd_g. Then

\[
                         m\le2n-1,\qquad n\le5.               \tag{26}
\]

Thus a positive subhalf calibrated local minimum with both ranks seven cannot have active support on six, seven, or eight input coordinates.

**Proof.** The real vector space of Hermitian D supported on S with zero fibre blocks has one complex variable z=D_xy for each of its m unordered cross-fibre edges, hence dimension 2m. Equation (21) gives

\[
 Q_W(D)=-\alpha\sum_{x,y\text{ in different fibres}}
             \frac{a_y\overline{a_x}}{G_{xy}}D_{xy}^2.         \tag{27}
\]

Each unordered edge contributes −2α Re(c_xy z²), where c_xy=a_y conjugate(a_x)/G_xy≠0. For z=u+iv, the real quadratic form Re(cz²) has eigenvalues +|c| and −|c|. Thus (27) has exactly m positive and m negative eigenvalues, with no zero eigenvalue, for arbitrary complex phases.

Fix any one point of 𝒜₀ and its m-dimensional negative eigenspace N. The real-linear map D↦Da has rank at most 2n−1, because its image lies in the hyperplane Im(a*Da)=0. If m>2n−1, a nonzero D∈N therefore satisfies Da=0. It obeys every condition in (22) and has Q_W(D)<0. For every other point of 𝒜₀, formula (27) is a strictly positive scalar multiple of the same form, so this single D is negative for all common witnesses. That contradicts (22) and proves the first inequality of (26).

For n=6 the possible fibre sizes are (2,2,2,0) and (2,2,1,1), giving m=12 or 13, both greater than 11. For n=7 the sizes are (2,2,2,1) and m=18>13. For n=8 they are (2,2,2,2) and m=24>15. This proves n≤5 with the original fibre constraints retained.

### 92.7. Excluding support in only two fibres

**Theorem 92.4.** Under the hypotheses of Theorem 92.2, the active stress support meets at least three original fibres.

**Proof.** Work in the reciprocal gauge (19). If the support meets exactly two fibres, their positive occupancies can only be (1,1), (2,1), (1,2), or (2,2). A two-coordinate support is impossible: its rank-one principal Grams have unit-modulus cross entries, so their product has modulus one and differs from the target 1/2 by at least 1/2, contradicting (10).

For occupancies (2,1), write the common principal Gram and a kernel vector as

\[
 G_S=H_S=\begin{pmatrix}I_2&g\\g^*&1\end{pmatrix},
 \qquad a_S=(-g,1),\qquad \|g\|_2=1.                         \tag{28}
\]

The norm equality follows from positivity and rank two. Both entries of g are nonzero. Put m_i=1/2−g_i², the cross column of the principal error. Its complete restricted diamond norm is exactly ∥m∥₂. Here is a direct adaptive proof, with its normalization retained.

For any feasible witness let w=W_fg be its cross column. Compress ρ,W to any unit vector in the first fibre and the second singleton. Write the compressed ρ diagonals as r,s, the compressed W diagonals as A,B, and its cross entry as z. Then r+s≤1 and positivity of W and ρ−W gives

\[
 |z|\le\sqrt{AB},\qquad
 |z|\le\sqrt{(r-A)(s-B)},\qquad
 2|z|\le\sqrt{rs}\le\tfrac12.                              \tag{29}
\]

The middle bound follows by adding the first two and using Cauchy–Schwarz. Taking the supremum over the first-fibre unit vector gives ∥w∥₂≤1/4. The objective is 4 Re(m*w), so it is at most ∥m∥₂. Equality is feasible: for u=m/∥m∥₂ choose ρ=diag(uu*/2,1/2) and W=(u,1)(u,1)*/4; then ρ−W=(u,−1)(u,−1)*/4≥0. The case m=0 is immediate, and here t>0 excludes it. Theorem 92.2 therefore gives t=∥m∥₂, and every norming witness satisfies

\[
 w=\frac{m}{4t}.                                             \tag{30}
\]

The positive common stress αa_Sa_S* instead forces 2 conjugate(g_i)w_i=αg_i, hence w_i=βg_i/conjugate(g_i) with β=α/2>0. Combining this with (30) gives

\[
 \tfrac12=(|g_i|^2+4t\beta)\frac{g_i}{\overline{g_i}}.
                                                                  \tag{31}
\]

The coefficient in parentheses is positive and the last factor has modulus one. Thus g_i/conjugate(g_i)=1 and |g_i|²=1/2−4tβ for both entries. Their sum contradicts ∥g∥₂²=1. The reversed occupancy (1,2) is identical after exchanging the fibres.

For occupancies (2,2), write

\[
 G_S=H_S=\begin{pmatrix}I_2&C\\C^*&I_2\end{pmatrix}.
                                                                  \tag{32}
\]

Positivity and rank three say that C has singular values one and a number strictly smaller than one. The kernel is spanned by a_S=(−u,v), where u,v are unit vectors with Cv=u and C*u=v. Every component of u,v and every entry of C is nonzero.

For the purpose of calculating (27), simultaneous diagonal-unitary coordinate changes G_S↦E*G_SE, a_S↦E*a_S, D_S↦E*D_SE preserve each ordered summand and the condition D_Sa_S=0. The phase acquired by D_xy² cancels the inverse phase in its coefficient. This is an algebraic change of coordinates for finding a direction; it does not claim that applying the same phases to both physical channels preserves their product or the target. The direction is returned to the original gauge after the calculation.

Choose these coordinates so that u=(c,d), v=(e,f) have positive real entries. Put u_perp=(−d,c), v_perp=(−f,e). Then

\[
 c^2+d^2=e^2+f^2=1,\qquad
 C=uv^T+z\,u_{\perp}v_{\perp}^T,\qquad |z|<1.                \tag{33}
\]

For any complex w, the Hermitian direction with cross block D_fg=w u_perp v_perp^T and reverse block its adjoint satisfies Da=0. Extend it by zeros outside S. Substitution into (27) gives exactly

\[
 Q_W(D)=2\alpha\operatorname{Re}(w^2 A),\qquad
 A=cdef\left(\frac{df}{C_{00}}+\frac{de}{C_{01}}
                    +\frac{cf}{C_{10}}+\frac{ce}{C_{11}}\right).
                                                                  \tag{34}
\]

This coefficient is nonzero for every permitted complex z. Indeed put r=d/c>0 and q=f/e>0. The bracket in (34) equals

\[
 \begin{split}
 &\frac{rq}{1+zrq}+\frac{r}{q-zr}
                  +\frac{q}{r-zq}+\frac{1}{rq+z}\\
 &\qquad=
 \frac{rq(1+r^2)(1+q^2)(1-z^2)}
 {(1+zrq)(q-zr)(r-zq)(rq+z)}.
 \end{split}                                                   \tag{35}
\]

The denominator is nonzero because all four entries of C are nonzero, and the numerator is nonzero because |z|<1. Choose the phase of w so that Re(w²A)<0, and return the resulting direction to the original coordinates. Formula (34) is then negative for every common witness, since its only witness-dependent factor is α>0. This contradicts the fixed-direction condition (22), and excludes the last two-fibre case. The theorem follows.

Combining Theorems 92.3 and 92.4 leaves exactly five possible occupancy patterns, up to fibre permutation:

\[
 (1,1,1,0),\quad (2,1,1,0),\quad (1,1,1,1),\quad
                 (2,2,1,0),\quad (2,1,1,1).                  \tag{36}
\]

A zero entry means a whole missing fibre. An entry one means only one retained coordinate of that original two-coordinate fibre. These are different restrictions, and none of the five patterns is excluded here.

### 92.8. Why small equal principal Grams alone do not imply a quarter bound

**Proposition 92.5.** There are equal positive principal Grams on one coordinate in each of four fibres, of rank three with a kernel vector nonzero on every coordinate, whose complete restricted diamond error is 21/100. They admit an original physical completion with both local ranks seven, but the completion has full error at least 1/2. The principal example cannot carry a positive common norming stress.

**Proof.** In a real three-dimensional environment choose

\[
 u_f=\frac{2e_0+\cos(\pi f/2)e_1+\sin(\pi f/2)e_2}{\sqrt5},
                    \qquad f=0,1,2,3.                       \tag{37}
\]

Their Gram R is real circulant with first row (1,4/5,3/5,4/5), eigenvalues 16/5,2/5,0,2/5, and kernel spanned by v=(1,−1,1,−1). Set both principal Grams equal to R. The singleton target is (I₄+J₄)/2, so with P=vv*/4,

\[
 L_S=\frac7{50}(vv^*-I_4)
       =\frac{14}{25}P-\frac7{50}I_4,\qquad
 Z=|L_S|=\frac7{50}I_4+\frac7{25}P.                           \tag{38}
\]

The eigenvalues of L_S are 21/50 and −7/50 with multiplicity three. Exact positive majorant certificates are

\[
 Z-L_S=\frac7{25}(I_4-P)\ge0,\qquad
 Z+L_S=\frac{21}{25}P\ge0,\qquad Z_{ff}=\frac{21}{100}.
                                                                  \tag{39}
\]

For every feasible singleton density ρ and witness W, ρ is diagonal and Tr(L_Sρ)=0. Therefore

\[
 \begin{split}
 2\operatorname{Tr}(L_SW)
  &=\operatorname{Tr}(L_SW)
              -\operatorname{Tr}[L_S(\rho-W)]\\
  &\le\operatorname{Tr}(ZW)+\operatorname{Tr}[Z(\rho-W)]
    =\operatorname{Tr}(Z\rho)=\frac{21}{100}.
 \end{split}                                                   \tag{40}
\]

Equality holds for ρ=I₄/4 and W=vv*/16. This proves the complete restricted diamond norm, including arbitrary references, rather than only a uniform-input lower bound. The singleton restriction is a scalar Schur map, so (39) is also its usual diamond majorant.

If a positive common norming stress existed, rank three would force it to be αvv* with α>0. Across distinct singleton fibres its equation would require W_fg=−αv_fv_g/(2R_fg). Every R_fg is positive and (L_S)_fg v_fv_g=7/50. Consequently

\[
 2\operatorname{Tr}(L_SW)=-\frac{7\alpha}{3}<0,                \tag{41}
\]

contradicting the positive norming value. Zero stress is impossible too: all cross entries of R are nonzero, so it would force all cross entries of W to vanish. Thus the obstruction concerns every proposed common norming stress, not merely the displayed uniform witness.

For the original-channel completion, use u_f as each first-bit environment record and four distinct orthonormal records e′_f in an orthogonal real four-dimensional space as the second-bit records. Use these same seven-dimensional records for both local channels. Each original fibre pair is orthonormal, so |f,i〉↦|f〉⊗record_(f,i) is a Stinespring isometry on all eight original inputs. After ordering the first-bit coordinates before the second-bit coordinates, both full Grams are R⊕I₄ and have rank seven. Hence both calibrated channels have local Choi rank seven, and the four-singleton restriction above is retained exactly.

However any first-bit coordinate and a second-bit coordinate in a different fibre have product coefficient zero instead of the target 1/2. The original matrix-unit test therefore gives full error at least 1/2. This completion is not an original subquarter competitor and does not have the common active support asserted in Theorem 92.2. The proposition follows.

### 92.9. Consequences and boundaries

If the unrestricted original-channel minimum were below 1/4, an attained calibrated minimizer would satisfy the common adaptive stresses and complementary conditions above, with both ranks between three and seven. If both ranks were seven, its common stress support would have one of the five patterns in (36). The argument excludes supports on six or more coordinates and supports in only two fibres. It does not exclude the five remaining patterns, unequal rank pairs, or lower-rank common-stress systems.

The exact 21/100 example shows why the remaining small-support analysis cannot discard the same norming witness and its positive stresses: positivity, equal principal Grams, rank |S|−1, and a physical completion do not alone imply a restricted quarter bound. Its full original error is at least 1/2, so it does not change the original optimum.

These results do not classify all calibrated local minima or all quarter-error attainters. The unrestricted original-channel optimum remains in [√3−3/2,1/4]. Calibration is used only through the established physical global comparison, with no rank-preservation claim.

The compact-max, finite-dimensional separation, Schur-product, and semidefinite duality ingredients are standard; see [Watrous, The Theory of Quantum Information, Chapters 1–3](https://cs.uwaterloo.ca/~watrous/TQI/). The physical Gram optimization is the established section-72 reduction, and the exact adaptive norm and its primal-dual gap are section 91. The conclusions proved here are the simultaneous norming stress condition for this product problem, its exact rank-seven support constraints, the second-order and two-fibre exclusions using the original fibre dimensions, and the small-support scope counterexample. No general minimax or semidefinite-duality theorem is asserted to be new.

## 93. A sharp complex three-vector bound and exclusion of three-singleton support

### 93.1. Domain and quantitative statement

Retain the original local CPTP maps A,B:C⁸→C⁴, four fibres of two input coordinates each, correlated encoding |f,i〉↦|f,i〉|f,i〉, and output encoding |f〉↦|ff〉. The error is the unhalved diamond norm, including arbitrary reference systems. For calibrated channels the forward local Grams satisfy G_ff=H_ff=I₂, their product coefficient is G⊙H, and the target has T_ff=I₂ and T_fg=J₂/2 for f≠g, as in sections 91–92. Calibration of arbitrary leaking channels is used only through the physical global comparison of section 72; it is not assumed to preserve local ranks or local minima.

The common-stress and active-support reduction in section 92 makes the two principal Grams equal on a hypothetical doubly rank-seven minimum's common support. The following bound treats the entire complex rank-two three-coordinate domain, so no further singular-error or curvature condition is needed for the three-singleton case.

**Theorem 93.1.** Let G be any complex Hermitian positive semidefinite 3×3 matrix with diagonal entries one and rank at most two. Put a=G₁₂, b=G₂₃, c=G₃₁, and let u be the positive real cube root of 9. Then

\[
 E(G):=\left|\frac12-a^2\right|^2+
        \left|\frac12-b^2\right|^2+
        \left|\frac12-c^2\right|^2
 \ \ge\ \frac{21-9u}{16}\ >\ \frac9{64}.                 \tag{1}
\]

The first inequality is sharp. No reality, phase, kernel-weight, or symmetry assumption is imposed on G.

### 93.2. An attainer and all boundary reductions

**Proof of Theorem 93.1.** Set

\[
 x=\frac{1+u}{4},\qquad y=\frac{1-x}{\sqrt3},\qquad
 z=x+iy,\qquad
 G_* =\begin{pmatrix}
 1&z&\overline z\\
 \overline z&1&z\\
 z&\overline z&1
 \end{pmatrix}.                                             \tag{2}
\]

Since 2<u<3, one has 0<x<1. The circulant eigenvalues are 1+2x, 2(1−x), and zero. Thus G_* is a rank-two correlation Gram, and direct substitution gives

\[
 E(G_*)=\frac{64x^4-64x^3+24x^2-40x+25}{12}
        =\frac{21-9u}{16}<\frac3{16}.                       \tag{3}
\]

The domain of Theorem 93.1 is compact. Hence a global minimizer exists, and every global minimizer has value below 3/16 by (3). Fix any such minimizer. None of its cross entries is zero: a zero alone contributes 1/4. None has modulus one: the reverse triangle inequality again gives a contribution at least 1/4. Its rank is exactly two, because rank one would force every cross entry to have modulus one. Every coordinate of a nonzero kernel vector is nonzero, since a kernel vector with a zero coordinate would make a 2×2 principal unit-diagonal block singular and force its cross entry to have modulus one.

In the real affine space of Hermitian unit-diagonal matrices, the determinant-zero set is a smooth hypersurface near this minimizer. Indeed the adjugate is a positive nonzero multiple of the kernel outer product. Each complex cross-coordinate derivative pair is therefore nonzero; in particular the real determinant gradient is nonzero. The two positive eigenvalues remain positive nearby, and on this hypersurface the third is zero. Thus the entire nearby hypersurface is feasible. Ordinary real Lagrange multipliers apply without discarding any boundary case.

### 93.3. Stationary equations and repeated magnitudes

Write q₁=|a|², q₂=|b|², q₃=|c|² and P=abc. The determinant condition and the conjugate-coordinate Lagrange equations are

\[
 \begin{aligned}
 1-q_1-q_2-q_3+2\operatorname{Re}P&=0,\\
 (2q_1+\lambda)a-\overline a&=\lambda\overline{bc},
 \end{aligned}                                               \tag{4}
\]

with cyclic versions of the second equation and a single real multiplier λ. The derivative conventions are ∂E/∂ā=2q₁a−ā and ∂det(G)/∂ā=−a+overline(bc). Dividing by the nonzero a gives

\[
 \frac{\overline a}{a}
       =2q_1+\lambda-\frac{\lambda\overline P}{q_1},          \tag{5}
\]

and similarly for b,c. The multiplier is nonzero. Otherwise all q_i=1/2 and all entries are real, so their determinant would be −1/2±1/√2, never zero.

Taking squared moduli in (5) shows that every q_i is a positive root of

\[
 \begin{split}
 F(X)={}&4X^4+4\lambda X^3+
       (\lambda^2-4\lambda\operatorname{Re}P-1)X^2\\
       &-2\lambda^2\operatorname{Re}P\,X+\lambda^2|P|^2.
 \end{split}                                                   \tag{6}
\]

The three q_i cannot be distinct. If they were, the fourth root, counted with multiplicity, would be r₀=λ²/4>0 by the constant term and |P|²=q₁q₂q₃. Vieta's sum and third symmetric coefficient would give

\[
 \begin{aligned}
 U:=q_1+q_2+q_3
    &=-\lambda-\frac{\lambda^2}{4}
       =1-\frac{(\lambda+2)^2}{4}\le1,\\
 q_1q_2q_3+r_0(q_1q_2+q_2q_3+q_3q_1)
    &=\frac{\lambda^2\operatorname{Re}P}{2}
      =r_0(U-1)\le0.
 \end{aligned}                                                 \tag{7}
\]

The second line contradicts its strictly positive left side. It also covers a fourth root equal to one of the first three; no distinctness of all four roots was assumed.

Relabel so q₁=q₂=q. Equation (5) implies a²=b². A diagonal sign conjugation of G can therefore arrange a=b, preserving positivity, rank, and every squared entry. This uses only signs, not an unrestricted phase gauge. Put r=|c|² and B=2q+λ. Multiplication of the first equation in (4) by a gives

\[
 B a^2=q(1+\lambda\overline c).                              \tag{8}
\]

### 93.4. Real and zero-denominator branches

If B=0, then c=−1/λ is real. Whenever c is real, its stationary equation forces a² real. The possibility a²=−q gives one squared error (1/2+q)²>1/4 and is impossible. Hence a²=q, so a,b are real. Since |c|≠1, the determinant condition becomes

\[
 (1-c)(1+c-2q)=0,\qquad q=\frac{1+c}{2},
 \qquad
 E=\left(c^2-\frac14\right)^2+\frac3{16}\ge\frac3{16},       \tag{9}
\]

again impossible. Thus every minimizing stationary point has B≠0 and Im c≠0. In particular the vanishing-denominator branch has been exhausted rather than canceled.

### 93.5. Polynomial reduction of the nonreal branch

Write c=X+iY with Y≠0. Substitution of (8) into the stationary equation for c gives

\[
 [B(2r+\lambda)-\lambda^2q]c-B\overline c=\lambda q.
                                                                    \tag{10}
\]

Its imaginary and real parts imply respectively

\[
 r=\frac{\lambda^2q/B-\lambda-1}{2},\qquad
 X=-\frac{\lambda q}{2B}.                                    \tag{11}
\]

The modulus of (8) and the determinant condition then yield

\[
 \begin{aligned}
 B(1+\lambda^2r-B^2)-\lambda^2q&=0,\\
 B^2(1-2q-r)+2q\lambda rB-\lambda q^2&=0.
 \end{aligned}                                                 \tag{12}
\]

Substituting r from (11), the two left sides are exactly the following polynomials f and g:

\[
 \begin{aligned}
 f&=-\frac12(\lambda^2+2\lambda+4q-2)V,\\
 V&=4q^2+(-\lambda^2+4\lambda+2)q+\lambda^2+\lambda,\\
 g&=-\frac12\bigl[-2\lambda^3q^2+3\lambda^3q-\lambda^3
             +6\lambda^2q^2+2\lambda^2q-3\lambda^2\\
  &\hspace{55mm}{}+18\lambda q^2-12\lambda q+16q^3-12q^2\bigr].
 \end{aligned}                                                 \tag{13}
\]

All preceding divisions were by quantities already proved nonzero. It remains to examine both factors of f.

### 93.6. Excluding the sextic branch by a rational Sturm certificate

If λ²+2λ+4q−2=0, substitution in g gives

\[
 \begin{aligned}
 q&=-\frac{\lambda^2+2\lambda-2}{4},\qquad
 B=\frac{2-\lambda^2}{2},\\
 g&=\frac{(\lambda+2)H(\lambda)}{16},\qquad
 H(\lambda)=\lambda^6+\lambda^5-5\lambda^4+4\lambda+4.
 \end{aligned}                                                 \tag{14}
\]

At λ=−2, equations (11) and (14) give q=1/2 but r=−1/2, impossible. For the remaining roots of H, the exact identity

\[
 r-X^2-\frac{2\lambda^3+7\lambda^2-4\lambda-6}{16}
   =-\frac{(\lambda+1)H(\lambda)}{8(\lambda^2-2)^2}           \tag{15}
\]

has nonzero denominator because B≠0. Thus Y² is the displayed cubic divided by 16 at any remaining candidate.

For completeness, the entire real-root isolation uses the following polynomials:

\[
 \begin{aligned}
 H_0&=\lambda^6+\lambda^5-5\lambda^4+4\lambda+4,\\
 H_1&=6\lambda^5+5\lambda^4-20\lambda^3+4,\\
 H_2&=13\lambda^4-4\lambda^3-24\lambda-28,\\
 H_3&=21\lambda^3-13\lambda^2-30\lambda-22,\\
 H_4&=-55\lambda^2+12\lambda+62,\\
 H_5&=7\lambda+27,\qquad H_6=1.
 \end{aligned}                                                 \tag{16}
\]

Here H₁=H₀′, and polynomial division gives −rem(H_(j−2),H_(j−1))=κ_j H_j, with the strictly positive rational factors

\[
 (\kappa_2,\kappa_3,\kappa_4,\kappa_5,\kappa_6)
 =\left(\frac5{36},\frac{144}{169},\frac{169}{441},
                     \frac{3528}{3025},\frac{39325}{49}\right).
                                                                    \tag{17}
\]

Thus this is a positively rescaled Sturm chain. Its exact signs and variation counts are

\[
 \begin{array}{c|rrrrrrr|c}
 \lambda&H_0&H_1&H_2&H_3&H_4&H_5&H_6&\text{variations}\\ \hline
 -\infty&+&-&+&-&-&-&+&4\\
 -3&+&-&+&-&-&+&+&4\\
 -14/5&-&-&+&-&-&+&+&3\\
 -7/10&-&+&-&-&+&+&+&3\\
 -69/100&+&+&-&-&+&+&+&2\\
 +\infty&+&+&+&+&-&+&+&2
 \end{array}.                                                   \tag{18}
\]

No finite endpoint has a zero sign. Sturm's theorem therefore gives exactly one real root in (−3,−14/5), exactly one in (−7/10,−69/100), and none elsewhere. The first interval makes λ²+2λ−2 positive: it decreases there and equals 6/25 at the right endpoint. Hence q<0. On the second interval, 2λ³+7λ²−4λ−6 is strictly decreasing and equals −57/125 at the left endpoint. Hence Y²<0. Both roots are unphysical, so the first factor in (13) supplies no minimizer.

### 93.7. The unique physical stationary value

It remains that V=0. The resultant in q is the exact identity

\[
 \operatorname{Res}_q(V,g)=4\lambda^3(3\lambda-2)C(\lambda),
 \qquad C(\lambda)=6\lambda^3+9\lambda^2+9\lambda+5.           \tag{19}
\]

The leading q-coefficients of V and g are nonzero constants. Only the necessary implication from a common root to a zero resultant is used. The case λ=0 was excluded in section 93.3. At λ=2/3, V has roots q=−1/2 and q=−5/9, and only the former also solves g=0; neither is positive. Therefore C(λ)=0.

The polynomial C is strictly increasing because

\[
 C'(\lambda)=18\left(\lambda+\frac12\right)^2+\frac92>0,
 \quad C(-7/8)=-\frac1{256},\quad
 C(-87/100)=\frac{15541}{500000}.                            \tag{20}
\]

It has a unique real root, in (−7/8,−87/100). Put

\[
 A_0=121\lambda^2-843\lambda-985,\qquad
 B_0=295\lambda^2+395\lambda+25.                             \tag{21}
\]

Reduction of the polynomial remainder of g modulo V, followed by reduction modulo C in λ, gives (A₀q−B₀)/96. Thus A₀q=B₀ at a candidate. The coefficient A₀ is strictly negative on the interval in (20): it is decreasing there and A₀(−7/8)=−9903/64. Division by A₀ is therefore justified. The identity

\[
 A_0\frac{6\lambda^2-3\lambda+5}{20}-B_0
      =\frac{(121\lambda-1085)C(\lambda)}{20}               \tag{22}
\]

forces q=q_C:=(6λ²−3λ+5)/20. The substitutions in (11) satisfy

\[
 \begin{aligned}
 r-q_C&=-\frac{(\lambda+15)C(\lambda)}
                  {20(6\lambda^2+7\lambda+5)},\\
 X-\frac{18\lambda^2+21\lambda+20}{20}
       &=-\frac{(9\lambda+10)C(\lambda)}
                  {10(6\lambda^2+7\lambda+5)}.
 \end{aligned}                                                 \tag{23}
\]

These denominators are positive because 6λ²+7λ+5=6(λ+7/12)²+71/24. Hence all three squared magnitudes agree and

\[
 q=r=\frac{6\lambda^2-3\lambda+5}{20},\qquad
 X=\frac{18\lambda^2+21\lambda+20}{20}.                      \tag{24}
\]

Equation (5) now makes all three oriented squared entries equal, without requiring the unsquared entries to be real. Consequently

\[
 E=3\left(q^2+q-2X^2+\frac14\right)
   =-\frac{3(54\lambda^2+63\lambda+10)}{80},                 \tag{25}
\]

where the second equality uses C(λ)=0. For u³=9 the real number λ=−(u²−u+3)/6 is the unique real root of C, as follows from

\[
 C\left(-\frac{u^2-u+3}{6}\right)
   =-\frac{(u^3-9)(u^3-3u^2+3u+8)}{36}.                    \tag{26}
\]

Substituting this λ into (25) and reducing by u³=9 gives E=(21−9u)/16. Every global minimizer was below 3/16, and all boundary and stationary alternatives below that threshold have been exhausted. The matrix (2) attains the resulting value, proving the sharp minimum. Finally 9·12³=15552<15625=25³ gives u<25/12 and therefore (21−9u)/16>9/64. This completes the proof of Theorem 93.1.

### 93.8. Complete-norm consumer and the remaining original-channel cases

**Theorem 93.2.** For a calibrated principal restriction to one input coordinate in each of three different original fibres, suppose the two forward local Grams coincide and have rank at most two. With G that common Gram and L=(I₃+J₃)/2−G⊙G, the complete unhalved diamond error δ_S satisfies

\[
 \delta_S\ \ge\ \frac{\|L\|_1}{3}
       \ \ge\ \frac23\sqrt{E(G)}
       \ \ge\ \frac{\sqrt{21-9\sqrt[3]{9}}}{6}
       \ >\ \frac14.                                       \tag{27}
\]

The Frobenius edge minimum in Theorem 93.1 is sharp; no sharpness claim is made for the derived diamond lower bound (27).

**Proof.** The uniform density ρ=I₃/3 is feasible in the complete adaptive formula of section 91. Its value is ||L||₁/3. Equivalently the uniform correlated input on the three coordinates has output error Lᵀ/3 in the correlated output basis, whose trace norm is ||L||₁/3. This verifies the original forward-Gram transpose convention and the unhalved normalization. Since it is an allowed input, the complete norm, which also allows arbitrary references, is at least this value.

The Hermitian matrix L has trace zero and Tr(L²)/2=E(G). Up to a sign reversal and reordering, its eigenvalues are s,t,−s−t for s,t≥0, including zero eigenvalues and the zero matrix. Thus

\[
 \|L\|_1=2(s+t),\qquad
 E(G)=s^2+st+t^2\le(s+t)^2.                                 \tag{28}
\]

This proves the second inequality in (27); Theorem 93.1 proves the remaining two. No singularity of L is assumed.

**Corollary 93.3.** A calibrated local minimum of the original four-fibre problem with both full local Gram ranks seven and error strictly below 1/4 cannot have common active-support occupancy (1,1,1,0). Consequently the possible doubly rank-seven patterns left by section 92 are reduced from five to four, up to permutation of the original fibres:

\[
 (2,1,1,0),\qquad (1,1,1,1),\qquad
                (2,2,1,0),\qquad (2,1,1,1).                 \tag{29}
\]

**Proof.** The common-witness theorem and exact active-support reduction of section 92 give a reciprocal phase gauge preserving the full product coefficient and target. On a support of occupancy (1,1,1,0), the principal Grams then coincide and have rank two. The complete restricted norm equals the full value because the common norming witness is supported there; restriction monotonicity alone also suffices for the lower bound. Equation (27) contradicts a value below 1/4. Combining this exclusion with Theorems 92.3–92.4 leaves precisely (29).

The corollary refines the unresolved list in sections 92.7 and 92.9. A zero occupancy still means an absent whole fibre, whereas an occupancy one retains only one coordinate of a two-coordinate fibre. No pattern in (29) is excluded here. Unequal full Gram ranks and the other lower-rank common-stress cases remain unresolved. For arbitrary leaking channels, calibration is invoked only to compare the unrestricted global optimum with an attained calibrated optimum, with no rank-preservation or local-minimum transfer. The unrestricted original-channel optimum remains in [√3−3/2,1/4]; neither its quarter lower bound nor a classification of all quarter-error attainters follows from this section.

The proof uses ordinary real Lagrange multipliers, polynomial resultants, and Sturm's real-root theorem as established mathematical tools. For the last, see [Eisermann, The Fundamental Theorem of Algebra made effective: an elementary real-algebraic proof via Sturm chains](https://arxiv.org/abs/0808.0097). The specific sharp complex-Gram minimum is derived in Theorem 93.1, and the physical consumer uses the adaptive norm and common-support reduction of sections 91–92.

## 94. Quartet tangent exclusion of doubly rank-seven subquarter minima

### 94.1. Original problem and precise scope

Retain the original local CPTP maps A,B:C⁸→C⁴, four fibres of two coordinates, correlated input encoding |f,i〉↦|f,i〉|f,i〉, output encoding |f〉↦|ff〉, and arbitrary-reference unhalved diamond error. On the calibrated domain, the local Grams satisfy G,H≥0 and G_ff=H_ff=I₂. With T_ff=I₂ and T_fg=J₂/2 for f≠g, section 91 gives the exact objective

\[
 F(G,H)=\max_{(\rho,W)\in\mathcal C}
       2\operatorname{Tr}[(T-G\odot H)W],\qquad
 \mathcal C=\left\{(\rho,W):\rho=\bigoplus_f\rho_f\ge0,
                 \ \operatorname{Tr}\rho=1,\ 0\le W\le\rho\right\}.
                                                                    \tag{1}
\]

**Theorem 94.1.** No calibrated local minimum of (1) with rank G=rank H=7 has error below 1/4.

This is a statement about calibrated local minima, not about every doubly rank-seven competitor. The physical calibration comparison of section 72 is global and may enlarge ranks; it does not transfer local minimality from an arbitrary leaking pair. The unrestricted quarter lower bound and unequal-rank cases, including pairs with one rank seven, are not asserted here.

### 94.2. The fixed support and the exact second-order prerequisite

**Proof of Theorem 94.1.** The established positive lower bound makes a hypothetical subquarter value t positive. Theorems 92.1–92.2 supply a common stress support S and a reciprocal diagonal-unitary gauge preserving the complete product coefficient and target. Fix this one gauge. There is one fixed vector a, nonzero exactly on S, such that

\[
 \ker G=\ker H=\operatorname{span}(a),\qquad G_S=H_S.
                                                                    \tag{2}
\]

The full Grams need not coincide outside S. Every cross-fibre entry of both Grams is nonzero, since the original matrix-unit test gives |1/2−G_ijH_ij|≤t<1/2.

Let 𝒜₀ be the nonempty compact common-witness subset from section 92.5, retaining both ρ and W. For every (ρ,W)∈𝒜₀, its first stress has the form α_W aa* with α_W>0. The same fixed a and the same gauge are used for all these witnesses. For every Hermitian D supported on S with D_ff=0 and Da=0, section 92.5 proves

\[
 \begin{gathered}
 \text{there exists }(\rho,W)\in\mathcal A_0
                    \text{ such that }Q_W(D)\ge0,\\
 Q_W(D)=-\alpha_W
      \sum_{i,j\text{ in different fibres}}
       \frac{\overline{a_i}a_j}{G_{ij}}D_{ij}^{2}.
 \end{gathered}                                                   \tag{3}
\]

The witness may depend on D. No single second-order witness for all directions is assumed. Instead, (3) rules out any one direction whose quadratic value is negative for every common witness; the only witness-dependent factor in that value is α_W>0.

Write n=|S| and introduce the weighted principal matrix

\[
 J=\operatorname{diag}(\overline{a_S})G_S
                  \operatorname{diag}(a_S),\qquad
 h_{ij}=J_{ij},\qquad d_i=J_{ii}=|a_i|^2>0,
 \qquad J\mathbf1_n=0.                                      \tag{4}
\]

Its distinct within-fibre entries vanish, and its cross-fibre entries are nonzero. The following lemma uses these complex entries without assuming they are positive or real.

### 94.3. A quartet direction embedded in the original eight coordinates

**Lemma 94.2.** Choose any ordered four distinct coordinates in S, denoted 1,2,3,4, such that the five edges 13,14,23,24,34 join different original fibres. Then

\[
 h_{13}+h_{14}=0,\qquad h_{23}+h_{24}=0.                     \tag{5}
\]

There is no requirement that coordinates 1 and 2 lie in the same fibre.

**Proof.** Put

\[
 A=\frac1{h_{13}}+\frac1{h_{14}},\qquad
 B=\frac1{h_{23}}+\frac1{h_{24}},\qquad C=\frac1{h_{34}}.     \tag{6}
\]

For arbitrary x∈C and s∈R, define E on these four coordinates by

\[
 E=\begin{pmatrix}
 0&0&x&-x\\
 0&0&-x+is&x-is\\
 \overline x&-\overline x-is&0&is\\
 -\overline x&\overline x+is&-is&0
 \end{pmatrix},                                             \tag{7}
\]

and set every other entry on S to zero. This matrix is Hermitian and each of its rows sums to zero. Its diagonal entries and its 12 edge vanish. Every potentially nonzero edge lies between different original fibres by hypothesis, even when the deliberately omitted 12 edge is also a cross-fibre edge.

On S set

\[
 D_S=\operatorname{diag}(1/\overline{a_S})\,E\,
                         \operatorname{diag}(1/a_S),
 \qquad D_{ij}=0\ \text{if }i\notin S\text{ or }j\notin S.
                                                                    \tag{8}
\]

This defines a Hermitian matrix on all eight original coordinates. All divisions are legitimate, D_ff=0 on every original two-coordinate fibre, and Da=0 because E1_n=0. Since (2) gives the full one-dimensional kernels, both G+εD and H−εD remain PSD for sufficiently small real ε: on a⊥ the unperturbed matrices are positive definite, and D annihilates a. They remain in their exposed support faces and retain every identity fibre block. Also D is supported where G=H, so the exact coefficient error along this feasible opposite-face path is

\[
 T-(G+\varepsilon D)\odot(H-\varepsilon D)
       =T-G\odot H+\varepsilon^2(D\odot D).                 \tag{9}
\]

The bare path by itself only concerns the full norming set. The restriction to common witnesses in this argument is precisely the fixed-direction selection (3), whose second-order drift and compact minimax proof are already established in section 92.5. Nothing stronger is inferred from (9).

Using E_ij²/h_ij=conjugate(a_i)a_jD_ij²/G_ij, and pairing each edge with its Hermitian reverse, equation (3) becomes

\[
 \begin{aligned}
 Q_W(D)&=-2\alpha_W\operatorname{Re}\Phi(x,s),\\
 \Phi(x,s)&=x^2(A+B)-2isxB-s^2(B+C).
 \end{aligned}                                                 \tag{10}
\]

Consequently Re Φ(x,s)≤0 for every complex x and real s. Otherwise one fixed choice would make Q_W(D)<0 for every common witness, contradicting (3).

Set s=0. If A+B≠0, choose a complex square root with x²(A+B)=1. This is impossible by (10), so A+B=0. If B≠0, instead set

\[
 s=1,\qquad x=\frac{i[1+\operatorname{Re}(B+C)]}{2B}.
                                                                    \tag{11}
\]

Then −2ixB=1+Re(B+C) and Re Φ(x,1)=1. This again gives the common negative value Q_W(D)=−2α_W. Therefore B=0 and A=0. The denominators in (6) are nonzero, so these equalities are exactly (5).

Applying this lemma to several quartets imposes simultaneous equations only on the same fixed G and a. Each violated equation would separately supply a direction negative for every common witness. The argument never combines independently selected witnesses or exchanges quadratic minimax quantifiers.

### 94.4. The four remaining occupancy contradictions

By Theorems 92.3–92.4, a hypothetical doubly rank-seven subquarter minimum has support on at most five coordinates meeting at least three original fibres. Corollary 93.3 excludes (1,1,1,0), using the sharp complex rank-at-most-two three-vector theorem and its complete-norm consumer. Thus only the following four patterns remain before applying Lemma 94.2:

\[
 (2,1,1,0),\qquad (1,1,1,1),\qquad
                    (2,1,1,1),\qquad (2,2,1,0).             \tag{12}
\]

Here occupancies refer to the original fibres; a zero means a whole absent fibre.

For (2,1,1,0), let 1,2 be the full fibre and 3,4 the singleton coordinates. All five edges in the lemma are cross-fibre. Equation (5) and the first weighted kernel row give

\[
 h_{13}+h_{14}=0,\qquad
 0=d_1+h_{13}+h_{14}=d_1>0,                                \tag{13}
\]

a contradiction. In the notation (6), the same contradiction appears as B=−d₂/(h₂₃h₂₄)≠0, so the second step of the lemma supplies a strict common negative direction.

For (1,1,1,1), keep coordinate 1 in the first position and choose the omitted partner successively as 2,3,4. Every quartet has all five required cross-fibre edges. Equation (5) gives

\[
 h_{13}+h_{14}=0,\qquad h_{12}+h_{14}=0,\qquad
 h_{12}+h_{13}=0.                                         \tag{14}
\]

These equations force all three entries to vanish, contradicting cross-fibre nonvanishing. The omitted edge may be cross-fibre: setting it to zero in the direction (7) is permitted by the original constraints.

For (2,1,1,1), let 1,2 be the full fibre and 3,4,5 the singleton coordinates. Apply the lemma to (1,2,j,k) for all three pairs from {3,4,5}. It gives

\[
 h_{13}+h_{14}=0,\qquad h_{13}+h_{15}=0,\qquad
 h_{14}+h_{15}=0,                                         \tag{15}
\]

so these nonzero cross-fibre entries would all vanish.

For (2,2,1,0), let {1,2} and {3,4} be the full fibres and let 5 be the singleton. Apply the lemma using the full first fibre and the pairs (3,5),(4,5). For each i∈{1,2}, the two conclusions and its weighted kernel row imply

\[
 h_{i3}=h_{i4}=-h_{i5},\qquad
 0=d_i+h_{i3}+h_{i4}+h_{i5}=d_i-h_{i5},
 \qquad h_{i5}=d_i>0.                                    \tag{16}
\]

Reverse the roles of the two full fibres to obtain h_j5=d_j>0 also for j∈{3,4}. The singleton row now contradicts positivity:

\[
 0=d_5+\sum_{i=1}^4 h_{5i}
   =d_5+\sum_{i=1}^4 d_i>0.                              \tag{17}
\]

The conjugations are retained: Hermiticity gives h₅ᵢ=conjugate(hᵢ₅)=d_i only after (16) has forced hᵢ₅ to be positive real. No positive gauge was assumed.

All four patterns in (12) are excluded. Together with Corollary 93.3 and the earlier support-size and two-fibre exclusions, this exhausts the hypothetical doubly rank-seven subquarter support. Theorem 94.1 follows.

### 94.5. Consequence for the attained calibrated global problem

**Corollary 94.3.** If the unrestricted original-channel optimum is strictly below 1/4, an attained calibrated minimizer has local Gram ranks between three and seven, with at least one rank at most six.

**Proof.** Apply the physical global calibration theorem of section 72 and the compact Gram formulation. The common-stress and earlier rank-two bounds in section 92.3 place both ranks in {3,4,5,6,7}. A global minimizer is a local minimum, so Theorem 94.1 excludes the pair (7,7).

This corollary excludes neither unequal pairs with one rank seven nor pairs with both ranks at most six. The active-support equalization and full one-dimensional-kernel face directions used above do not automatically extend to those cases. No rank-preserving calibration, convex extreme-point reduction, or transfer of local minimality from leaking channels has been used. The unrestricted original optimum remains in [√3−3/2,1/4].

The dependencies are the original calibrated adaptive norm of section 91; the same-witness, support, fixed-direction, support-size, and two-fibre results of section 92; and the quantitative three-singleton exclusion of section 93. The additional argument here is the explicit complex quartet tangent and its weighted row contradictions. It does not require the earlier singular-error or interior-density necessary conditions for three-singleton support, or a real gauge, small-norm transversal, or reciprocal-Gram positivity assertion.

## 95. A PSD quotient and full-support rank-(7,6) exclusion

### 95.1. Original channels, exact objective, and scope

Retain the original local CPTP maps A,B:C⁸→C⁴, the four original two-coordinate fibres, the correlated input encoding |f,i〉↦|f,i〉|f,i〉, the output encoding |f〉↦|ff〉, and the arbitrary-reference unhalved diamond error. On the calibrated domain put

\[
 \begin{aligned}
 \mathcal E&=\{G=G^*\ge0:G_{ff}=I_2\text{ for every fibre }f\},\\
 \mathcal C&=\{(\rho,W):\rho=\bigoplus_f\rho_f\ge0,
                    \ \operatorname{Tr}\rho=1,\ 0\le W\le\rho\},\\
 T_{ff}&=I_2,\qquad T_{fg}=J_2/2\quad(f\ne g),\\
 F(G,H)&=\max_{(\rho,W)\in\mathcal C}
                 2\operatorname{Tr}[(T-G\odot H)W].
 \end{aligned}                                                     \tag{1}
\]

Section 91 identifies (1) exactly with that calibrated physical error. Every local minimum below means a local minimum on the full domain 𝓔×𝓔, rather than on a fixed-rank stratum.

**Theorem 95.1.** Suppose (G,H) is such a local minimum with 0<F(G,H)<1/2, rank G=7, and a vector spanning ker G has all eight coordinates nonzero. Then rank H≠6. The statement also holds with the two parties interchanged.

The proof first obtains a supported positive correlation quotient for any rank-seven first Gram, and then a necessary quadratic inequality with its full opposite-kernel constraint. In the full-support rank-(7,6) case, explicit complex directions contradict that inequality for every possible number, from zero to four, of singular quotient fibre blocks. No positivity or reality of cross-fibre entries is assumed.

This theorem excludes a class of calibrated local minima at every positive subhalf value. It makes no claim about arbitrary rank-(7,6) competitors, rank-seven kernels with missing coordinates, or smaller opposite ranks. The calibration comparison in section 72 may enlarge ranks and does not transfer local minimality from an arbitrary leaking pair. The unrestricted optimum remains between √3−3/2 and 1/4.

### 95.2. One rank-seven side gives a supported PSD quotient

For this subsection retain that (G,H) is a local minimum on the full calibrated domain, with 0<t=F(G,H)<1/2 and rank G=7; no full-support or opposite-rank hypothesis is imposed. Fix one nonzero a spanning ker G and let S=supp(a). Set L=T−G⊙H. Let 𝒜 be the compact convex set of norming pairs (ρ,W) in (1), and define

\[
 b(W;G',H')=-2\operatorname{Tr}
  [((G'-G)\odot H+G\odot(H'-H))W],
 \qquad G',H'\in\mathcal E.                                  \tag{2}
\]

The simultaneous first-order result of section 92 supplies the nonempty compact convex common-witness subset

\[
 \mathcal A_0=\{(\rho,W)\in\mathcal A:
             b(W;G',H')\ge0\text{ for all }G',H'\in\mathcal E\}.
                                                                    \tag{3}
\]

For every pair in this subset there are complementary PSD stresses

\[
 \begin{aligned}
 P_A&=\operatorname{blockdiag}(\Lambda_A)
                           -2\overline H\odot W\ge0,
       &P_AG&=0,\\
 P_B&=\operatorname{blockdiag}(\Lambda_B)
                           -2\overline G\odot W\ge0,
       &P_BH&=0.
 \end{aligned}                                                     \tag{4}
\]

Both stresses are nonzero by the positive-subhalf argument of section 92. Thus P_A=αaa* with α>0. Moreover every cross-fibre entry of G and H is nonzero: the original matrix-unit test gives |1/2−G_ijH_ij|≤t<1/2. Equating the cross-fibre entries in (4) gives

\[
 W_{ij}=-\frac{\alpha a_i\overline{a_j}}{2\overline{H_{ij}}},
 \qquad
 (P_B)_{ij}=\alpha a_i\overline{a_j}
                           \frac{\overline{G_{ij}}}{\overline{H_{ij}}}
 \quad(i,j\text{ in different fibres}).                         \tag{5}
\]

**Lemma 95.2.** For each common witness, P_B is supported on S, with (P_B)_ii=α|a_i|². The matrix

\[
 R=\alpha^{-1}\operatorname{diag}(1/a_S)(P_B)_{SS}
                         \operatorname{diag}(1/\overline{a_S})
                                                                    \tag{6}
\]

is PSD with diagonal one, and satisfies

\[
 G_S=H_S\odot\overline R,\qquad
 R\operatorname{diag}(\overline{a_S})H_S=0.                    \tag{7}
\]

If n=|S|, h=rank H_S, and r=rank R, then

\[
 \operatorname{rank}G_S=n-1,\qquad h+r\le n,\qquad
 n-1\le hr,\qquad r\le8-\operatorname{rank}H.                 \tag{8}
\]

**Proof.** If i∉S, (5) makes every cross-fibre entry in row i of P_B zero. Since H_ff=I₂, the diagonal equation (P_BH)_ii=0 then gives (P_B)_ii=0. A PSD matrix with a zero diagonal entry has a zero corresponding row and column. Thus P_B is supported on S. For any i, the same complementary equation yields

\[
 \begin{aligned}
 (P_B)_{ii}
  &=-\alpha a_i\sum_{j\text{ outside }i\text{'s fibre}}
                            \overline{a_j}\,\overline{G_{ij}}\\
  &=-\alpha a_i\overline{\sum_{j\text{ outside }i\text{'s fibre}}
                                                  G_{ij}a_j}
   =\alpha|a_i|^2.
 \end{aligned}                                                     \tag{9}
\]

The last equality uses Ga=0 and G_ff=I₂. Formula (6) is an invertible diagonal congruence of (P_B)_SS divided by α>0, so R is PSD with unit diagonal. Equation (5) gives R_ij=overline(G_ij)/overline(H_ij) on cross-fibre entries. The first identity in (7) also holds on diagonal entries and on the zero distinct within-fibre entries, regardless of the corresponding entries of R. The second follows from P_BH=0 and support of P_B.

Every kernel vector of the principal PSD matrix G_S extends by zero to a vector in ker G. Since that full kernel is span(a), dim ker G_S=1. The second identity in (7) gives h+r≤n. Gram factorizations of H_S and overline R realize their Hadamard product by tensor products of records of dimensions h and r, so its rank is at most hr. Finally rank R=rank P_B and P_BH=0 give the last inequality in (8). ∎

The quotient need not be rank one. Its cross-fibre entries are determined by the quotient formula; that formula does not specify its within-fibre entries, which are not needed for the cross-fibre quadratic coefficients below. In particular, when S contains all eight coordinates and rank H=6, one has r≤2. If r=1, its unit diagonal makes R=uu* with |u_i|=1, and (7) makes G a diagonal-unitary conjugate of H, contradicting their different ranks. Hence

\[
 \operatorname{rank}R=2,\qquad
 P_B=\alpha\operatorname{diag}(a)R\operatorname{diag}(\overline a),
 \qquad \operatorname{range}(P_B)=\ker H.                    \tag{10}
\]

These assertions alone are necessary conditions. The proof must still retain both the full opposite kernel and the exact product variation.

### 95.3. Joint face tangents with the full kernel constraint

Continue with the general support S. Fix one pair in 𝒜₀ only to define R by (6). Let D be any Hermitian matrix on all eight coordinates, supported on S×S, such that

\[
 D_{ff}=0\text{ on every original fibre},\qquad
 D\ker H=0.
                                                                    \tag{11}
\]

Define D_G=−overline R⊙D on S×S and extend it by zero elsewhere. All subsequent Hadamard expressions involving this principal R and full eight-coordinate directions are formed on S×S and extended by zero outside that set. It is Hermitian and has zero original fibre blocks. Since range(P_B)⊆ker H, (11) implies DP_B=0 and therefore

\[
 D_S\operatorname{diag}(a_S)R=0,\qquad
 (D_Ga)_i=-\sum_j D_{ij}a_jR_{ji}=0.                         \tag{12}
\]

For the second equality, the sum is the i-th diagonal entry of the first matrix in (12); outside S it vanishes by support. Thus D_G annihilates the entire kernel of G. Equation (7) also gives

\[
 D_G\odot H+G\odot D=0,\qquad
 T-(G+sD_G)\odot(H+sD)
       =L+s^2\overline R\odot(D\odot D).                   \tag{13}
\]

The entrywise square in this formula is not an absolute square. Both Gram paths are feasible for every sufficiently small real s. Indeed a Hermitian direction annihilating the full kernel acts only on its orthogonal complement, where the unperturbed Gram is positive definite. Small perturbations remain PSD, and every original fibre block remains I₂.

**Lemma 95.3.** For every fixed D satisfying (11), some pair (ρ,W)∈𝒜₀ satisfies

\[
 Q_W(D):=2\operatorname{Tr}[(\overline R\odot D\odot D)W]\ge0.
                                                                    \tag{14}
\]

**Proof.** The selection is made with D fixed. Given M>0 and arbitrary G′,H′∈𝓔, put V_G=M(G′−G), V_H=M(H′−H). The paths

\[
 G_s=G+sD_G+s^2V_G,\qquad H_s=H+sD+s^2V_H                 \tag{15}
\]

are feasible for sufficiently small s. For example,

\[
 G_s=(1-Ms^2)\left(G+\frac{sD_G}{1-Ms^2}\right)+Ms^2G'
                                                                    \tag{16}
\]

is a convex combination of feasible matrices; the H path has the same form. Expansion gives the coefficient L plus

\[
 s^2[\overline R\odot D\odot D-V_G\odot H-G\odot V_H]+O(s^3).
                                                                    \tag{17}
\]

The remainder is uniform against the compact witness set 𝓒. The compact-max derivative formula at scale s², together with local minimality, therefore gives

\[
 \max_{(\rho,W)\in\mathcal A}
       [Q_W(D)+M b(W;G',H')]\ge0
                \quad\text{for every }G',H'\in\mathcal E.          \tag{18}
\]

There is one pair in 𝒜 satisfying all the inequalities inside (18) simultaneously. Otherwise compactness would give finitely many with empty intersection. Their affine image of the compact convex set 𝒜 would be strictly separated from the nonnegative orthant by nonnegative coefficients. Normalize those coefficients to sum to one. The resulting convex average of the corresponding feasible pairs G′,H′ contradicts (18). This separation uses only affine variables; the direction D remains fixed.

Call the resulting pair (ρ_M,W_M). Taking G′=G and H′=H gives Q_(W_M)(D)≥0. The Q values are uniformly bounded on 𝒜. Along a convergent subsequence as M→∞, the inequalities give b(W_*;G′,H′)≥0 for every fixed feasible pair. The limit belongs to 𝒜₀ and still has Q_(W_*)(D)≥0. This proves (14). ∎

For every common witness, (5) has the same fixed G,H,a and some α_W>0. Substitution into (14), retaining the reversed indices in the trace, gives

\[
 \begin{aligned}
 Q_W(D)&=\alpha_W q(D),\\
 q(D)&=-\sum_{\substack{i,j\in S\\i,j\text{ in different fibres}}}
       \frac{\overline{a_i}a_j\overline{R_{ij}}}{H_{ij}}D_{ij}^2.
 \end{aligned}                                                     \tag{19}
\]

The ordered summands for (i,j) and (j,i) are conjugates, so q is real. Its cross-fibre coefficients do not depend on the common witness, and its remaining entries vanish. Consequently Lemma 95.3 and α_W>0 imply q(D)≥0 for every admissible D. This does not interchange the direction and witness quantifiers: a witness may be selected separately for each fixed D because every such selection gives a strictly positive multiple of the same real number q(D).

Introduce weighted coordinates

\[
 E_D=\operatorname{diag}(\overline{a_S})D_S\operatorname{diag}(a_S),
 \qquad J=\operatorname{diag}(\overline{a_S})H_S
                                         \operatorname{diag}(a_S).
                                                                    \tag{20}
\]

Then E_D is Hermitian, its original fibre blocks vanish, E_DR=0 by (12), and

\[
 q(D)=-\sum_{\substack{i,j\in S\\i,j\text{ in different fibres}}}
               \frac{\overline{R_{ij}}}{J_{ij}}(E_D)_{ij}^2\ge0.
                                                                    \tag{21}
\]

In general E_DR=0 does not by itself replace the full-kernel condition (11). The replacement is guaranteed when range(P_B)=ker H; no converse on the restricted direction space is asserted. In the full-support rank-(7,6) case, (10) gives exactly that equality. Invertible diagonal multiplication then makes (11) equivalent to E_DR=0.

### 95.4. The resulting rank-two algebraic problem

Under the hypotheses of Theorem 95.1 with rank H=6, put

\[
 c_{ij}=\frac{\overline{R_{ij}}}{J_{ij}}
          \quad(i,j\text{ in different fibres}),\qquad
 \mathcal V=\{E=E^*:E_{ff}=0,\ ER=0\}.
                                                                    \tag{22}
\]

All these coefficients are nonzero, and c_ji=overline(c_ij). Equations (19)–(21) give a single real quadratic form

\[
 q(E)=-\sum_{i,j\text{ in different fibres}}c_{ij}E_{ij}^{2}
                         \ge0\qquad(E\in\mathcal V).        \tag{23}
\]

Here and below q(E) denotes the same form expressed in weighted coordinates. Factor R=U*U, where U is a rank-two 2×8 matrix, and write U_f for its four 2×2 fibre blocks. Then ER=0 is equivalent to EU*=0. Each U_f has rank one or two, since each column of U has norm one. We will contradict (23) in every case.

We use the elementary fact that for a nonnegative real quadratic form, a zero vector of the form lies in its radical:

\[
 q(X)=0\quad\Longrightarrow\quad
 B_q(X,Y)=0\text{ for every }Y,\qquad
 B_q(X,Y)=\frac{q(X+Y)-q(X)-q(Y)}2.                         \tag{24}
\]

Indeed q(X+sY)=2sB_q(X,Y)+s²q(Y) is nonnegative for both signs of all sufficiently small real s, forcing its linear coefficient to vanish.

### 95.5. Singular fibres give complex star directions

Suppose U_f has rank one. Choose a nonzero vector n supported on fibre f with Un=0. Both coordinates of n are nonzero, since each of the two columns of U_f is nonzero. If v∈ker U has v_f=0 and z∈C, define

\[
 S_f(z,v)=z n v^*+\overline z\,v n^*.
                                                                    \tag{25}
\]

This full eight-coordinate matrix is Hermitian, has zero entire original fibre blocks, and annihilates U*. It therefore belongs to 𝓥 and is supported only on edges incident to f. Its value in (23) is

\[
 q(S_f(z,v))=-2\operatorname{Re}[z^2A_f(v)],\qquad
 A_f(v)=\sum_{i\in f,\,j\notin f}c_{ij}n_i^2\overline{v_j}^{2}.
                                                                    \tag{26}
\]

Since every complex z is allowed, nonnegativity forces A_f(v)=0. Every star (25) thus has zero polarization with every member of 𝓥 by (24).

**At least two singular fibres.** Choose two singular fibres f,g whose complement C, consisting of the other two fibres, has rank U_C=2. Such a choice always exists. With exactly two or three singular fibres, the complement of any chosen two contains an invertible fibre. If all four are singular, rank U=2 gives two independent fibre column lines; choose those as C and the other two as f,g.

Let n_f,n_g be local kernel vectors on f,g. For arbitrary p∈C² on f and r∈C² on g, choose v,w∈ker U with

\[
 v_f=0,\quad v_g=r,\quad U_Cv_C=-U_gr,\qquad
 w_g=0,\quad w_f=p,\quad U_Cw_C=-U_fp.                    \tag{27}
\]

These equations are solvable because U_C is surjective. The two stars S_f(z,v), S_g(y,w) overlap only on the cross block fg. Their zero polarization is

\[
 -2\operatorname{Re}\left[
 z\overline y\sum_{i\in f,\,j\in g}
       c_{ij}(n_f)_i p_i\overline{r_j}\,\overline{(n_g)_j}
                         \right]=0.                       \tag{28}
\]

Arbitrary complex phase of z makes the inner sum zero. Taking p and r to be individual coordinate vectors gives c_ij(n_f)_i overline((n_g)_j)=0 for every entry of that cross block. Both local kernel vectors have no zero coordinate, so every such c_ij is zero, contradicting (22). This excludes two, three, and four singular fibres, including all complex-phase and coincident-line possibilities.

**Exactly one singular fibre.** Let f be the singular fibre and g,h,k the three invertible ones. Fix its local kernel vector n. For arbitrary u∈C² define v∈ker U by

\[
 v_g=U_g^{-1}u,\qquad v_h=-U_h^{-1}u,\qquad v_f=v_k=0.
                                                                    \tag{29}
\]

For arbitrary p∈C² choose w∈ker U with w_f=p, w_k=−U_k⁻¹U_fp, and w_g=w_h=0. The matrix Y=wv*+vw* is Hermitian and annihilates U*. Its vector supports lie in the disjoint groups of entire fibres {f,k} and {g,h}, so its original fibre blocks vanish. Thus Y∈𝓥. Its edges shared with S_f(z,v) are exactly fg and fh. Their zero polarization, with arbitrary complex phase of z, yields

\[
 \sum_{i\in f}n_i p_i
  \left[\sum_{j\in g}c_{ij}\overline{(U_g^{-1}u)_j}^{2}
       +\sum_{j\in h}c_{ij}\overline{(U_h^{-1}u)_j}^{2}
  \right]=0.                                                 \tag{30}
\]

Every n_i is nonzero and p is arbitrary, so each bracket vanishes. For fixed i∈f set

\[
 Q_\ell(u)=\sum_{j\in\ell}c_{ij}
                    \overline{(U_\ell^{-1}u)_j}^{2},
                     \qquad \ell\in\{g,h,k\}.                \tag{31}
\]

Apply (29)–(30) to each pair of invertible fibres, using the remaining invertible fibre to construct w. This gives Q_g+Q_h=Q_g+Q_k=Q_h+Q_k=0, hence every Q_ℓ vanishes identically. Since U_ℓ is invertible, U_ℓ⁻¹u ranges over C². Its two coordinate-vector values force both corresponding coefficients c_ij to vanish. This again contradicts (22), excluding one singular fibre.

### 95.6. Four invertible fibres give four-vertex directions

It remains to exclude zero singular fibres. For arbitrary u∈C² put x_f(u)=U_f⁻¹u. For every Hermitian 4×4 matrix Z with diagonal zero and Z1₄=0, define the full eight-coordinate matrix

\[
 E_{fg}=Z_{fg}x_f(u)x_g(u)^*\quad(f\ne g),\qquad E_{ff}=0.
                                                                    \tag{32}
\]

This is Hermitian, preserves every original fibre block, and satisfies EU*=0: its f-th block row against U* is x_f(u)(Σ_gZ_fg)u*=0. Substitution into (23) therefore gives

\[
 \begin{aligned}
 -\sum_{f\ne g}k_{fg}(u)Z_{fg}^{2}&\ge0,\\
 k_{fg}(u)&=\sum_{i\in f,\,j\in g}
          c_{ij}x_f(u)_i^2\overline{x_g(u)_j}^{2}.
 \end{aligned}                                                     \tag{33}
\]

For fixed u the coefficients satisfy k_gf=overline(k_fg). The following elementary four-vertex observation forces every one of them to vanish. Use the Hermitian zero-row-sum matrix with upper entries

\[
 Z_{12}=0,\quad Z_{13}=x,\quad Z_{14}=-x,\quad
 Z_{23}=-x+is,\quad Z_{24}=x-is,\quad Z_{34}=is,
 \qquad x\in\mathbb C,\ s\in\mathbb R.                     \tag{34}
\]

With A=k₁₃+k₁₄, B=k₂₃+k₂₄, C=k₃₄, the left side of (33) is −2Re Φ, where

\[
 \Phi=(A+B)x^2-2isBx-s^2(B+C).                              \tag{35}
\]

Setting s=0 and varying complex x gives A+B=0. If B≠0, take s=1 and x=i[1+Re(B+C)]/(2B). Then Re Φ=1, contradicting (33). Thus B=0 and A=0. Relabeling the four vertices gives all three pairwise sums of the coefficients in any fixed row equal to zero. Each coefficient is therefore zero. In particular, k_fg(u)=0 for every u.

To recover the original 2×2 coefficient block C_fg=(c_ij)_(i∈f,j∈g), set m(u)=(u₁²,u₁u₂,u₂²)ᵀ and write x_f(u)⊙x_f(u)=A_fm(u). The 2×3 matrix A_f has rank two: its rows are squares of two independent linear forms, whose squares remain linearly independent. Hence

\[
 m(u)^T A_f^T C_{fg}\overline{A_g}\,\overline{m(u)}=0
                                      \quad(u\in\mathbb C^2).       \tag{36}
\]

The nine monomials of bidegree (2,2) in u and overline u are linearly independent as polynomials in the four real coordinates of u. Indeed the change of variables from those real coordinates to u₁,u₂,overline(u₁),overline(u₂) is invertible over C. Thus (36) gives A_fᵀC_fg overline(A_g)=0. Since A_fᵀ has full column rank and overline(A_g) has full row rank, C_fg=0. This contradicts (22), excluding zero singular fibres.

### 95.7. Exhaustion and the remaining global problem

The quotient has exactly zero, one, two, three, or four singular original fibre blocks. Sections 95.5–95.6 exclude every case, proving Theorem 95.1. All directions were embedded in the original eight coordinates, had zero entire original fibre blocks, and annihilated the full opposite kernel through (10). Every common-witness quadratic used the same fixed G,H,a and the same cross-fibre quotient. Complex phases were varied explicitly rather than discarded by a real gauge.

The new exclusion uses the exact adaptive objective and simultaneous common stresses of sections 91–92, the quotient of Lemma 95.2, and the fixed-direction argument of Lemma 95.3. It does not require the sharp three-vector theorem or the doubly rank-seven support-size reduction. Section 94 separately excludes all doubly rank-seven subquarter calibrated local minima.

A hypothetical global subquarter optimum can still lie at a calibrated minimum whose rank-seven kernel has smaller coordinate support, whose opposite Gram has rank at most five, or whose two ranks are both at most six, subject to the earlier reductions. Neither a missing whole fibre nor a single missing coordinate is covered by Theorem 95.1. In smaller opposite ranks, annihilating R need not annihilate the full opposite kernel. No rank-preservation assertion under calibration or unsupported reduction to extreme Grams is used. The unrestricted quarter lower bound for the original channels, including leakage, remains open.

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

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

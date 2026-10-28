# Higuchi-Sudbery rigidity, marginal fibers and minimal interaction locality

## 1. Scope and mathematical inputs

This is an ordinary mathematical continuation of the existing [HS4 dossier](../../../Problems/higuchi-sudbery-2000-four-qubit-average-entropy-maximum.md). Its new statements have not been formalized in Lean. The existing maximum theorem and its degree-six certificate remain unchanged. Historical originality of the continuation is not asserted.

Throughout, A,B,C,D are labelled qubits, psi is a normalized pure state in (C^2)^{tensor 4}, and the three cuts are AB|CD, AC|BD, AD|BC, in that order. The amplitude index is 8a+4b+2c+d. Local-unitary equivalence means a product of four one-qubit unitaries, allowing a global phase and **not** allowing a permutation of the four parties unless explicitly stated.

Let rho_c be the two-qubit marginal of cut c, lambda_{c,j} its four eigenvalues, and

$$F(\psi)=\frac{1}{3}\sum_c S_2(\rho_c),\qquad F_*=1+\frac12\log_2 3,\qquad \Delta=F_*-F(\psi).$$

Here S_2 denotes von Neumann entropy with logarithm base 2; the subscript specifies the logarithm base, not Renyi order. Below Renyi entropy is denoted R_alpha instead. Put

$$P=\sum_c\operatorname{Tr}\rho_c^2,\qquad E=\sum_c e_3(\operatorname{spec}\rho_c),\qquad e_3(v)=\sum_{i<j<k}v_iv_jv_k.$$

The actual inputs already present in the HS4 development are P>=1, E<=5/36, and the cubic entropy majorant. Their owners are `HS4Assembly.literal_purity_identity`, `HS4Assembly.spectrum_e3_eq_minors`, `PrimeHierarchyCertificate.prime_certificate_identity`, `ReflectionEvaluation.ref_eval_rhs_nonneg`, and `HermiteEntropy.hermite_majorant`, including their private live proof components under `D5/S3/Quantum/Entanglement/HiguchiSudbery/`. This text reuses those mathematical inputs; it does not replace their kernel proof with numerical tests.

The only external classification input used below is the one-uniform normal-form theorem, Gour-Wallach [GW10], Theorem 5: every normalized four-qubit pure state with all four one-qubit marginals equal to I_2/2 is locally unitarily equivalent to a vector in the Bell-product subspace A. That theorem is used with all its hypotheses. The uniqueness sentence of their Theorem 10 is **not** used. Sections 3 and 4 keep the complex-conjugate branches distinct for labelled parties.

## 2. Exact entropy-deficit decomposition and quantitative rigidity

All logarithms in this section are natural unless a base is shown. Define

$$a=\frac16,\quad b=\frac12,$$

$$p(x)=\frac{4-3\ln3}{8}+\frac{-11+2\ln2+12\ln3}{2}x+\frac{36-39\ln3}{2}x^2+18(\ln3-1)x^3,$$

$$g(x)=p(x)+x\ln x,\qquad 0\ln0:=0,$$

and

$$A=\frac{11+2\ln2-9\ln3}{2},\quad B=\frac32(5\ln3-6)<0,\quad C=54(\ln3-1)>0.$$

### Proposition 2.1. Deficit identity

For every normalized four-qubit pure state,

$$\boxed{3\ln2\,\Delta=\sum_{c,j}g(\lambda_{c,j})+(-B)(P-1)+C\left(\frac5{36}-E\right).} \tag{2.1}$$

All three terms on the right are nonnegative.

Proof. For a normalized four-entry spectrum v, Newton's identity gives

$$\sum_jv_j^3=\frac{3\sum_jv_j^2-1}{2}+3e_3(v).$$

Substitution in the displayed cubic gives sum_j p(v_j)=A+B sum_j v_j^2+C e_3(v). Summing over the three cuts, subtracting their actual entropies, and using

$$3A+B+\frac5{36}C=3\ln2+\frac32\ln3$$

gives (2.1). Nonnegativity uses the actual scalar majorant and the two coupled bounds from Section 1. No independently chosen or incompatible marginal spectra are introduced. QED.

### Proposition 2.2. Spectral stability and the equality set

For 0<=x<=1,

$$g(x)\ge\frac1{12}(x-a)^2(x-b)^2. \tag{2.2}$$

Consequently,

$$\sum_c\left\|(\rho_c-aI_4)(\rho_c-bI_4)\right\|_F^2\le36\ln2\,\Delta, \tag{2.3}$$

$$P-1\le\frac{3\ln2}{-B}\Delta,\qquad \frac5{36}-E\le\frac{3\ln2}{C}\Delta. \tag{2.4}$$

Moreover, Delta=0 if and only if all three marginal spectra equal {1/2,1/6,1/6,1/6}.

Proof. The polynomial p has double contact with -x ln x at a,b. For x>0 away from these two nodes, the Hermite remainder formula on the interval containing x,a,b gives

$$g(x)=\frac{2}{24\xi^3}(x-a)^2(x-b)^2$$

for some 0<xi<=1. This proves (2.2); continuity supplies x=0, and the two contact points have zero gap. Equations (2.3)-(2.4) follow by dropping nonnegative terms in (2.1). If Delta=0, (2.2) forces every eigenvalue to lie in {a,b}. If k of the four eigenvalues equal b, normalization reads 1=(4-k)/6+k/2, hence k=1. The converse follows by evaluating the entropy. QED.

For a basis-free version of the exact spectral conclusion, define Q_c=3rho_c-I_4/2. At equality, Q_c is a rank-one orthogonal projector and rho_c=(I_4+2Q_c)/6. Equation (2.3) also gives

$$\sum_c\|Q_c^2-Q_c\|_F^2\le2916\ln2\,\Delta.$$

This controls distance to projector equations. It is not by itself a bound on distance of the full state to one particular LU orbit.

### Proposition 2.3. One-body rigidity

Write rho_X=(I_2+r_X dot sigma)/2, and let

$$\tau_4=\left|\psi^T\sigma_y^{\otimes4}\psi\right|^2.$$

The literal purity identity in the existing code, equivalently [GW10], Theorem 6 with its stated tangle normalization, is

$$2(P-1)=\sum_{X=A,B,C,D}|r_X|^2+\tau_4. \tag{2.5}$$

Thus every maximizer is one-uniform and has tau_4=0. More quantitatively,

$$\sum_X\|\rho_X-I_2/2\|_F^2\le\frac{3\ln2}{-B}\Delta,\qquad \tau_4\le\frac{6\ln2}{-B}\Delta. \tag{2.6}$$

Proof. Each Bloch component is the corresponding diagonal difference or twice the real/imaginary part of the off-diagonal entry in `literal_purity_identity`. Taking its real part with the second amplitude argument equal to the conjugate gives (2.5). Since ||rho_X-I_2/2||_F^2=|r_X|^2/2, (2.6) follows from (2.4). QED.

## 3. Complete maximizer classification for labelled parties

Let H_+=M4 be the explicit state in the dossier, and H_-=conjugate(H_+). Let O_+, O_- be their U(2)^4 orbits on pure-state rays.

### Theorem 3.1. Exactly two LU orbits

$$\boxed{\{\psi:F(\psi)=F_*\}=\mathcal O_+\;\dot\cup\;\mathcal O_-.} \tag{3.1}$$

The two orbits become one if qubit permutations are also allowed.

Proof of completeness. Proposition 2.3 makes every maximizer one-uniform, so [GW10], Theorem 5 applies. Define the real Bell vectors beta_0=phi_+, beta_1=phi_-, beta_2=psi_+, beta_3=psi_-, with the usual normalized plus/minus signs, and u_j=beta_j(AB) tensor beta_j(CD). In this normal form psi=sum_j z_j u_j. Its AB Schmidt probabilities are |z_j|^2, so Proposition 2.2 gives the multiset {1/2,1/6,1/6,1/6}.

The product local Pauli operations X_A X_C and Z_A Z_C permute the coordinates by (02)(13) and (01)(23), respectively, with no remaining signs on the u_j. These permutations act transitively on the four indices. Move the coefficient with squared modulus 1/2 to index 0.

The spin-flip form on the Bell-product subspace is sum_j z_j^2. Therefore tau_4=0 gives

$$z_0^2+z_1^2+z_2^2+z_3^2=0.$$

Now |z_0^2|=1/2=sum_{j=1}^3 |z_j^2|. Equality in the complex triangle inequality forces z_1^2,z_2^2,z_3^2 to have the same phase, opposite to z_0^2. After an overall phase adjustment the vector has coefficients

$$(z_0,z_1,z_2,z_3)=\frac1{\sqrt6}(i\sqrt3,\epsilon_1,\epsilon_2,\epsilon_3),\qquad \epsilon_j\in\{1,-1\}.$$

X_A X_B flips signs at indices 1,3, and Z_A Z_B flips signs at indices 2,3. They remove every even-parity sign pattern among the last three coordinates. If epsilon_1 epsilon_2 epsilon_3=-1, first multiply the entire vector by -1, then remove the resulting even-parity signs. Thus there are at most two orbits, represented by

$$m_\pm=\frac1{\sqrt6}(\pm i\sqrt3\,u_0+u_1+u_2+u_3).$$

The explicit H_+ has Bell-product coordinates (1,-1,-1,i sqrt(3))/sqrt(6). The same displayed Pauli permutations and sign flips take it to m_+; complex conjugation gives the corresponding map for H_-. Both are maxima since conjugation preserves the marginal spectra. This proves coverage of the equality set without using a uniqueness claim from another entropy theorem.

Proof that the orbits are distinct. Let d_c(psi)=det F_c(psi), where F_c is the literal 4 by 4 amplitude flattening for the three cuts, and set

$$\chi(\psi)=\operatorname{Im}\left[d_0(\psi)\overline{d_1(\psi)}\right]. \tag{3.2}$$

Under a product U_A tensor U_B tensor U_C tensor U_D, every d_c is multiplied by the same phase

$$\eta=\left(\det U_A\det U_B\det U_C\det U_D\right)^2.$$

Indeed F_{AB} transforms as (U_A tensor U_B)F_{AB}(U_C tensor U_D)^T, and the other cuts obey the corresponding formula. Therefore chi is invariant under all local unitaries and under global phase. Conjugation reverses its sign. Direct determinant evaluation gives

$$d_0(H_+)=\frac{i\sqrt3}{36},\quad d_1(H_+)=\frac1{24}+\frac{i\sqrt3}{72},\quad d_2(H_+)=\frac1{24}-\frac{i\sqrt3}{72},$$

$$\chi(H_+)=\frac{\sqrt3}{864},\qquad \chi(H_-)=-\frac{\sqrt3}{864}.$$

These nonzero opposite invariants exclude LU equivalence. Finally, swapping C and D sends H_+ exactly to H_-. Hence including permutations identifies the two orbits. QED.

The original [HS00] already exhibits H_+ and its conjugate as separate candidates. The contribution of this continuation is the exhaustive equality-set argument using the existing global certificate, together with an explicit labelled-party separator. No claim is made that the conjugate pair itself is a new discovery.

## 4. The entire two-body marginal fiber

Define

$$R=\begin{pmatrix}1/6&0&0&0\\0&1/3&-1/6&0\\0&-1/6&1/3&0\\0&0&0&1/6\end{pmatrix}=\frac16I_4+\frac13|\psi_-\rangle\langle\psi_-|.$$

Every one of the six two-qubit marginals of H_+ and H_- equals this same real matrix. Also <H_+|H_->=0.

### Theorem 4.1. Exact mixed-state fiber

Among all four-qubit density matrices, with the pair matrices expressed in the fixed computational bases,

$$\boxed{\{\sigma:\sigma_{XY}=R\text{ for every }X<Y\}=\{t|H_+\rangle\langle H_+|+(1-t)|H_-\rangle\langle H_-|:0\le t\le1\}.} \tag{4.1}$$

In particular its only pure states are the two endpoints.

Proof. Let J=(1/2)sum_X sigma_X be total spin and L=J^2. Then

$$L=3I_{16}+\frac12\sum_{X<Y}\boldsymbol\sigma_X\cdot\boldsymbol\sigma_Y\ge0.$$

For R, the expectation of sigma_X dot sigma_Y is -1. Any sigma in the left side of (4.1) therefore has Tr(sigma L)=0. Positivity forces its support into ker L.

An explicit real orthonormal basis of this two-dimensional kernel is

$$e_0=\frac1{\sqrt3}\left[|0011\rangle+|1100\rangle-\frac12(|0101\rangle+|0110\rangle+|1001\rangle+|1010\rangle)\right],$$

$$e_1=\frac12(|0101\rangle-|0110\rangle-|1001\rangle+|1010\rangle).$$

For an elementary dimension check, J_z=0 restricts to the six weight-two strings. J_+=0 imposes the four equations sum_{j!=i} x_{ij}=0. They have rank four and force opposite-edge coefficients equal and their three values to sum to zero. Hence the kernel has dimension two, spanned by e_0,e_1. Conversely J_z=J_+=0 implies J_-=0 by the spin commutator, so these are exactly the zero-total-spin vectors.

On this basis, the swap operators are

$$P_{AB}=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad P_{AC}=\begin{pmatrix}-1/2&-\sqrt3/2\\-\sqrt3/2&1/2\end{pmatrix}.$$

Both swaps have expectation zero in R. If the density matrix on this kernel is [[a,c],[conjugate(c),1-a]], the two expectations force a=1/2 and Re(c)=0. Positivity then requires |Im(c)|<=1/2. Since

$$H_\pm=(e_0\pm i e_1)/\sqrt2,$$

these are precisely the convex combinations in (4.1). Conversely every such combination has all six marginals equal to R, by linearity of partial trace. QED.

### Proposition 4.2. A three-body observable resolves the fiber

With epsilon_{xyz}=1 and Pauli operators in the fixed bases, define

$$K_{ABC}=\sum_{a,b,c\in\{x,y,z\}}\epsilon_{abc}\,\sigma_A^a\sigma_B^b\sigma_C^c\otimes I_D.$$

The exact identities are

$$K_{ABC}=2i(P_{AB}P_{BC}-P_{BC}P_{AB}),\qquad K_{ABC}^3=12K_{ABC},$$

$$K_{ABC}H_+=-2\sqrt3H_+,\qquad K_{ABC}H_-=2\sqrt3H_-.$$

Thus C_{ABC}=-K_{ABC}/(2sqrt(3)) has deterministic outcomes +1 and -1 on the two endpoints, and Tr(sigma C_{ABC})=2t-1 on the full fiber. All observable expectations supported on at most two qubits agree between the endpoints; this calibrated three-body observable distinguishes them perfectly.

The Pauli identity follows from P_{XY}=(I+sigma_X dot sigma_Y)/2 and [sigma_a,sigma_b]=2i epsilon_{abc}sigma_c. The cubic follows by setting V=P_{AB}P_{BC}, using V^3=I and V^dagger=V^2. On (e_0,e_1), K is [[0,2sqrt(3)i],[-2sqrt(3)i,0]], giving the displayed eigenvectors.

This is an expectation/tomography statement. It does not exclude sequential protocols whose complete recorded outcomes reveal three-body correlations, and it is not a quantum-error-correcting-code claim for the entire two-dimensional span. K is a calibrated observable, whereas chi in (3.2) is a local-basis invariant; they serve different roles.

## 5. Minimum Hamiltonian locality and a robust fidelity certificate

A k-local Hamiltonian here is a static Hermitian operator on exactly these four qubits, expressible as a sum of operators supported on at most k qubits. Ancillas, time-dependent gate synthesis and dissipative preparation are outside this definition.

### Theorem 5.1. Two-local impossibility and a gapped three-local construction

No two-local Hamiltonian can have H_+ or H_- as a nondegenerate ground state. Conversely,

$$\boxed{H^{(+)}=L+I_{16}+\frac{K_{ABC}}{2\sqrt3}} \tag{5.1}$$

has H_+ as its unique ground state, ground energy zero and spectral gap exactly 2 in the coefficient normalization shown. Changing the sign of K gives the analogous Hamiltonian H^{(-)} for H_-.

Proof of the lower bound on locality. The two orthogonal states have identical two-body marginals, hence the same energy expectation for every two-local Hamiltonian T. If H_+ has ground energy e, then T-eI>=0 and <H_-|(T-eI)|H_->=0. Positivity makes H_- another ground vector. The same argument holds with the endpoints reversed.

Proof of construction and gap. The operator L is nonnegative, and ||K||<=2sqrt(3) follows from its Hermitian cubic identity. Therefore I+K/(2sqrt(3))>=0. Let Pi_+,Pi_- be the two endpoint projectors and Q=I-Pi_+-Pi_-. Four spin-1/2 representations decompose as 0^{oplus 2} plus 1^{oplus 3} plus 2, which follows by applying (1/2) tensor (1/2)=0 plus 1 twice. Thus L>=2Q. Since the two endpoint eigenvectors of K are known and its remaining spectrum lies in [-2sqrt(3),2sqrt(3)],

$$I+K/(2\sqrt3)\ge2\Pi_-.$$

It follows that

$$\boxed{H^{(+)}\ge2(I-\Pi_+).} \tag{5.2}$$

H^{(+)}H_+=0 and H^{(+)}H_-=2H_-, so the lower bound is attained by an excited vector, proving uniqueness and the exact gap. Equation (5.1) contains only pair Heisenberg terms and one scalar-chirality term supported on ABC. Its maximum interaction order is three. QED.

Consequently every maximizer in Theorem 3.1 has minimum unique-ground-state Hamiltonian locality exactly three: product local conjugation transports the construction and preserves operator support sizes.

As an independent finite check, the full spectrum of (5.1), including multiplicities, is

$$0^{(1)},\quad2^{(4)},\quad3^{(3)},\quad4^{(3)},\quad7^{(5)}.$$

### Corollary 5.2. Energy-to-fidelity certificate

For any density matrix sigma, pure or mixed,

$$\boxed{\langle H_+|\sigma|H_+\rangle\ge1-\frac12\operatorname{Tr}(\sigma H^{(+)}).} \tag{5.3}$$

This follows by tracing (5.2) against sigma. It is a fidelity bound from specified two- and three-body observable expectations. It supplies no claim about hardware implementation, thermalization rates, sampling cost or uncalibrated-device certification.

## 6. A rigorous boundary for Renyi continuation

The von Neumann maximizing state does not remain the maximizing candidate throughout 1<alpha<2. Define

$$R_\alpha(\rho)=\frac{\log_2\operatorname{Tr}(\rho^\alpha)}{1-\alpha},\qquad \overline R_\alpha(\psi)=\frac13\sum_c R_\alpha(\rho_c).$$

For H_+,

$$r(\alpha)=\overline R_\alpha(H_+)=\frac{\log_2(2^{-\alpha}+3\,6^{-\alpha})}{1-\alpha}.$$

For the cluster state (|0000>+|0011>+|1100>-|1111>)/2, the three spectra are (1/2,1/2,0,0) and two copies of (1/4,1/4,1/4,1/4), so its average Renyi entropy is 5/3 at every positive order. This candidate and its cut entropies are established in [GW10].

### Proposition 6.1. A unique two-candidate crossing below order two

There is a unique alpha_0 in (3/2,5/3) at which r(alpha_0)=5/3. For every alpha>alpha_0 the cluster candidate strictly beats H_+ and H_-, including a nonempty interval inside (1,2).

Proof. A nonuniform probability vector has strictly decreasing Renyi entropy. Explicitly, with ell(alpha)=ln sum_j p_j^alpha, ell'' is the positive variance of ln p under the tilted distribution. Since ell(1)=0, strict convexity gives ell(alpha)<(alpha-1)ell'(alpha) for alpha>1; differentiating ell(alpha)/(1-alpha) proves strict decrease.

At alpha=3/2, the power sum is (sqrt(3)+1)/(2sqrt(6)). Its sixth power is (208+120sqrt(3))/13824<1/32, since sqrt(3)<28/15. Therefore r(3/2)>5/3. At alpha=5/3, the desired reverse comparison is

$$(1+3^{-2/3})^9>32.$$

It follows from the exact integer comparisons 9*12^3<25^3 and 37^9>32*25^9: they imply 3^{-2/3}>12/25 and then (1+3^{-2/3})^9>(37/25)^9>32. Hence r(5/3)<5/3. Continuity and strict decrease give a unique crossing. QED.

Its numerical value is approximately 1.58798688975; this decimal is a numerical locator, not an exact expression. This comparison does not identify the globally optimal state at intermediate orders. Another family may dominate one or both candidates. No complete Renyi phase diagram is claimed.

## 7. Source attribution, formal boundary and continuation targets

The mathematical dependencies are intentionally separate. The global moment inequalities come from the existing HS4 proof; one-uniform normal form comes from [GW10], Theorem 5; the scalar remainder estimate, phase-alignment classification, determinant separator, exact marginal-fiber argument and parent-Hamiltonian/fidelity argument are explicitly derived above. The two original conjugate candidates and their marginal spectrum are already in [HS00]. Theorem 10 of [GW10] is not used to collapse the two labelled-party branches. Its bare uniqueness wording cannot support that collapse because (3.2) separates the two explicitly.

[HS25] revisits the four-qubit AME obstruction using invariant, coding and state-polynomial methods, and [HW25] treats spectral compatibility through a symmetry-reduced hierarchy. These provide context for retaining joint-state compatibility rather than optimizing three unrelated spectra. Neither source is asserted to contain the new HS4 equality-set proof written here, and no exhaustive literature-priority claim is made for the marginal or Hamiltonian consequences.

The next formal targets are the deficit identity with strict equality conditions; the literal determinant covariance and conjugate values; the two-body marginal fiber and chirality operator; the operator inequality (5.2); and then the full equality classification. The last target additionally needs a formal one-uniform-to-Bell-product normal-form theorem. Existing finite eigenvalue checks do not supply that universal theorem. The current paper derivation uses the published normal-form theorem with its hypotheses, and its Lean implementation remains open.

Useful remaining mathematical questions are an explicit global distance bound to the **union** O_+ union O_- from Delta, and the genuine all-state Renyi optimizer diagram. Distance to a chosen one of the two orbits cannot be controlled by entropy deficit alone: a state in the other orbit already has deficit zero. The calibrated energy witness (5.3) avoids that ambiguity by specifying which branch is tested.

### References

- [HS00] A. Higuchi and A. Sudbery, *How entangled can two couples get?*, Physics Letters A 273 (2000), 213-217. [arXiv:quant-ph/0005013v2](https://arxiv.org/abs/quant-ph/0005013v2), Section 3. Correct DOI: [10.1016/S0375-9601(00)00480-1](https://doi.org/10.1016/S0375-9601(00)00480-1).
- [GW10] G. Gour and N. R. Wallach, *All Maximally Entangled Four Qubits States*, Journal of Mathematical Physics 51 (2010), 112201. [arXiv:1006.0036v2](https://arxiv.org/abs/1006.0036v2), Theorems 5 and 6, and Eqs. (3)-(5). DOI: [10.1063/1.3511477](https://doi.org/10.1063/1.3511477).
- [HS25] F. Huber and J. Siewert, *On two maximally entangled couples*, Quantum Science and Technology 11 (2026), 015025, published December 2025. [arXiv:2506.21282](https://arxiv.org/abs/2506.21282), DOI: [10.1088/2058-9565/ae23f4](https://doi.org/10.1088/2058-9565/ae23f4).
- [HW25] F. Huber and N. Wyderka, *Refuting spectral compatibility of quantum marginals*, Quantum 9 (2025), 1918. [Publisher article](https://quantum-journal.org/papers/q-2025-11-20-1918/), DOI: [10.22331/q-2025-11-20-1918](https://doi.org/10.22331/q-2025-11-20-1918).

## 8. Direct closure by one Schmidt cut, without the general normal-form theorem

This section provides an alternative proof of the equality classification in Section 3. It uses the inherited global HS4 inequality and the equality consequences of Section 2, but does not use [GW10], Theorem 5, Kempf-Ness theory, or a classification of general four-qubit states. The quantum-coordinate tools are the standard two-qubit spin-flip and magic-basis tools [HW97], with the precise identities derived here. All statements in this section remain ordinary mathematical proofs, not new Lean declarations.

Write lambda_*=(1/2,1/6,1/6,1/6). For a normalized state define the spin bilinear q(psi)=psi^T sigma_y^{tensor 4} psi, so tau_4=|q|^2. For every two by two matrix V, direct multiplication gives V^T sigma_y V=(det V)sigma_y. Consequently |q| is invariant under product local unitaries; its phase need not be invariant.

### Lemma 8.1. A distinguished Bell eigenvector

Suppose a two-qubit density matrix has spectrum lambda_* and both one-qubit marginals I_2/2. Let v be a unit eigenvector for its simple eigenvalue 1/2. Then

$$\rho=\frac16I_4+\frac13|v\rangle\langle v|,\qquad \operatorname{Tr}_B|v\rangle\langle v|=I_2/2.$$

Thus v is maximally entangled. This follows simply by taking a one-qubit partial trace of the displayed spectral decomposition. If B_v is its two by two amplitude matrix, B_v B_v^dagger=B_v^dagger B_v=I_2/2. Given any fixed Bell vector with matrix B_0, the one-qubit unitary V=2B_0 B_v^dagger satisfies V B_v=B_0. Hence the distinguished vector can be fixed using a genuine one-qubit operation, not an arbitrary two-qubit change of basis.

### Lemma 8.2. The exact one-plus-three block

Put s=(|01>-|10>)/sqrt(2), and use the following orthonormal basis separately on AB and CD:

$$q_0=i s,\qquad q_x=(\sigma_x\otimes I)s,\qquad q_y=(\sigma_y\otimes I)s,\qquad q_z=(\sigma_z\otimes I)s.$$

The Pauli convention is sigma_y=[[0,-i],[i,0]]. If Q has these four columns, direct evaluation gives

$$Q^\dagger Q=I_4,\qquad (\sigma_y\otimes\sigma_y)\overline Q=Q,\qquad Q^T(\sigma_y\otimes\sigma_y)Q=I_4. \tag{8.1}$$

Suppose a normalized four-qubit state has rho_X=I_2/2 for all four parties, spectrum(rho_AB)=lambda_*, and q(psi)=0. Purity of the global state gives the same spectrum for rho_CD. Apply Lemma 8.1 independently on AB and CD to make their distinguished eigenvectors q_0. Both marginals are then the fixed R from Section 4.

Write the resulting amplitude matrix as F=QZQ^T. The left reduced matrix is ZZ^dagger and the right one is Z^T conjugate(Z). Since both equal the real diagonal matrix D=diag(1/2,1/6,1/6,1/6), we also have Z^dagger Z=D. Associativity gives DZ=ZD. The distinct eigenvalue 1/2 therefore removes every cross entry between index zero and the other three indices:

$$Z=\begin{pmatrix}z&0\\0&T\end{pmatrix},\qquad |z|^2=1/2,\qquad TT^\dagger=T^\dagger T=I_3/6. \tag{8.2}$$

Choose the overall phase so z=i/sqrt(2). By (8.1), q(psi)=sum_{j,k}Z_{jk}^2. Its vanishing gives sum_{j,k}T_{jk}^2=1/2, while (8.2) gives sum_{j,k}|T_{jk}|^2=1/2. Taking the real part of their difference yields

$$2\sum_{j,k}(\operatorname{Im}T_{jk})^2=0.$$

Every entry of T is real. Consequently T=O/sqrt(6) for a real orthogonal matrix O in O(3).

### Lemma 8.3. Both orientations and no other orbit

For V in SU(2), the collective operation V tensor V fixes s and acts on (q_x,q_y,q_z) by the real rotation R_V determined by

$$V\sigma_jV^\dagger=\sum_k(R_V)_{kj}\sigma_k.$$

Every R in SO(3) occurs. For a direct construction, take its axis n and angle theta and set V=cos(theta/2)I-i sin(theta/2)n dot sigma. The Pauli product rule gives Rodrigues' formula. Equivalently, for real a,b,c,d with a^2+b^2+c^2+d^2=1 and V=aI-i(b sigma_x+c sigma_y+d sigma_z), its rotation matrix is

$$R_V=\begin{pmatrix}
a^2+b^2-c^2-d^2&2(bc-ad)&2(bd+ac)\\
2(bc+ad)&a^2-b^2+c^2-d^2&2(cd-ab)\\
2(bd-ac)&2(cd+ab)&a^2-b^2-c^2+d^2
\end{pmatrix}. \tag{8.3}$$

Before imposing the unit-quaternion equation, direct polynomial identities give R_V R_V^T=(a^2+b^2+c^2+d^2)^2 I and det R_V=(a^2+b^2+c^2+d^2)^3. Every real orthogonal three by three matrix with determinant one has a unit eigenvector of eigenvalue one; its orthogonal plane carries a planar rotation. This supplies the axis-angle representation, including the identity and angle pi cases.

Apply such a collective rotation only on AB. If det O=+1, take R_V=O^T; if det O=-1, take R_V=-O^T. The triplet block becomes respectively +I_3/sqrt(6) or -I_3/sqrt(6). An overall minus sign in the second case gives the representatives

$$\widetilde m_\pm=\frac{\pm i}{\sqrt2}q_0\otimes q_0+\frac1{\sqrt6}\sum_{j=x,y,z}q_j\otimes q_j.$$

In the fixed computational coordinates, direct substitution gives tilde m_+=-H_+ and tilde m_-=-H_-. The determinant invariant (3.2) distinguishes the two labelled-party LU orbits. Thus the orientation of the real triplet block is exactly the remaining discrete branch after allowable local rotations.

### Theorem 8.4. Complete equality characterization with a single spectral cut

For any normalized pure state, the following are equivalent:

1. F(psi)=F_*.
2. All three two-versus-two marginal spectra are lambda_*.
3. P=1 and spectrum(rho_AB)=lambda_*.
4. All four one-qubit marginals are I_2/2, q(psi)=0, and spectrum(rho_AB)=lambda_*.
5. psi belongs to O_+ union O_-.

Proof. Section 2 gives 1 iff 2. Condition 2 gives P=3(1/3)=1, hence 3. The nonnegative purity identity (2.5) proves 3 implies 4. Lemmas 8.1-8.3 prove 4 implies 5. The explicit spectra of the two HS representatives and local-unitary invariance give 5 implies 1. QED.

Condition 3 is a single-cut test within the minimum-total-purity locus; it does not permit omitting the common-state condition P=1. For example, the state with Z=diag(1/sqrt(2),I_3/sqrt(6)) has the indicated AB spectrum but q=1. Conversely the cluster state has P=1 and q=0 without the required spectrum. The construction also shows why the general four-qubit normal-form theorem is unnecessary for this equality set: the simple distinguished Schmidt value and spin-flip equality already force the needed special form.

## 9. An explicit all-state stability bound to the two-orbit union

Let

$$d(\psi,\mathcal M)=\min_{s\in\{+,-\},\,U\in U(2)^4,\,\theta\in\mathbb R}\|\psi-e^{i\theta}UH_s\|_2,\qquad \mathcal M=\mathcal O_+\cup\mathcal O_-.$$

The minimum exists by compactness. We prove a global Holder bound with explicit, nonoptimal constants. This is a pure-state, trusted-coordinate mathematical estimate. It is neither an optimal robustness exponent nor a device-independent self-test.

### Lemma 9.1. Improved scalar gap and spectral rounding

For 0<=x<=1, the scalar gap in Section 2 satisfies

$$g(x)\ge\frac1{54}\operatorname{dist}(x,\{1/6,1/2\})^2. \tag{9.1}$$

For x<=1/2, the Hermite remainder point is at most 1/2, so g(x)>=(2/3)(x-1/6)^2(x-1/2)^2. The more distant node is at least 1/6 away, proving (9.1). For x>=1/2, divide the remainder bound by (x-1/2)^2. Its coefficient is at least (x-1/6)^2/(12x^3), decreasing on [1/2,1] and bounded below by 25/432>1/54. The contact nodes and x=0 follow by continuity.

Define

$$\gamma=\sqrt{162\ln2},\qquad \mu=\sqrt{\frac{3\ln2}{-B}},\qquad \Delta_0=\frac1{5832\ln2}.$$

The deficit identity gives sum_{c,j} dist(lambda_{c,j},{1/6,1/2})^2<=gamma^2 Delta. If 0<=Delta<Delta_0, each spectrum rounds to exactly one copy of 1/2 and three copies of 1/6, and its Euclidean error is at most s=gamma sqrt(Delta). Indeed, if k entries round to 1/2, their rounded sum is (2+k)/3, differing from one by at most 2s<1/3; hence k=1. This also ensures the largest eigenvalue is simple. Complementary marginals have the same rounded spectrum.

### Lemma 9.2. Approximate Bell gauges and exact-marginal comparison state

Under the preceding small-deficit assumption set m=mu sqrt(Delta). Equation (2.6) gives ||rho_X-I_2/2||_F<=m for each party and |q(psi)|<=sqrt(2)m. Write the AB reduced state as

$$\rho_{AB}=\frac16I_4+\frac13|v\rangle\langle v|+D_v,\qquad \|D_v\|_F\le s,$$

where v is its top eigenvector. The Frobenius partial-trace inequality ||Tr_B D||_F<=sqrt(2)||D||_F gives a Bloch-vector bound for v:

$$|r_v|\le3\sqrt2\,m+6s=:r_0. \tag{9.2}$$

The same applies to the top eigenvector w of rho_CD. A two-qubit pure vector with Bloch length r has maximum overlap with a Bell vector equal to sqrt((1+sqrt(1-r^2))/2). Consequently its phase-adjusted vector distance to some Bell vector is at most r: use 2(1-sqrt((1+c)/2))<=1-c<=r^2 with c=sqrt(1-r^2).

Choose Bell approximations v_0,w_0 and product one-qubit unitaries taking them to q_0. These are the allowed physical local gauges. In these gauges the actual top eigenvectors remain within r_0 of q_0. A plane rotation W sending a unit vector v to q_0, after aligning their phases, satisfies ||W-I||_op<=||v-q_0||_2. Apply these two comparison rotations to the state; their total vector error is at most 2r_0. They may be two-qubit operations and are used only to construct a nearby comparison vector, not to assert an allowed local preparation.

Keep the resulting Schmidt vectors and replace their four Schmidt coefficients by sqrt(lambda_*). Since

$$\sum_j(\sqrt{\lambda_j}-\sqrt{\lambda_{*,j}})^2\le6\sum_j(\lambda_j-\lambda_{*,j})^2\le6s^2,$$

this adds at most sqrt(6)s to the vector error. We obtain a normalized comparison state phi whose AB and CD marginals are exactly R, with

$$\|U_{\rm loc}\psi-\phi\|_2\le e:=6\sqrt2\,m+(12+\sqrt6)s. \tag{9.3}$$

The spin bilinear is Lipschitz on the unit sphere: |q(u)-q(v)|<=2||u-v||_2, by expanding the difference and using ||sigma_y^{tensor 4}||_op=1. Therefore |q(phi)|<=sqrt(2)m+2e.

### Lemma 9.3. Rounding a complex unitary triplet block

For any normalized phi with its AB and CD marginals exactly R, Lemma 8.2 without the zero-spin assumption gives, after a global phase,

$$Z_\phi=\operatorname{diag}(i/\sqrt2,W/\sqrt6),\qquad W\in U(3),\qquad q(\phi)=-\frac12+\frac16\sum_{j,k}W_{jk}^2.$$

Write W=X+iY with X,Y real. Unitarity implies ||X||_F^2+||Y||_F^2=3, so

$$\|Y\|_F^2=-3\operatorname{Re}q(\phi)\le3|q(\phi)|.$$

All singular values t_j of X lie in [0,1]. A real orthogonal polar factor O exists even if X is singular, and

$$\|X-O\|_F^2=\sum_j(1-t_j)^2\le\sum_j(1-t_j^2)=\|Y\|_F^2.$$

It follows that ||W-O||_F^2<=6|q(phi)|. Replacing W by O creates a state eta in M by Lemma 8.3, and

$$\|\phi-\eta\|_2^2\le|q(\phi)|. \tag{9.4}$$

This estimate covers both orientations of O and every U(3) block. No nonsingularity of Re W is assumed.

### Theorem 9.4. Quantitative global rigidity

Define the exact constants

$$c=6\sqrt2\,\mu+(12+\sqrt6)\gamma,\qquad k=\sqrt2\,\mu+2c.$$

For 0<=Delta<Delta_0,

$$\boxed{d(\psi,\mathcal M)\le\min\{\sqrt2,\ c\sqrt\Delta+\sqrt{k}\,\Delta^{1/4}\}.} \tag{9.5}$$

Indeed Lemma 9.2 gives e=c sqrt(Delta), Lemma 9.3 gives distance at most sqrt(sqrt(2)m+2e), and the triangle inequality proves (9.5). The cap sqrt(2) is the universal distance between unit rays after phase minimization.

For every normalized pure state, without a small-deficit hypothesis,

$$\boxed{d(\psi,\mathcal M)\le K\Delta^{1/4},\qquad K=\max\left\{\sqrt2\Delta_0^{-1/4},\ c\Delta_0^{1/4}+\sqrt{k}\right\}.} \tag{9.6}$$

For Delta<Delta_0, absorb sqrt(Delta)<=Delta_0^{1/4}Delta^{1/4} in (9.5); for Delta>=Delta_0, use the universal cap. Numerically gamma=10.5966902..., mu=1.65367464..., c=167.148661..., k=336.635971..., and K=39.3100978... . The displayed formulas, not these decimal locators, define the constants. They are conservative and not optimized.

With fidelity defined as the squared overlap with a pure reference, the same argument yields

$$\max_{s,U}|\langle UH_s|\psi\rangle|^2\ge\max\{0,1-K^2\sqrt\Delta\}. \tag{9.7}$$

This follows from 1-|<u|v>|^2<=min_theta ||u-e^{i theta}v||_2^2. Equations (9.5)-(9.7) control the full pure state up to local unitaries and the unavoidable conjugate branch. They strengthen the earlier estimates on marginal spectra alone, but do not choose a branch from entropy alone.

## 10. Mathematical closure and remaining formal obligations

Together, the inherited HS4 bound, Theorem 8.4 and Theorem 9.4 provide the exact global maximum, all equality states, and an explicit stability estimate for the original pure-state von Neumann objective. The argument in Section 8 bypasses the external general normal-form input used in Section 3 and therefore removes that dependency from this route. Section 9 supplies the explicit global distance bound posed in Section 7. The inherited degree-six certificate is not reproved here; it remains an explicit dependency of the maximum and deficit arguments.

The remaining formalization route consists of finite-dimensional partial traces and spectral decompositions; the elementary distinguished-Bell gauge; the block-commutation and spin-flip identities (8.1)-(8.2); the explicit quaternion rotation lift (8.3); and the determinant separator. A general Kempf-Ness or four-qubit normal-form theorem is no longer required for this route. These are uncompleted Lean obligations in this delivery. There is no claim of a new kernel-checked equality classification or stability theorem, no full replay of the inherited certificate, and no independent-review or historical-priority claim.

The companion experiment entry is `docs/reports/hs4-rigidity/verify_schmidt_closure.py` in the existing experiments PR #11. It checks fixed and symbolic coordinate identities, samples both orthogonal components with product local rotations, exercises arbitrary unitary triplet rounding, and tests the small-deficit construction on perturbed HS states. Finite tests do not certify the universal statements above. The globally optimal Renyi diagram, an optimal robustness exponent, and stronger numerical constants remain outside the present result.

Additional source: [HW97] S. Hill and W. K. Wootters, *Entanglement of a Pair of Quantum Bits*, Physical Review Letters 78 (1997), 5022-5025. [arXiv:quant-ph/9703041v2](https://arxiv.org/abs/quant-ph/9703041v2), DOI [10.1103/PhysRevLett.78.5022](https://doi.org/10.1103/PhysRevLett.78.5022). This is background attribution for two-qubit magic-basis methods. The precise basis, transformation laws, HS4 classification and error estimates used here are derived explicitly above.

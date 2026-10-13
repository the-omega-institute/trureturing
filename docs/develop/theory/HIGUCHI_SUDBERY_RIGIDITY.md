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

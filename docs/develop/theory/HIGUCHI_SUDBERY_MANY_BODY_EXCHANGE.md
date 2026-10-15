# HS4 cells: many-body exchange, cubic chirality and finite spectral certification

## 1. Scope, established inputs and algorithm distinction

This chapter continues [HS4 rigidity](HIGUCHI_SUDBERY_RIGIDITY.md) and [AURIC network and spatial completion](HIGUCHI_SUDBERY_AURIC_NETWORK_CLOSURE.md). It supplies ordinary mathematical proofs for a declared microscopic exchange Hamiltonian. The inherited global entropy certificate is unchanged. These new results have not been formalized in Lean or independently reviewed; historical priority of the derived formulas is not asserted.

The four-spin singlet doublet, its exchange/chirality representation and perturbative coupling of tetrahedra are established condensed-matter constructions. Tsunetsugu [T01] studies a particular pyrochlore coupling geometry. Wang [W10], Sections II, IV.B and Appendix B, gives the same singlet carrier, several second-order couplings and an encoded Kitaev construction. His exact construction permits higher-body interactions; his perturbative chirality-axis construction also permits microscopic spin-chirality terms. Those results are not reissued as new discoveries. Here every inter-cell term is a real isotropic two-spin exchange, the coupling matrix is arbitrary, and an explicit cubic coefficient and finite-system remainder are derived.

Three algorithms must be distinguished. The Schur transform [BCH06] exposes total-spin sectors and their multiplicities. Schrieffer-Wolff perturbation theory [BDL11] eliminates virtual higher-spin sectors. Shor's algorithm [Shor97] concerns factoring and discrete logarithms; only the finite Fourier/phase-estimation mechanism is used in Section 8. The spelling `sohr` does not specify a separate algorithm here. No factoring computation, quantum hardware execution or generic many-body speedup is claimed.

All spin operators are dimensionless, J_i^alpha=sigma_i^alpha/2. The energy scale Delta below is the single-cell triplet gap, not an entropy deficit. Face labels i=0,1,2,3 are fixed, and a,b,c denote distinct cells.

## 2. Microscopic Hamiltonian and exact sector selection

For one cell let L=(sum_i J_i)^2 and let E:C^2 -> (C^2)^{tensor 4} be the real isometry with columns

$$e_0=\frac{|0011\rangle+|1100\rangle-(|0101\rangle+|0110\rangle+|1001\rangle+|1010\rangle)/2}{\sqrt3},$$
$$e_1=\frac{|0101\rangle-|0110\rangle-|1001\rangle+|1010\rangle}{2}.$$

Its range is C=ker L. The total-spin decomposition is

$$(\mathbb C^2)^{\otimes4}=(V_0\otimes\mathbb C^2)\oplus(V_1\otimes\mathbb C^3)\oplus V_2.$$

Thus L has eigenvalues 0,2,6 with multiplicities 2,9,5. The logical Pauli matrices X,Y,Z act on the multiplicity space at total spin zero. The HS endpoints are H_+=(e_0+i e_1)/sqrt(2) and H_-=(e_0-i e_1)/sqrt(2); they have logical Y eigenvalues +1 and -1.

For two cells define

$$H_0=\frac\Delta2(L_a+L_b),\quad \Delta>0,\qquad K=E\otimes E,\quad P=KK^\dagger,\quad Q=I-P,$$
$$V(T)=\sum_{i,j=0}^3t_{ij}\,\mathbf J_{ai}\cdot\mathbf J_{bj},\qquad T\in\mathbb R^{4\times4},\qquad H=H_0+V(T). \tag{2.1}$$

Entries of T have units of energy. V is Hermitian even when T is not symmetric, since its two factors are on different cells. Define the logical two-spin moments

$$A_{ii}=\frac34I_2,\qquad A_{ik}=E^\dagger(\mathbf J_i\cdot\mathbf J_k)E=\frac{2\widehat S_{ik}-I_2}{4}\quad(i\ne k),$$

where S is physical spin swap and a hat means compression by E. The exact matrices inherited from the preceding chapter are

$$\widehat S_{01}=\widehat S_{23}=Z,\quad \widehat S_{02}=\widehat S_{13}=-\frac Z2-\frac{\sqrt3X}{2},\quad \widehat S_{03}=\widehat S_{12}=-\frac Z2+\frac{\sqrt3X}{2}. \tag{2.2}$$

### Lemma 2.1. A fixed virtual denominator

For every T,

$$PVP=0,\qquad H_0VK=2\Delta VK,\qquad E^\dagger J_i^\alpha J_k^\beta E=\frac{\delta_{\alpha\beta}}3A_{ik}. \tag{2.3}$$

Proof. A vector operator applied to a spin-zero state transforms in the spin-one representation: commuting the total angular momentum through J_i^alpha gives the vector representation, whose Casimir is 2. It has no spin-zero component, so E^dagger J_i^alpha E=0. A cross-cell exchange creates spin one on both cells and hence energy 2Delta. The compressed second tensor is invariant under simultaneous rotations; its unique invariant rank-two Cartesian tensor is delta, and summing alpha=beta gives A_ik. These statements can equivalently be checked as the finite identities L J_i^alpha E=2J_i^alpha E and (2.3); the supplied checker verifies all indices. QED.

In the fixed code coordinates, the second and third homogeneous effective coefficients are

$$H_{[2]}=-\frac1{2\Delta}K^\dagger V^2K,\qquad H_{[3]}=\frac1{4\Delta^2}K^\dagger V^3K. \tag{2.4}$$

These follow either from the usual degenerate SW expansion with PVP=0 or from the exact Schur complement in Section 5. The two resolvents next to VK both act as 1/(2Delta). Equation (2.4) specifies Taylor coefficients, not an exact all-order replacement of H. Their values refer to this fixed effective-coordinate convention.

## 3. Second-order coupling and the boundary contrast space

Let

$$B=\frac12\begin{pmatrix}1&1&1\\1&-1&-1\\-1&1&-1\\-1&-1&1\end{pmatrix},\qquad C_4=BB^T=I_4-\frac14\mathbf1\mathbf1^T,\qquad B^TB=I_3,$$
$$\widetilde T=B^TTB. \tag{3.1}$$

B gives an orthonormal basis of the zero-sum face-label space. It is unrelated to a claim about the dimension of physical space.

### Proposition 3.1. Full second-order formula and exact inactive couplings

$$\boxed{H_{[2]}=-\frac1{6\Delta}\sum_{i,j,k,l}t_{ij}t_{kl}\,A_{ik}\otimes A_{jl}.} \tag{3.2}$$

It belongs to span{I,X,Z} tensor span{I,X,Z}, so its Y tensor Y coefficient vanishes. Moreover,

$$\frac14\operatorname{Tr}(K^\dagger V^2K)=\frac13\|\widetilde T\|_F^2,\qquad -\frac14\operatorname{Tr}H_{[2]}=\frac{\|\widetilde T\|_F^2}{6\Delta}. \tag{3.3}$$

Consequently VK=0 if and only if tilde T=0. In that case H annihilates the code exactly, not merely through a fixed perturbative order.

Proof. Substitute (2.3) into the expansion of V^2; the two Cartesian deltas sum to 3, giving (3.2). The matrices (2.2) imply Tr(A_ik)/2=(C_4)_ik, including diagonal indices. Taking the normalized trace of K^dagger V^2K therefore gives Tr(T^T C_4 T C_4)/3=||B^T T B||_F^2/3. Since K^dagger V^2K=(VK)^dagger VK is positive, zero trace is equivalent to VK=0. H_0K=0 then proves the exact assertion. QED.

For example any T=1 r^T+s 1^T has zero contrast. Such interactions involve a total cell spin and annihilate the singlet code. A single physical exchange link has a nonzero contrast but rank at most one: it can produce a common energy shift without the cubic oriented term below. Absence of an explicit YY coefficient at second order does not imply absence of YY correlations in a second-order eigenstate.

## 4. A determinant law for the cubic chirality interaction

For a logical two-qubit operator M write c_YY(M)=Tr[(Y tensor Y)M]/4.

### Theorem 4.1. Arbitrary real coupling matrices

For every real T,

$$\boxed{c_{YY}(H_{[3]})=\frac3{16\Delta^2}\det(B^TTB).} \tag{4.1}$$

Thus a nonzero cubic chirality coefficient requires and is guaranteed by three linearly independent zero-sum coupling directions. A singular contrast kills this coefficient; it does not exclude other couplings, higher-order effects or dynamical chirality readout.

Proof. Put h_ikm=epsilon_ikml for distinct i,k,m and the remaining label l, with epsilon_0123=1, and put h_ikm=0 when an index repeats. The coefficient of Y in every ordered local triple word is

$$\frac12\operatorname{Tr}\left[Y E^\dagger J_i^\alpha J_k^\beta J_m^\gamma E\right]=-\frac{\sqrt3}{24}h_{ikm}\epsilon_{\alpha\beta\gamma}. \tag{4.2}$$

For distinct sites, rotational invariance makes the Cartesian tensor proportional to epsilon. Contracting it fixes the coefficient from the already explicit scalar chirality E^dagger J_0 dot(J_1 cross J_2)E=-sqrt(3)Y/4. Closure of the total spin supplies the missing-index signs. If a label repeats, use J^alpha J^beta=delta_ab I/4+(i/2)sum_gamma epsilon_abgamma J^gamma; commuting operators on different sites reduces the word to one- and two-spin compressions, all with zero Y coefficient. This also covers nonconsecutive repeated labels.

Use (4.2) on both cells in V^3 and sum the Cartesian indices, for which sum epsilon_abgamma^2=6. Group the distinct face triples by their missing rows and columns. Expanding the three-by-three determinants gives

$$c_{YY}(K^\dagger V^3K)=\frac3{16}\sum_{l,m=0}^3(-1)^{l+m}\det T_{\widehat l,\widehat m}. \tag{4.3}$$

Cauchy-Binet applied to B^TTB gives

$$\sum_{l,m}(-1)^{l+m}\det T_{\widehat l,\widehat m}=4\det(B^TTB). \tag{4.4}$$

For clarity, the signed maximal minors of the displayed B all have modulus 1/2; multiplying the row and column minors gives precisely the coefficient (-1)^{l+m}/4. Equations (4.3)-(4.4) and (2.4) prove (4.1). This is an all-variable polynomial identity, not interpolation from a list of coupling matrices. QED.

### Corollary 4.2. Sharp strength bound and symmetry boundary

$$|c_{YY}(H_{[3]})|\le\frac3{16\Delta^2}\left(\frac{\|\widetilde T\|_F^2}{3}\right)^{3/2}. \tag{4.5}$$

For nonzero contrast equality holds exactly when its three singular values are equal. Indeed the absolute determinant is their product, and AM-GM applied to their squares proves (4.5). T=gI_4 attains it; an odd permutation of matched face labels reverses the determinant sign. These statements fix the labelled local orientation conventions.

The physical H_0 and V are real matrices, as are E and the effective coefficients in (2.4). Therefore a Pauli term with an odd number of logical Y factors has zero coefficient. YY is allowed by this symmetry and can correlate orientations without choosing an individual handedness. Time-reversal-breaking one-cell chirality fields are not generated by this real Hamiltonian alone. The determinant controls only the stated cubic YY coefficient; it is not a complete formula for H_[3] or a proof of chiral long-range order.

## 5. Finite-system error bound from an exact Schur complement

This section certifies the two-cell truncation against the full 256-dimensional Hamiltonian. It does not use a thermodynamic-limit estimate. Let nu=||V||_op and suppose nu<=Delta/4. Set A_0=QH_0Q, A=A_0+QVQ and W=QVK, treating A_0 and A as operators on ran Q. Then A_0>=Delta I, A>= (Delta-nu)I and A_0^{-1}W=W/(2Delta).

### Theorem 5.1. A fourth-order spectral error with an explicit constant

Let E_1<=...<=E_4 be the four lowest eigenvalues of H, and let mu_1<=...<=mu_4 be the eigenvalues of H_[2]+H_[3]. Then

$$E_i\le0,\quad E_5(H)\ge\Delta-\nu>0,\qquad \boxed{|E_i-\mu_i|\le\frac{\nu^4}{\Delta^3}\quad(1\le i\le4).} \tag{5.1}$$

Proof. The four-dimensional trial space has identically zero quadratic form P H P, so the first four eigenvalues are nonpositive. Weyl's bound gives the assertion for the fifth. At any E<=0, solving the Q part of the eigenvector equation yields the exact four-by-four operator

$$F(E)=-W^\dagger(A-EI)^{-1}W,\qquad F(E)p=Ep. \tag{5.2}$$

The code component p cannot vanish for a nonpositive eigenvector because A>0. Equation (5.2) bounds |E|<=nu^2/(Delta-nu). For D=QVQ-EI, the exact resolvent expansion with its untruncated remainder is

$$(A_0+D)^{-1}=R_0-R_0DR_0+R_0D(A_0+D)^{-1}DR_0,\qquad R_0=A_0^{-1}.$$

Substitution in (5.2), using R_0W=W/(2Delta), gives

$$\|F(E)-(H_{[2]}+H_{[3]})\|\le\frac{\nu^2}{4\Delta^2}\left[|E|+\frac{(\nu+|E|)^2}{\Delta-\nu}\right]. \tag{5.3}$$

Put x=nu/Delta<=1/4 and use the preceding bound on E. The right side is at most

$$\frac{\nu^4}{4\Delta^3}\left[\frac1{1-x}+\frac1{(1-x)^3}\right]\le\frac{25}{27}\frac{\nu^4}{\Delta^3}\le\frac{\nu^4}{\Delta^3}.$$

For ordered eigenvalues f_i(E) of F(E), the derivative F'(E)=-W^dagger(A-EI)^{-2}W is nonpositive, so each f_i is nonincreasing. Hence f_i(E)-E is strictly decreasing, tends to a positive value as E tends to minus infinity, and is nonpositive at E=0. Each has one root, and the root order agrees with i. These four roots, counted with multiplicity, are precisely the four nonpositive eigenvalues of H. Weyl's bound applied to F(E_i) and H_[2]+H_[3] proves (5.1). The case nu=0 is immediate. QED.

For a large graph the total ||V|| can grow with size. Equation (5.1) is not a uniform-volume many-body error theorem. Linked-cluster SW estimates [BDL11] supply the appropriate established framework for that different task, whose locality hypotheses and constants have not been checked here.

## 6. A microscopic eight-spin entangling ground state

Choose four matched links T=gI_4, g>0. All interactions in H are then ordinary two-spin antiferromagnetic Heisenberg exchanges, up to the constant in H_0. Since the four cross-cell links are disjoint, ||V||=3g exactly.

### Proposition 6.1. Explicit effective coefficients

$$H_{[2]}=-\frac{g^2}{2\Delta}I-\frac{g^2}{4\Delta}(X_aX_b+Z_aZ_b),$$
$$H_{[3]}=-\frac{3g^3}{16\Delta^2}(I+X_aX_b+Z_aZ_b-Y_aY_b). \tag{6.1}$$

Proof. In (3.2) set t_ij=g delta_ij and use the six matrices (2.2); this gives the first equality. For the second expand the four matched links in V^3 and use the local Pauli products and (4.2). Equivalently the finite exact identity is K^dagger V(I)^3K=-(3/4)(I+XX+ZZ-YY), which is verified entrywise from the displayed E and swap matrices. No fitted coefficients are used. QED.

The lowest eigenvector of the truncation is the logical Bell vector

$$|\Phi\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},\qquad K|\Phi\rangle=\frac{H_+\otimes H_-+H_-\otimes H_+}{\sqrt2}. \tag{6.2}$$

Its four eigenvalues, with multiplicities, are

$$-\frac{g^2}{\Delta}-\frac{3g^3}{4\Delta^2},\quad \left(-\frac{g^2}{2\Delta}\right)^{(2)},\quad0.$$

At second order alone the Bell vector already has <Y_aY_b>=-1; the cubic term supplies an additional explicit YY interaction. This distinguishes correlations in a state from a coefficient of its Hamiltonian.

### Theorem 6.2. Unique entangled ground state of the full Hamiltonian

At g=Delta/100 the full 256-dimensional H has a unique ground state Psi_0 and

$$\boxed{\operatorname{gap}(H)\ge\frac{4913}{100000000}\Delta>0,\qquad |\langle K\Phi|\Psi_0\rangle|^2\ge\frac{9409}{9418}.} \tag{6.3}$$

In particular the actual microscopic ground state is entangled across the two four-spin cells.

Proof. Theorem 5.1 applies with nu=3g. The low-band gap is at least g^2/(2Delta)+3g^3/(4Delta^2)-162g^4/Delta^3, which gives the first rational number in (6.3). The higher band is above Delta-3g and cannot close this gap.

To identify the projected eigenvector, H is invariant under simultaneously applying any permutation of the four face labels to both cells. On the code the common fixed space of the paired swaps is exactly the line Phi. To check the dimension explicitly, invariance under Z tensor Z restricts to a|00>+b|11>, and the paired swap with matrix -Z/2-sqrt(3)X/2 forces a=b. All paired real orthogonal swap matrices fix Phi. The exact F(E) commutes with these swaps, so it preserves that line and its orthogonal complement. Its distance from the truncation is bounded by (5.3). The positive truncated separation minus twice that error forces the lowest eigenvector of F(E_1) to be Phi. Thus P Psi_0 is proportional to K Phi.

The Q component equals -(A-E_1 I)^{-1}W p, so its norm is at most [3g/(Delta-3g)]||p||. Normalization gives the squared code overlap at least 1/[1+(3g/(Delta-3g))^2]=9409/9418. A product state across the two cells has squared overlap with K Phi at most 1/2, because its two nonzero Schmidt coefficients are 1/sqrt(2); convexity extends this to every separable mixed state. The larger fidelity proves entanglement. QED.

The code Bell state has one ebit between cells and maximally mixed one-cell logical marginals, with the HS internal pair data. The full microscopic ground state has small higher-spin leakage and is not asserted to have those internal marginals exactly. Nor is it a product of two pure HS states. This is consistent with the local-purity budget in the preceding chapter. The lower bound concerns a specified finite Hamiltonian; no material realization, phase transition or spontaneous time-reversal breaking follows.

## 7. A finite graph: the triangle correction to independent-edge dynamics

Consider any finite simple graph of cells, with

$$H_0=\frac\Delta2\sum_aL_a,\qquad V=\sum_{ab\in E(G)}g_{ab}\sum_{i=0}^3\mathbf J_{ai}\cdot\mathbf J_{bi}.$$

Every edge uses the same matched labels. Project to the product of the singlet spaces. The first-order coefficient vanishes, and the second-order coefficient is the sum of (6.1)'s second-order edge terms.

### Theorem 7.1. Complete cubic linked terms in the matched-label model

The third-order coefficient is the sum of the edge terms from (6.1), plus one term for each unordered graph triangle {a,b,c}:

$$\frac{g_{ab}g_{bc}g_{ca}}{\Delta^2}\,\mathcal T_{abc},$$
$$\boxed{\mathcal T_{abc}=\frac12I+\frac14\sum_{uv\subset\{a,b,c\}}(X_uX_v+Z_uZ_v)+\frac18(Z_aZ_bZ_c-X_aX_bZ_c-X_aZ_bX_c-Z_aX_bX_c).} \tag{7.1}$$

Proof. Each rightmost exchange creates two triplets with total energy 2Delta, and the leftmost exchange annihilates precisely such a sector. Therefore the outer resolvents again give 1/(4Delta^2). In a projected ordered product of two or three edges, any cell incident exactly once contributes P_a J_ai P_a=0. With three edges, the only surviving incidence multigraphs are three repetitions of one edge, or a triangle. Disconnected patterns and paths contain such a singly touched cell.

For a triangle, each cell is touched twice. The three local second moments give a Cartesian contraction 3/27=1/9. All six orders of the three different edges give the same result because the compressed second moment is symmetric. The triangle contribution is therefore

$$\mathcal T_{abc}=\frac16\sum_{i,j,k=0}^3A_{ik}^{(a)}\otimes A_{ij}^{(b)}\otimes A_{jk}^{(c)}. \tag{7.2}$$

Substituting (2.2) in this finite 64-term sum gives (7.1). The companion checker verifies the complete exact 8-by-8 identity, and separately checks the microscopic cubic compression for two weighted three-cell cycles. QED.

A forest has no triangle correction. On a uniform chain, after dropping constants, the cubic truncation is

$$-J_\perp\sum_a(X_aX_{a+1}+Z_aZ_{a+1})+J_\chi\sum_aY_aY_{a+1},$$
$$J_\perp=\frac{g^2}{4\Delta}+\frac{3g^3}{16\Delta^2},\qquad J_\chi=\frac{3g^3}{16\Delta^2}. \tag{7.3}$$

A logical-axis rotation and a staggered transverse sign change turn (7.3) into an XXZ chain with anisotropy 3g/(4Delta+3g). This is an algebraic identification of the truncation and a concrete target for symmetry-resolved tensor-network calculations. No DMRG calculation or infinite-chain phase theorem has been performed here. Higher-order terms and size-uniform error bounds must be controlled before transferring any exact XXZ phase conclusion to the microscopic model.

The three independent face-contrast directions in (4.1) and a graph triangle in (7.1) are different structures. The former controls a two-cell chirality coefficient; the latter adds genuine three-cell terms. Neither is an independent-source triangle preparation assumption. In particular replacing network dynamics by independently derived pair terms misses (7.1).

## 8. Exact character readout: what Schur and Fourier methods actually add

Schur decomposition must retain the two-dimensional multiplicity at total spin zero. Measuring only total spin returns zero on both H_+ and H_- and loses their distinction. On N cells the retained code has dimension 2^N, versus 16^N for the complete spin space; it is still exponentially large and its ground state is not solved by a basis transform alone.

The code restriction can be implemented as a legitimate channel with a leakage flag,

$$\mathcal R(\rho)=E^\dagger\rho E\ \oplus\ \operatorname{Tr}[(I-EE^\dagger)\rho]|\mathrm{fail}\rangle\langle\mathrm{fail}|. \tag{8.1}$$

Kraus operators E^dagger and |fail><q_j| for an orthonormal basis of the complement prove complete positivity and trace preservation. The output includes the flag; dropping it and normalizing is a separate postselection operation. This retains the full logical orientation, unlike the non-CP shape-only decoder identified in the preceding chapter.

For a single cell, let C_3=S_01 S_12. Direct multiplication gives

$$C_3^3=I,\qquad \widehat C_3=-\frac12I+\frac{i\sqrt3}{2}Y.$$

With omega=exp(2pi i/3), its eigenvalues on H_+ and H_- are omega and omega^2. The finite Fourier projectors are

$$\Pi_k=\frac13\sum_{l=0}^2\omega^{-kl}C_3^l,\qquad E^\dagger\Pi_0E=0,\quad E^\dagger\Pi_1E=\frac{I+Y}{2},\quad E^\dagger\Pi_2E=\frac{I-Y}{2}. \tag{8.2}$$

Preparing a qutrit ancilla in (|0>+|1>+|2>)/sqrt(3), applying controlled C_3^l and inverse Fourier transform F_3^dagger, then measuring the ancilla implements these projectors. The character sum annihilates every mismatched eigenphase. On sigma_r the output probabilities are (0,(1+r)/2,(1-r)/2), so the two exact HS endpoints are perfectly distinguished.

This is a fully specified order-three phase readout, using an ancilla, controlled permutations and phase-sensitive Fourier gates. It is not the factoring task of [Shor97], a restricted real-Kraus protocol, or an experimentally executed circuit. Its physical gate cost and accuracy have not been established. Equations (8.1)-(8.2) are exact mathematical constructions.

## 9. Consequence for AURIC and the spatial theory

The preceding spatial chapter supplied local singlet cells and their observation fibers without a microscopic inter-cell coupling. Here the exchange Hamiltonian supplies that missing input. Virtual excitation generates logical interactions; their third-order orientation coefficient depends on the oriented determinant of the face-contrast coupling, while actual graph loops generate additional linked terms. The full-system estimate verifies a finite entangled ground state beyond the projected approximation.

This preserves three separations required by the AURIC theory. A visible observation quotient is not automatically a physical channel: (8.1) keeps the missing multiplicity and a failure record. A local pair model is not a complete network dynamics: (7.1) supplies its triangle correction. An occupation constraint is not implied by a similar drawing: the no11 Fibonacci space and its legal pulse menu have not been derived from (2.1) or (7.3). A map to that constrained space would require an additional explicitly supplied blockade, bias and preparation/control proof.

The original unrestricted HS entropy maximum is not reproved by this perturbative construction. The main new derivations here are (4.1), the sharp contrast bound, the finite spectral certificate (5.1), the concrete microscopic ground-state bounds (6.3), and the graph-dependent cubic term (7.1). General exchange-only control, Schur transforms, SW theory, Fourier orthogonality and tetrahedral singlet carriers retain their established attribution.

## 10. Verification and remaining boundaries

The companion program is `docs/reports/hs4-rigidity/verify_manybody_exchange.py` in experiments PR #11. Its exact checks include every ordered local three-spin word, all-variable cofactor contraction, nine physical coupling matrices, the matched coefficients, paired-permutation invariance, character projectors and the triangle identity. Separate numerical checks compare the complete 256-dimensional low spectrum with the stated bound, evaluate on-shell Schur complements, and test three-cell path and cycle compressions. Their counts describe assertions, not the number of scalar entries or a proof by sampling. Universal claims rely on the arguments above.

No new Lean compilation, inherited HS certificate replay, canonical admission run, independent mathematical review, quantum hardware experiment or historical-first claim is made. The finite norm bound is not uniform in graph size; no many-body thermodynamic phase, actual geometric face-matching equation, gravity, or quantum factoring advantage is established. These boundaries also apply when interpreting the singlet cells as quantum tetrahedra.

### References and precise roles

- [T01] H. Tsunetsugu, *Antiferromagnetic Quantum Spins on the Pyrochlore Lattice*, Physical Review B 65, 024415. [arXiv:cond-mat/0103231](https://arxiv.org/abs/cond-mat/0103231). Existing chiral singlet doublets and coupling-geometry-dependent perturbation theory; its pyrochlore bond arrangement is not the arbitrary two-cell T used here.
- [W10] F. Wang, *Realization of the Exactly Solvable Kitaev Honeycomb Lattice Model in a Spin Rotation Invariant System*, Physical Review B 81, 184416 (2010). [arXiv:1001.0266v2](https://arxiv.org/abs/1001.0266v2), [DOI:10.1103/PhysRevB.81.184416](https://doi.org/10.1103/PhysRevB.81.184416). Sections II, IV.B and Appendix B establish the prior singlet, exchange and perturbative setting; the chirality-axis microscopic perturbation there is not restricted to bilinear exchanges.
- [BDL11] S. Bravyi, D. P. DiVincenzo and D. Loss, *Schrieffer-Wolff transformation for quantum many-body systems*, Annals of Physics 326 (2011), 2793-2826. [arXiv:1105.0675](https://arxiv.org/abs/1105.0675), [DOI:10.1016/j.aop.2011.06.004](https://doi.org/10.1016/j.aop.2011.06.004). General effective-Hamiltonian and linked-cluster theory; the explicit finite bound in Section 5 is proved directly here.
- [BCH06] D. Bacon, I. L. Chuang and A. W. Harrow, *Efficient Quantum Circuits for Schur and Clebsch-Gordan Transforms*, Physical Review Letters 97 (2006), 170502. [arXiv:quant-ph/0407082](https://arxiv.org/abs/quant-ph/0407082), [DOI:10.1103/PhysRevLett.97.170502](https://doi.org/10.1103/PhysRevLett.97.170502). Symmetry-resolved basis transformation, not a generic ground-state algorithm.
- [Shor97] P. W. Shor, *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer*, SIAM Journal on Computing 26 (1997), 1484-1509. [arXiv:quant-ph/9508027](https://arxiv.org/abs/quant-ph/9508027). The factoring task is separate from the elementary three-character phase readout in (8.2).

## 11. Nonperturbative positivity: a unique ground state at every positive matched coupling

Sections 11-16 concern the same microscopic two-cell Hamiltonian as Section 6, now for every Delta>0 and g>0 without a small-coupling assumption. They give ordinary mathematical proofs, not new Lean declarations. The matrix-positivity mechanism is established spin-reflection-positivity methodology [LS00]. Its finite specialization is proved here, including the full-rank and uniqueness steps needed below. This is not an originality claim for reflection positivity or for the existence of singlet ground states in reflected magnets.

Put h=Delta L/2 and R=Y^{tensor 4}; in computational coordinates R is real, symmetric and unitary. For a 16 by 16 coefficient matrix C define the linear isometry

$$\mathcal V(C)=\sum_{\mu,\nu} C_{\mu\nu}|\mu\rangle_a\otimes R|\nu\rangle_b,\qquad \|\mathcal V(C)\|^2=\operatorname{Tr}C^\dagger C.$$

The antiunitary time reversal on one cell is Theta=R times coordinate conjugation. The matrix identities R(J_i^alpha)^T R=-J_i^alpha and Rh^T R=h give

$$H\mathcal V(C)=\mathcal V(\mathscr H(C)),\qquad
\mathscr H(C)=hC+Ch-g\sum_{i,\alpha}J_i^\alpha C J_i^\alpha. \tag{11.1}$$

This is a representation of the full 256-dimensional operator, with no projection or omitted sector. The superoperator is complex-linear, Hilbert-Schmidt selfadjoint and preserves Hermitian matrices.

### Theorem 11.1. Strict matrix positivity and uniqueness

For every Delta>0 and g>0, H has a unique ground ray. Its normalized coefficient matrix in (11.1) can be chosen strictly positive definite. Consequently its Schmidt rank across the two four-spin cells is 16. These assertions also hold for four unequal matched couplings g_i>0, replacing g in each site's three terms by g_i. No claim of the subsequent three-dimensional reduction or monotonicity is made for unequal links.

Proof. A lowest-eigenvalue eigenmatrix has a nonzero Hermitian real or imaginary part, since the superoperator preserves adjoints. Choose a Hermitian ground matrix C with eigenvalues c_m and Hilbert-Schmidt norm one. In its eigenbasis,

$$\langle C,\mathscr H(C)\rangle=2\operatorname{Tr}(hC^2)-g\sum_{i,\alpha,m,n}c_mc_n|(J_i^\alpha)_{mn}|^2.$$

Replacing C by |C| preserves C^2 and the norm and cannot increase this Rayleigh quotient, because |c_m c_n|>=c_m c_n. The variational principle therefore gives a positive semidefinite ground eigenmatrix A.

If v is in ker A, take its expectation in the eigenmatrix equation. The h terms and eigenvalue term vanish, leaving

$$0=-g\sum_{i,\alpha}\langle J_i^\alpha v,A J_i^\alpha v\rangle.$$

Every summand is nonnegative before the minus sign, so all J_i^alpha preserve ker A. The single-site Pauli matrices generate the full matrix algebra on four qubits: products contain every Pauli tensor. Its only common invariant subspaces are zero and the whole space. Since A is nonzero, ker A=0.

For uniqueness, suppose D is an independent Hermitian ground eigenmatrix. The Hermitian matrix A^{-1/2}DA^{-1/2} is not scalar. At an appropriate finite endpoint of the interval on which $I+t A^{-1/2}DA^{-1/2}$ is positive semidefinite, A+tD is nonzero, positive semidefinite and singular. It is another ground eigenmatrix, contradicting the preceding kernel argument. If the complex ground eigenspace had larger dimension, its Hermitian real form would supply such a D. Thus the ground ray is unique. Strict positivity gives 16 nonzero singular values, hence full Schmidt rank. With g_i>0 the same sum-of-nonnegative-terms and irreducibility arguments apply. QED.

Uniqueness implies a positive spectral gap for each fixed finite-system parameter pair. It does not give a gap uniform as g tends to zero or a thermodynamic-limit gap. At g=0 the full ground space has dimension four, so that endpoint is excluded.

## 12. An exact three-dimensional ground-state problem, with a global certificate

Define the single-cell spectral projectors and their ranks by

$$P_0=\frac{(L-2I)(L-6I)}{12},\quad P_1=\frac{L(6I-L)}8,\quad P_2=\frac{L(L-2I)}{24},\qquad(d_0,d_1,d_2)=(2,9,5).$$

These are the full spin-zero, spin-one and spin-two sectors, including multiplicities. Write Xi_j=mathcal V(P_j)/sqrt(d_j). They are orthonormal physical eight-spin vectors. The following direct spin identities determine their exact invariant span. With mathcal Q(A)=sum_{i,alpha}J_i^alpha A J_i^alpha,

$$\mathcal Q(I)=3I,\qquad \mathcal Q(L)=L+6I,\qquad \mathcal Q(L^2)=-L^2+14L+12I,$$

or equivalently

$$\mathcal Q(P_0)=\frac23P_1,\quad
\mathcal Q(P_1)=3P_0+\frac32P_1+\frac32P_2,\quad
\mathcal Q(P_2)=\frac56P_1+\frac32P_2. \tag{12.1}$$

These finite identities follow by substituting $L=3I+2\sum_{i<j}\mathbf J_i\cdot\mathbf J_j$ and $J_i^\alpha J_i^\beta=\delta_{\alpha\beta}I/4+(i/2)\epsilon_{\alpha\beta\gamma}J_i^\gamma$. A Pauli tensor of weight w is an eigenvector of mathcal Q with eigenvalue 3-w; expanding L and L^2 gives the three displayed formulas. The companion program verifies them as full exact 16 by 16 identities and verifies the corresponding physical eight-spin action separately.

### Theorem 12.1. Exact ground block and cubic energy equation

For every Delta>0 and g>0 the full ground energy is the smallest eigenvalue of

$$\boxed{M(\Delta,g)=\begin{pmatrix}
0&-\sqrt2 g&0\\
-\sqrt2 g&2\Delta-3g/2&-\sqrt5 g/2\\
0&-\sqrt5 g/2&6\Delta-3g/2
\end{pmatrix}.} \tag{12.2}$$

Let alpha=(alpha_0,alpha_1,alpha_2)^T be its normalized lowest eigenvector with positive entries. Then the full physical ground state and its coefficient matrix are exactly

$$\Psi_0=\sum_{j=0}^2\alpha_j\Xi_j,\qquad
C_0=\sum_{j=0}^2c_jP_j,\qquad c_j=\alpha_j/\sqrt{d_j}>0. \tag{12.3}$$

In particular the ground energy is the smallest real root of

$$z^3+(3g-8\Delta)z^2+(12\Delta^2-12\Delta g-g^2)z+12\Delta g^2-3g^3=0. \tag{12.4}$$

Proof. Equation (12.1), the cell energies and Hilbert-Schmidt normalization give (12.2) on the Xi span. Since both off-diagonal couplings are strictly negative, replacing a real minimizing vector by its coordinatewise absolute value cannot raise the energy. A resulting nonnegative eigenvector cannot have a zero coordinate: its row equation forces its neighbor to be zero, and connectedness propagates this to every coordinate. Thus alpha is strictly positive. Its matrix C_0 is positive definite because the P_j are complementary projectors. Theorem 11.1 supplies a positive definite ground coefficient A for the full operator. One has Tr(A C_0)>0, so these two eigenmatrices cannot belong to distinct eigenvalues of a selfadjoint operator. Therefore the lowest block eigenvalue is the full ground eigenvalue, and uniqueness identifies its ray. The determinant of zI-M gives (12.4). QED.

This last positivity comparison certifies that no state in an omitted symmetry sector has lower energy. Merely diagonalizing a three-dimensional trial block would not establish that fact. The other two eigenvalues of M are not in general the first two excitations of the full H, so (12.2) is not a three-level replacement of its entire spectrum.

## 13. An exact majorization order from weak to strong coupling

Let lambda(g) be the 16 Schmidt probabilities of the normalized ground state across cells, in decreasing order. Their exact form is

$$\lambda(g)=\bigl((c_0^2)^{[2]},(c_1^2)^{[9]},(c_2^2)^{[5]}\bigr),$$

where bracketed superscripts specify multiplicity rather than powers.

### Theorem 13.1. Coupling orders the entire Schmidt spectrum

For fixed Delta>0 and 0<g_1<g_2,

$$\boxed{\lambda(g_1)\succ\lambda(g_2),} \tag{13.1}$$

with a strict inequality for every proper decreasing partial sum. In particular the pure-state cell-to-cell entanglement entropy increases strictly with g and obeys

$$1<S(\operatorname{Tr}_b|\Psi_0\rangle\langle\Psi_0|)<4\quad\text{bits},$$

with limiting values one as g/Delta tends to zero and four as g/Delta tends to infinity.

Proof. Set t=Delta/g and e(t)=lambda_min M(t,1). The ground eigenvalue is simple. Hellmann-Feynman gives

$$e'(t)=2\alpha_1^2+6\alpha_2^2\in(0,6).$$

The first and last rows of the eigenmatrix equation in the unnormalized projectors yield

$$x(t):=\frac{c_1}{c_0}=-\frac{e(t)}3>0,\qquad
r(t):=\frac{c_2}{c_1}=\frac{3/2}{6t-3/2-e(t)}>0. \tag{13.2}$$

Therefore x'(t)=-e'(t)/3<0 and r'(t)=-(3/2)(6-e'(t))/(6t-3/2-e(t))^2<0. At t=0 the normalized ground vector is (sqrt(2),3,sqrt(5))/4, with e=-3 and c_0=c_1=c_2=1/4. For t>0, consequently c_0>c_1>c_2>0. Both successive ratios increase strictly as g increases.

For two such couplings the ratios of the three groups of Schmidt probabilities, lambda_j(g_2)/lambda_j(g_1), increase strictly from group zero to group two. Their weighted average, with weights lambda(g_1), is one. Every proper leading partial set in the decreasing Schmidt order has a strictly smaller average ratio than the whole set, since the excluded entries have no smaller ratios and include an entry from a strictly larger group. This proves all partial-sum inequalities (13.1). Strict Schur concavity of the Shannon entropy gives strict increase; the majorization interpretation is standard [N99], rather than a new general entanglement-conversion theorem.

As t tends to infinity, the positive 2t and 6t terms force alpha_1,alpha_2 to zero: the trial alpha=(1,0,0) has energy zero and the remaining fixed matrix has bounded norm. Hence alpha_0 tends to one and the two nonzero limiting Schmidt probabilities are 1/2. At t=0 the 16 probabilities equal 1/16. Continuity supplies both limits. Since $2c_0^2+9c_1^2+5c_2^2=1$ and all c_j are positive, $c_0^2<1/2$. The order just proved makes every Schmidt entry at most c_0^2, so the entropy is at least $-\log_2 c_0^2>1$. The unequal c_j make the upper bound strict. QED.

The weak-coupling limiting vector is Xi_0=(H_+ tensor H_-+H_- tensor H_+)/sqrt(2). The strong-coupling limit is mathcal V(I/4), the product of four matched inter-cell spin singlets. Thus increasing coupling redistributes entanglement into the higher-spin sectors. It does not preserve exact singlet support of either cell, and this entanglement entropy is across cells, not the original four-qubit pure-state internal-cut objective.

## 14. Exact HS-pair recovery, including a coupling-independent deterministic protocol

### Proposition 14.1. Spin-zero filtering works throughout the positive-coupling range

Measure the two cell spin sectors, retain their outcome labels, and select the outcome (0,0). Applied to the full microscopic ground state, the postselected state is exactly Xi_0, with probability

$$\boxed{p_{00}=\alpha_0^2=2c_0^2,\qquad \frac18<p_{00}<1.} \tag{14.1}$$

It decreases strictly with g/Delta, tending to one at weak coupling and 1/8 at strong coupling. This is exact filtering at arbitrary positive coupling, not a fidelity statement about a truncated effective ground state.

Proof. Orthogonality of P_j gives (P_0 tensor P_0)Psi_0=alpha_0 Xi_0. By Theorem 13.1 the largest Schmidt entry c_0^2 decreases strictly. Its endpoints are 1/2 and 1/16, proving (14.1). Retaining the outcomes makes the success event explicit. Conditioning is not a trace-preserving operation; the unconditioned instrument includes the unsuccessful outcomes. QED.

### Theorem 14.2. One encoded ebit can be recovered deterministically by specified cell-local operations

There is a fixed one-way local-operations-and-classical-communication protocol, independent of Delta and g, that maps every density matrix supported on span{Xi_0,Xi_1,Xi_2} to the pure encoded Bell state Xi_0. It therefore applies to every uniform-matched ground state above. This stronger protocol allows arbitrary operations on the four spins within each cell; it is not restricted to exchange-only, spin-preserving or real-instrument readout menus.

Proof by construction. Choose a real orthonormal basis |j,k> of each P_j sector, 1<=k<=d_j. Then

$$\Xi_j=\frac1{\sqrt{d_j}}\sum_{k=1}^{d_j}|j,k\rangle_a\otimes\Theta|j,k\rangle_b.$$

For every j and unordered pair k<l, cell a uses the Kraus operator

$$A_{jkl}=\frac{|e_0\rangle\langle j,k|+|e_1\rangle\langle j,l|}{\sqrt{d_j-1}}.$$

Each |j,k> occurs in d_j-1 pairs. Thus sum_{j,k<l} A_{jkl}^dagger A_{jkl}=sum_j P_j=I_16. There are choose(2,2)+choose(9,2)+choose(5,2)=47 labelled outcomes. On receiving (j,k,l), cell b applies a unitary mapping the two orthogonal vectors Theta|j,k>,Theta|j,l> to e_0,e_1, respectively, completed arbitrarily on the orthogonal complement. Such an extension exists in the same 16-dimensional cell.

On a vector sum_j alpha_j Xi_j, the selected branch is

$$\frac{\alpha_j}{\sqrt{d_j(d_j-1)}}(e_0\otimes e_0+e_1\otimes e_1),$$

with probability 2|alpha_j|^2/[d_j(d_j-1)]. After normalization it is Xi_0 for every nonzero-probability outcome. The same map kills |Xi_j><Xi_k| for j!=k and sends each diagonal projector to |Xi_0><Xi_0|. Linearity therefore proves the assertion for every density matrix on the three-dimensional span. QED.

This is an explicit application of established deterministic entanglement-concentration principles [N99], not a new general LOCC theorem. Some branches change the cell's total spin and are not realizable by assuming only the earlier exchange-control menu. Their physical implementation and costs have not been supplied. With those broader cell-local operations allowed, the output is unconditional and no outcome label is silently discarded before its conditional correction. Trace-distance contraction also makes the deterministic protocol robust: an input within trace distance epsilon of any state on this span produces an output within epsilon of Xi_0.

## 15. Exact local input for arbitrary finite-graph energy bounds

Let a finite simple cell graph have maximum degree d>=1, uniform onsite scale Delta>0 and positive edge strengths g_e, with microscopic Hamiltonian

$$H_G=\frac\Delta2\sum_a L_a+\sum_{e=ab}g_e\sum_{i=0}^3\mathbf J_{ai}\cdot\mathbf J_{bi}.$$

Write E_*(Delta,g)=lambda_min M(Delta,g), the exact full two-cell energy from Theorem 12.1. For any graph matching mathcal M, whose edges have disjoint endpoints,

$$\boxed{\sum_{e\in E(G)}E_*(\Delta/d,g_e)\le E_0(H_G)\le\sum_{e\in\mathcal M}E_*(\Delta,g_e).} \tag{15.1}$$

Proof. Allocate Delta/(2d)(L_a+L_b) to every edge. The remaining onsite operator is Delta/2 sum_a(1-deg(a)/d)L_a, which is positive semidefinite. Each edge operator is bounded below by its exact two-cell ground energy, proving the left inequality, including graphs with triangles. For the upper bound, take the tensor product of exact two-cell ground states on the matching and arbitrary singlets on the unmatched cells. The pair ground states are total spin zero because every P_j in (12.3) commutes with collective rotations in the reflected representation. Every individual physical spin therefore has zero expectation. Each edge outside the matching connects different independent factors of this trial state, so its exchange expectation vanishes. The variational energy is exactly the right side. QED.

For a d-regular uniform graph on N cells with a perfect matching, this specializes to

$$\frac d2E_*(\Delta/d,g)\le\frac{E_0(H_G)}N\le\frac12E_*(\Delta,g). \tag{15.2}$$

These are nonperturbative bounds with finite per-cell scale, independent of N. The lower-bound mechanism is Anderson's established cluster construction, reviewed and extended for different pyrochlore motifs in [KP26]. The present contribution is its explicit substitution of the all-coupling eight-spin energy and the matching upper bound. It is not a size-uniform SW approximation, an optimal energy bracket, an exact thermodynamic energy, or a many-body spectral-gap theorem. Corners shared by physical spins in [KP26]'s motifs are different from the disjoint cells and matching links used here.

## 16. Verification, attribution and the remaining many-body problem

The new universal arguments concern a specified finite Hamiltonian and its graph-energy applications. They replace the weak-coupling premise for the uniform matched two-cell ground state with a full positivity argument, provide an exact ground block, establish an all-coupling Schmidt majorization order, and give explicit recovery instruments. The earlier perturbative determinant and triangle coefficients retain their different arbitrary-coupling-matrix scope. A three-cell loop's dynamics, its exact ground state, and an infinite chain's phase are not solved by Theorem 12.1.

The companion program is `docs/reports/hs4-rigidity/verify_nonperturbative_exchange.py` in experiments PR #11. It checks exact spin reversal, all three projectors, the full sandwich identities, the physical 256-by-3 invariant-subspace action, the symbolic cubic and the complete 47-branch recovery map on all nine sector matrix units. Separate bounded numerical checks compare full eight-spin ground states with the exact block over 37 logarithmically spaced ratios from 10^-3 to 10^3, test 12 unequal positive matched-link cases, and evaluate four complete three-cell graph energy brackets. The graph checks use the full magnetization-zero sector, which contains a representative of every total-spin eigenmultiplet for twelve spin-1/2 sites. No inequality is certified universally by the sampled ratios.

No new Lean compilation, inherited-certificate replay, independent mathematical review, historical-first claim, quantum hardware implementation or thermodynamic phase theorem is asserted. The reflected positive-coefficient argument and general majorization/LOCC interpretation retain their established source ownership. The precise finite formulas, domains and constructive proof steps above are the additional mathematical content. The next open scope is a uniform many-body description retaining actual loop corrections; the energy bounds (15.1) constrain that problem without claiming to solve it.

### Additional primary sources

- [LS00] E. H. Lieb and P. Schupp, *Singlets and reflection symmetric spin systems*, Physica A 279 (2000), 378-385. [arXiv:math-ph/9910037v1](https://arxiv.org/abs/math-ph/9910037v1), Sections 2-5, [DOI:10.1016/S0378-4371(99)00521-X](https://doi.org/10.1016/S0378-4371(99)00521-X). Supplies the established reflected coefficient-matrix method. The positivity and irreducibility proof needed for the present all-positive matched links is written in full above; uniqueness is not attributed to the abstract's weaker existence statement.
- [N99] M. A. Nielsen, *Conditions for a class of entanglement transformations*, Physical Review Letters 83 (1999), 436-439. [arXiv:quant-ph/9811053](https://arxiv.org/abs/quant-ph/9811053), [DOI:10.1103/PhysRevLett.83.436](https://doi.org/10.1103/PhysRevLett.83.436). Established majorization/LOCC context. The parameter ordering and the particular recovery instrument used here are derived above.
- [KP26] P. Kranitz and K. Penc, *Rigorous Anderson-type lower bounds on the ground-state energy of the pyrochlore Heisenberg antiferromagnet*, [arXiv:2601.07800v1](https://arxiv.org/abs/2601.07800v1), Introduction Eqs. (1)-(3), [DOI:10.1515/zna-2026-0009](https://doi.org/10.1515/zna-2026-0009). Source for current cluster-bound methodology and its distinct overlapping pyrochlore geometry. None of that paper's numerical lattice bounds is transferred to this model.

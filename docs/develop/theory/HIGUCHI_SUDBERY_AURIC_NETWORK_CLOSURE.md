# HS4, AURIC observable closure and quantum-network compatibility

## 1. Scope and exact source correspondence

This is a mathematical companion to [HS4 rigidity](HIGUCHI_SUDBERY_RIGIDITY.md), not a replacement of the inherited maximum theorem. The statements below have ordinary written proofs and finite symbolic checks; they have not been compiled in Lean or independently reviewed. Historical priority of the individual consequences is not asserted.

The source interfaces are deliberately kept distinct:

| Supplier | Consumed object | Boundary |
| --- | --- | --- |
| [AURIC seam and future quotient](AURIC_FIB_ATOM_SEAM_BILINEAR_CURVATURE_AND_OUTPUT_FUTURE_QUOTIENT.md), Sections 1-2 | Five legal occupancy modes, the four-dimensional observation space, its direction d and multiplication defect | An ordinary finite probability model; it does not construct a quantum state or Hamiltonian |
| [AURIC output-resolved instruments](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md), Section 15 and its editorial conditions | Closure under each labelled branch, with complete legal action/output histories | Averaged transitions alone need not determine recorded futures |
| [FIB legal interference](FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md), Sections 8.2-8.3, 8.10-8.12 | Explicit conditional coherent pulses, adjoint effects, and action-menu-dependent readout depth | The no11 occupation graph and its Hamming-depth theorem are not the HS4 exchange graph |
| [Triangle source geometry](TRIANGLE_NETWORK_SOURCE_INDEPENDENCE_AND_FIBER_GEOMETRY.md), Sections 1-2 | Independent edge sources, two-edge responses, and the separate FIB pushforward | Observable correlation is not evidence of source dependence or network nonlocality |
| [HS4 rigidity](HIGUCHI_SUDBERY_RIGIDITY.md), Sections 4-5 | The real two-dimensional singlet basis, conjugate endpoints, their six marginals and scalar chirality | Static parent-Hamiltonian locality is different from dynamical readout locality |

AURIC's probability/phase distinction is also explicit in [Probability, Phase Transport and Holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md), Section 2.3. Its pure-state extension requires supplied phases. The two models below share an observable-completion mechanism, not a state-space isomorphism, a Fibonacci dimension law, or an inferred physical implementation.

All four physical qubits are labelled A,B,C,D. The computational amplitude index is 8a+4b+2c+d. Write S_XY for the qubit swap and sigma^a for Pauli matrices, with sigma^y=[[0,-i],[i,0]]. Let e_0,e_1 be the real orthonormal singlet basis in HS4 rigidity Section 4, E the 16 by 2 matrix with these columns, and Pi=EE^dagger. Put

$$H_\pm=(e_0\pm i e_1)/\sqrt2,\qquad \Pi_\pm=|H_\pm\rangle\langle H_\pm|,$$

$$\sigma_r=\frac{1+r}{2}\Pi_++\frac{1-r}{2}\Pi_-,\qquad -1\le r\le1.$$

In the ordered basis e_0,e_1, use logical Pauli matrices X_L,Y_L,Z_L. Then

$$E^\dagger\sigma_r E=(I_2+rY_L)/2.$$

The parameter r=2t-1 is the entire literal two-body marginal fiber from the preceding volume. Only its endpoints are pure. None of the mixed states is declared a pure-state entropy maximizer.

## 2. The precise classical-to-quantum closure correspondence

### Proposition 2.1. Two different defects of incomplete observation

On AURIC's ordered five-mode carrier (0,1,2,3,13), with x denoting position 1, y position 3 and z position 2, write

$$\mathcal B_{\rm cl}=\operatorname{span}_{\mathbb R}\{1,x,y,z\},\qquad d=(1,-1,0,-1,1)^T.$$

The allowed occupation vectors are (0,0,0),(1,0,0),(0,0,1),(0,1,0),(1,1,0). Thus xz=yz=0, xy=1_{13}, and

$$d^T1=d^Tx=d^Ty=d^Tz=0,\qquad d^Txy=1.$$

For f=a+bx+cy+ez and g=a'+b'x+c'y+e'z,

$$d^T(fg)=bc'+cb'.$$

Consequently adjoining the product xy completes the observable space from dimension four to the full five-dimensional function space. This is the supplier's multiplication defect, with the exact dictionary above.

For the HS4 singlet subspace, the restrictions of all static Hermitian operators supported on at most two qubits span exactly

$$\mathcal B_{\rm q}=\operatorname{span}_{\mathbb R}\{I_2,X_L,Z_L\}.$$

Its Hilbert-Schmidt annihilator in Hermitian two by two matrices is R Y_L. For F=aI+bX_L+cZ_L and G=a'I+b'X_L+c'Z_L,

$$i[F,G]=2(bc'-cb')Y_L,\qquad FG+GF\in\mathcal B_{\rm q}. \tag{2.1}$$

The classical defect is symmetric; the quantum commutator defect is alternating. Both exhibit an observable space that loses information needed by a specified composition operation. They are not the same bilinear form.

Proof of the quantum restriction. The singlet subspace is pointwise fixed by collective SU(2). Rotations by pi make every restricted one-body Pauli matrix vanish and force the off-diagonal components of a restricted two-body Pauli tensor to vanish. Rotations permuting axes make its three diagonal components equal. Therefore

$$E^\dagger\sigma_X^a\sigma_Y^b E=\frac{\delta_{ab}}3 E^\dagger(2S_{XY}-I)E.$$

Direct substitution of e_0,e_1 gives

$$\widehat S_{AB}=\widehat S_{CD}=Z_L,$$
$$\widehat S_{AC}=\widehat S_{BD}=-\tfrac12Z_L-\tfrac{\sqrt3}{2}X_L,$$
$$\widehat S_{AD}=\widehat S_{BC}=-\tfrac12Z_L+\tfrac{\sqrt3}{2}X_L,$$

where a hat denotes E^dagger(.)E. A Hermitian two-local operator has a real Pauli expansion, proving containment; the displayed swaps and identity prove equality. Pauli multiplication proves (2.1). The classical formula follows by x^2=x, y^2=y, z^2=z and xz=yz=0. QED.

In particular, for every such static quantum observable M,

$$\operatorname{Tr}(\sigma_r M)\text{ is independent of }r.$$

The two dimensions relevant to completion are 4 to 5 for classical functions and 3 to 4 for Hermitian operators on the singlet qubit. Counting three classical means and three logical Pauli directions does not identify the underlying carriers.

### 2.2. Output-resolved future completion

For a declared finite-dimensional quantum instrument with branches I_{a,o}, define its Heisenberg adjoint by Tr(I_{a,o}(rho)F)=Tr(rho I_{a,o}^*(F)). Starting with a supplied terminal observable space W_0 containing I, set

$$W_{n+1}=\operatorname{span}_{\mathbb R}\left(W_n\cup\{I_{a,o}^*(F):F\in W_n,\ (a,o)\text{ allowed}\}\right).$$

A fixed action/output word has probability given by an iterated adjoint applied to I. Consequently the full recorded-future quotient is the annihilator of W_infinity, relative to the stated initial state domain and legal menu. This is the quantum version of the supplier's branchwise finite observation closure: on diagonal density matrices and diagonal tests the adjoints reduce to the corresponding classical subkernels. If W_n=W_{n+1}, the space is invariant under every allowed branch and all longer words add nothing. Finite-dimensional stabilization follows, without a finite-sample identifiability claim.

For history-dependent menus this recurrence must use the actual allowed history states or a declared menu-preserving enlargement. A quantum preparation map from AURIC histories into the HS4 singlet subspace has not been supplied. The correspondence established here is the displayed observable/adjoint construction, with different concrete state spaces.

## 3. Tetrahedral pair realizations and a sharp global gluing obstruction

Every sigma_r has the same six literal pair marginals

$$R=\frac16I_4+\frac13|s\rangle\langle s|=\frac14\left(I_4-\frac13\sum_a\sigma^a\otimes\sigma^a\right),\qquad s=(|01\rangle-|10\rangle)/\sqrt2.$$

### Theorem 3.1. Separable pairs, with no fully separable global completion

Let n_1,...,n_4 be the tetrahedral unit vectors (1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1), each divided by sqrt(3). For a unit n put P(n)=(I+n dot sigma)/2. Then

$$R=\frac14\sum_{j=1}^4 P(n_j)\otimes P(-n_j). \tag{3.1}$$

Thus each pair is separable. Nevertheless, no fully separable four-qubit density matrix has all six pair marginals R. More precisely, if D(rho,tau)=||rho-tau||_1/2, then

$$\boxed{\min_{\omega\ \mathrm{fully\ separable}}\frac16\sum_{X<Y}D(\omega_{XY},R)=\frac16.} \tag{3.2}$$

Proof. The tetrahedron has sum_j n_j=0 and (1/4)sum_j n_j n_j^T=I_3/3. Expanding the product projectors proves (3.1).

For a product state with local Bloch vectors r_X, |r_X|<=1, the total-spin operator L=sum_{X<Y} S_XY satisfies

$$\langle L\rangle=3+\frac12\sum_{X<Y}r_X\cdot r_Y
=3+\frac14\left(|\sum_Xr_X|^2-\sum_X|r_X|^2\right)\ge2.$$

Convexity gives Tr(omega L)>=2 for every fully separable omega. But Tr(R S)=0, and each swap has operator norm one. Trace duality therefore gives

$$2\le\sum_{X<Y}\operatorname{Tr}[S_{XY}(\omega_{XY}-R)]\le\sum_{X<Y}||\omega_{XY}-R||_1.$$

For attainment, let B be the six sign vectors s in {+1,-1}^4 with sum_X s_X=0. The explicitly fully separable state

$$\omega_* =\frac1{24}\sum_{j=1}^4\sum_{s\in B}\bigotimes_X P(s_X n_j)$$

has, for every pair,

$$\omega_{*,XY}=R'=\frac14\left(I_4-\frac19\sum_a\sigma^a\otimes\sigma^a\right).$$

Indeed the balanced-sign average has E s_X=0 and E(s_X s_Y)=-1/3 for distinct parties, and the tetrahedral second moment supplies another factor 1/3. The difference R-R' has eigenvalues 1/6,-1/18,-1/18,-1/18. Hence ||R-R'||_1=1/3 and the average trace distance is 1/6. This saturates the lower bound. QED.

This supplies an explicit common-source compatibility obstruction, including a tight distance and an attaining approximation. Independent pairwise separable decompositions cannot be glued into a fully separable global state. The obstruction is not a Bell-locality inequality: a classical hidden-variable response model is a different mathematical class from a separable density-matrix preparation, and quantum triangle sources may themselves be entangled.

The tetrahedral second moment is the exact geometric bridge used here. It neither identifies HS4 with the EJM distribution nor turns the five-mode AURIC pyramid into a four-vector tetrahedron.

## 4. The missing tensor is orientation-sensitive, and its readout can still be triangle-local

### Theorem 4.1. All fixed three-party projective statistics

For unit Bloch directions a,b,c and outcomes x,y,z in {+1,-1}, measure a dot sigma_A, b dot sigma_B and c dot sigma_C on sigma_r, without using D. The exact joint law is

$$\boxed{p_r(x,y,z\mid a,b,c)=\frac18\left[1-\frac{xy\,a\cdot b+xz\,a\cdot c+yz\,b\cdot c}{3}-\frac{r\,xyz}{\sqrt3}\,a\cdot(b\times c)\right].} \tag{4.1}$$

Proof. All one-body means vanish and the pair tensor is -delta_ab/3 by R. Direct Pauli evaluation on H_+ gives <sigma_A^a sigma_B^b sigma_C^c>=-epsilon_abc/sqrt(3); on its conjugate the sign reverses. Equivalently, collective rotation invariance makes this tensor alternating, and <K_ABC>=-2sqrt(3)r fixes its coefficient since sum epsilon_abc^2=6. Multilinearity gives the scalar triple product, and expanding the three projectors gives (4.1). QED.

The pair terms depend only on the Gram matrix of the measurement directions. The last term additionally detects oriented volume. Reflection preserves that Gram matrix and reverses the oriented term. This explains exactly which additional structure is lost by a pairwise symmetric description in this example.

For discrimination of H_+ versus H_- with equal priors using one fixed product projective setting on A,B,C, the total-variation distance of the output laws is

$$\operatorname{TV}(p_+,p_-)=\frac{|a\cdot(b\times c)|}{\sqrt3}\le\frac1{\sqrt3}.$$

The bound is attained by orthonormal directions. Therefore the optimal success probability within this specified measurement class is (1+1/sqrt(3))/2. This is not a bound for adaptive LOCC, a fourth-party measurement, general POVMs, or coherent exchange controls.

### Proposition 4.2. An exact independent-source triangle lift for the orthogonal setting

For an oriented orthonormal triple the law is p_r(x,y,z)=[1+v xyz]/8 with v=-r/sqrt(3). In fact every distribution of this form, -1<=v<=1, is classical triangle-local.

Proof. Take three independent fair signs alpha,beta,gamma on the three source edges and an independent private sign eta at C with E eta=v. Define

$$x=\beta\gamma,\qquad y=\gamma\alpha,\qquad z=\eta\alpha\beta.$$

Each party uses precisely its two incident edge sources; eta is private local randomness absorbed in C's response. The pair x,y is uniform, xyz=eta, and conditioning on eta gives the four equiprobable triples of the corresponding parity. Thus p(x,y,z)=[1+v xyz]/8. No common three-party selector is introduced. QED.

The construction reproduces one fixed setting. It does not provide a setting-independent model for the full directional family (4.1). It is a concrete reason to keep three claims separate: the global quantum states differ, a three-body experiment sees the difference, and that particular output distribution is nevertheless compatible with independent classical triangle sources. The latter question has different quantifiers from state reconstruction.

## 5. Arbitrarily long real-instrument histories remain blind

### Theorem 5.1. Conjugation blindness of the complete recorded process

Consider any finite adaptive protocol whose branch CP maps admit Kraus matrices that are real in the fixed computational basis, up to a phase for each Kraus matrix. The same policy is used for both input hypotheses; private randomness is independent of the unknown hypothesis. Terminal effects are real. Then every complete finite action/output record has the same probability on H_+ and H_-, and hence on every sigma_r. Positive-probability postselection and subsequent protocols from this menu preserve that equality.

Proof. A composed branch has real Kraus representatives obtained by multiplying the real matrices. Its terminal effect is a sum of matrices B^T F B with B real and F real symmetric. It is therefore real symmetric. For such an effect T,

$$\langle H_-|T|H_-\rangle=\overline{\langle H_+|T|H_+\rangle}=\langle H_+|T|H_+\rangle,$$

because the probability is real. Adaptive policies multiply each fixed history probability by the same conditional action weights under both hypotheses. Summing unretained Kraus outcomes or classical random seeds preserves equality. Conditioning divides equal joint probabilities by equal nonzero event probabilities. These statements hold for every finite history length by the same composition argument. QED.

In particular the theorem applies to arbitrary histories of pair singlet/triplet projective measurements, real swap gates, and classical control, with all outputs retained. This is a menu-specific no-go theorem. Arbitrary two-local instruments need not have real Kraus representations; three successive one-qubit measurements can also retain a three-body correlation, as (4.1) shows. Those larger menus are not excluded.

Having real exchange Hamiltonian coefficients does not make an exchange pulse real: exp(-itH) is generally complex. This is the resource introduced next.

## 6. One coherent two-local pulse completes the hidden coordinate

### Theorem 6.1. Perfect chirality readout with one two-local pulse

Supply the signed exchange control

$$G=\frac{S_{AD}-S_{AC}}{\sqrt3},\qquad U_\theta=\exp(-i\theta G),$$

followed by the pair measurement (I+S_AB)/2, (I-S_AB)/2. A control call may turn on the displayed two overlapping exchange terms together with their specified relative sign. It is not a single elementary swap gate.

The singlet subspace is invariant under G and

$$E^\dagger G E=X_L,\qquad E^\dagger U_\theta^\dagger S_{AB}U_\theta E=\cos(2\theta)Z_L+\sin(2\theta)Y_L.$$

Thus the outcome o in {+1,-1} has

$$\boxed{\Pr_r(o\mid\theta)=\frac{1+or\sin(2\theta)}2.} \tag{6.1}$$

At theta=pi/4, the result is deterministic +1 on H_+ and -1 on H_-. On the full fiber, the probability of +1 is (1+r)/2=t. The minimum number of such coherent calls before a single pair readout is exactly one: zero calls are blind by Proposition 2.1.

Proof. The compressed swap matrices in Section 2 give G=X_L. Their full matrices preserve the singlet subspace, so compressing the exponential is legitimate. The Pauli identity exp(i theta X) Z exp(-i theta X)=cos(2theta)Z+sin(2theta)Y gives the effect and (6.1). For a full-space exact check, the transpositions obey S_AD S_AC S_AD=S_AC S_AD S_AC. With both squares equal to I, this implies G^3=G and hence

$$U_\theta=I+(\cos\theta-1)G^2-i\sin\theta G.$$

Its restriction is the displayed logical rotation. G has operator norm one since G^3=G and its restriction has eigenvalues +/-1. QED.

The completed observable space is exactly Herm(2): I,X_L,Z_L are already obtained from static two-body data and the pulse contributes Y_L. Its dimension increases from three to four and its singlet-state kernel vanishes. This is the HS4 realization of output-future completion; it is not the Fibonacci-cube shortest-path theorem with renamed vertices.

There is no conflict with the preceding two-local parent-Hamiltonian impossibility. Unique-ground-state selection is a static spectral task; (6.1) is a controlled dynamical task followed by measurement. No three-body Hamiltonian is turned on. The supplied control needs signed couplings and calibrated time; neither its hardware availability nor an ancilla-free gate synthesis cost is asserted.

For comparison, using only the single elementary control exp(-i theta S_AB) and then measuring S_AC gives contrast (sqrt(3)/2)sin(2theta). At theta=pi/4 its equal-prior success is (2+sqrt(3))/4, below one. This comparison is for that specified control/readout pair and is not a universal optimality statement for every elementary pulse protocol.

### Corollary 6.2. Finite sampling, calibration error and record erasure

For |r|<1 and the regular outcomes in (6.1), the classical Fisher information per preparation is

$$J_\theta(r)=\frac{\sin^2(2\theta)}{1-r^2\sin^2(2\theta)}.$$

At theta=pi/4 this is 1/(1-r^2), the quantum Fisher information of the commuting family sigma_r with orthogonal eigenprojectors Pi_+,Pi_-. The sample mean of N independent +/-1 outcomes is an unbiased estimator of r with variance (1-r^2)/N. The endpoint cases have deterministic outcomes and are treated directly rather than by a regular Fisher formula. This does not give finite-sample exact knowledge of a general r.

If the pulse has angle pi/4+delta, the wrong outcome probability on either exact endpoint is sin^2(delta). If the actual input is within trace distance epsilon of that endpoint, the wrong-outcome probability is at most sin^2(delta)+epsilon, by unitary and measurement contraction. These are calibrated, trusted-model bounds.

Finally choose an independent fair pulse sign s and apply U_{s theta}. The recorded joint law is

$$\Pr_r(s,o)=\frac14[1+sor\sin(2\theta)].$$

Retaining s permits the informative statistic so. Discarding s gives Pr_r(o)=1/2 for every r. This is an exact quantum example of the AURIC distinction between output-resolved closure and averaging away the record. It requires no informal identification of an average channel with each of its branches.

## 7. The three-cycle commutator and the proper network boundary

The inherited scalar chirality is

$$K_{ABC}=2i(S_{AB}S_{BC}-S_{BC}S_{AB}),\qquad E^\dagger K_{ABC}E=-2\sqrt3Y_L.$$

The two products are opposite oriented three-cycles. Their difference supplies the alternating quantity absent from static pair observation, and the control commutator i[G,Z_L]=2Y_L exposes precisely the same missing logical direction. Thus orientation, a specified noncommuting composition, and a phase-sensitive readout fit into one exact finite model.

The graph roles must still be distinguished. An HS4 exchange edge is an allowed operator coupling. A FIB legal edge is an allowed occupation flip. A triangle-network edge is an independent source. Giving these three edge sets the same drawing supplies no map between their operator algebras, source products or resource costs.

The EJM nonclassicality result [GR25] uses the actual independent-source scenario and an exact inflation certificate. Fully quantum inflation [SWS25] studies which multipartite states admit a given quantum source network. Neither conclusion follows solely from the hidden coordinate of sigma_r, from the tetrahedral ensemble (3.1), or from a nonzero triple correlator. Proposition 4.2 gives a concrete local readout counterexample to that inference. This boundary is a mathematical part of the connection, not an unresolved wording issue.

## 8. Attribution and formalization targets

Exchange-only encoded quantum control is established background [DBKBW00], not a newly discovered capability. The contributions derived here are the explicit HS4 observable kernel and defect, the signed one-call chirality readout, the complete real-instrument record obstruction, the exact information/record-loss formulas, the tetrahedral gluing distance with an attaining separable preparation, and the fixed-setting triangle lift. Their historical novelty has not been exhaustively checked.

The quantum-network definitions and general source/product distinction are reused from the cited repository volume. The five-mode probability formulas and observable-completion supplier retain their original ordinary-proof status. The new arguments use the explicit HS4 singlet states and do not require a new replay of the global entropy certificate to establish the finite readout or separability conclusions. Their interpretation as properties of every maximizer additionally uses the equality classification in the preceding volume and transports the calibrated observables by the same product local unitaries.

The useful Lean targets are the full-space compression and cubic identities; the all-history real-Kraus argument; the one-pulse probability theorem; the fully separable witness and attaining 24-term preparation; and the independent-source parity construction. No new Lean, Scribe, freeze, registration, full-certificate replay or CI-success claim is made here. Experiments belong to the companion repository under docs/reports/hs4-rigidity. Finite symbolic checks are supporting evidence and do not replace the all-history or all-separable-state proofs above.

### References

- [DBKBW00] D. P. DiVincenzo, D. Bacon, J. Kempe, G. Burkard, K. B. Whaley, *Universal Quantum Computation with the Exchange Interaction*, Nature 408 (2000), 339-342. [arXiv:quant-ph/0005116](https://arxiv.org/abs/quant-ph/0005116), DOI [10.1038/35042541](https://doi.org/10.1038/35042541). Established exchange-only universality; the present four-qubit finite readout is derived explicitly and is not attributed as the paper's circuit.
- [GR25] V. Gitton and R. Renner, *The Elegant Joint Measurement is Non-Classical in the Triangle Network*, [arXiv:2510.15143](https://arxiv.org/abs/2510.15143). Exact computer-assisted EJM nonclassicality via inflation and symmetry reduction; cited for network scope, not as a certificate replay in this companion.
- [SWS25] I. D. Smith, E. Wolfe, R. W. Spekkens, *Fully quantum inflation: quantum marginal problem constraints in the service of causal inference*, [arXiv:2501.12320](https://arxiv.org/abs/2501.12320). State-network compatibility is distinct from the compatibility of one measured probability distribution.

## 9. A concrete spatial cell: the smallest quantum tetrahedron

The spatial interface used here is the finite-state, CPTP inverse-limit construction of [Typed Bridges, first continuation, Section 32](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE_CONTINUATION.md). That construction requires actual completely positive bonding maps and does not assert a smooth spacetime. The following finite cell makes the hidden observable and the permitted coarse-graining explicit. All new claims in Sections 9-13 are ordinary mathematical derivations, not Lean-verified declarations.

Set J_X=sigma_X/2 in dimensionless units and let C=Inv((C^2)^{tensor 4})=ker J_total^2. The isometry E already defined above identifies C with C^2. The quantum-tetrahedron interpretation assigns the four spins to four faces, fixes each area Casimir J_X^2=3I/4, and imposes closure sum_X J_X=0 on C. These are the established intertwiner construction [B98, S13]; they are additional geometric semantics for this carrier, not a derivation of gravity from FIB occupancies. AURIC occupation labels and face-spin labels remain different objects.

Amelung-Sahlmann [AS26] investigate entanglement of precisely this class of invariant tensors, including spin 1/2, but their principal objective is entropic fill. Their entropic tetrahedron, the coherent-state label geometry and the quantum volume operator are distinct constructions. Their results do not supply the unrestricted HS average-von-Neumann-entropy theorem. We use their work to locate the geometric question, not as an unproved identification of entropy and physical volume.

### Proposition 9.1. Oriented volume and volume magnitude separate already at spin 1/2

Define the signed triple-product operator

$$Q_{\rm geom}=\mathbf J_A\cdot(\mathbf J_B\times\mathbf J_C)=K_{ABC}/8.$$

Its restriction and square are

$$\widehat Q_{\rm geom}=-\frac{\sqrt3}{4}Y_L,\qquad \widehat{Q_{\rm geom}^2}=\frac3{16}I_2. \tag{9.1}$$

In the dimensionless volume convention of [S13], Section 2, Eqs. (3)-(5),

$$V_{\rm red}=\frac{\sqrt2}{3}\sqrt{|\widehat Q_{\rm geom}|}=\frac{\sqrt2\,3^{1/4}}6 I_2. \tag{9.2}$$

Thus every state on C has the same positive volume magnitude and volume distribution in this convention. H_+ and H_- are the two signed-volume eigenvectors, with eigenvalues -sqrt(3)/4 and +sqrt(3)/4. Their significance is sharp orientation, not a larger magnitude of (9.2) than other singlet states.

Proof. The already displayed compression of K gives (9.1). Functional calculus of its two eigenvalues gives (9.2). As a concrete distinction, e_1 is the product of the AB and CD singlets up to a phase; its average two-versus-two entropy is (0+2+2)/3=4/3, strictly below F_*, while (9.2) is unchanged. Physical area and volume units, if adopted from loop quantum gravity, require their separately supplied scale factors. QED.

### Proposition 9.2. The complete boundary-shape disk and orientation fiber

Every density matrix supported on C has a unique logical representation

$$\rho(u,v,w)=E\frac{I_2+uX_L+vY_L+wZ_L}{2}E^\dagger,\qquad u^2+v^2+w^2\le1.$$

Let s_1,s_2,s_3 be the expectations of S_AB,S_AC,S_AD, respectively. Then

$$s_1=w,\qquad s_2=-\frac w2-\frac{\sqrt3u}{2},\qquad s_3=-\frac w2+\frac{\sqrt3u}{2},$$

$$s_1+s_2+s_3=0,\qquad \sum_c s_c^2=\frac32(u^2+w^2),\qquad \langle Q_{\rm geom}\rangle=-\frac{\sqrt3}{4}v. \tag{9.3}$$

The set of attainable boundary expectations is exactly the disk

$$\sum_c s_c=0,\qquad \frac23\sum_c s_c^2\le1.$$

Above each disk point the full mixed-state fiber is

$$-\sqrt{1-\frac23\sum_c s_c^2}\le v\le\sqrt{1-\frac23\sum_c s_c^2}. \tag{9.4}$$

Only the two endpoints are pure in the disk interior; on its boundary they coincide. At its center they are H_+ and H_-. The pure-state Bloch sphere therefore projects to the boundary-data disk as two orientation sheets meeting on the circle. This is a map between state and observation spaces, not a spatial-dimension theorem.

Proof. The swap compressions of Section 2 give (9.3); their inverse is w=s_1 and u=(s_3-s_2)/sqrt(3). Positivity of the logical density matrix is equivalent to the ball inequality, yielding the entire fiber (9.4). Rank one is equality in that ball inequality. At the disk center the normalized pair angle means are <J_X dot J_Y>/(3/4)=-1/3, the regular tetrahedral Gram data, for every v in the fiber. They cannot select its orientation or purity. QED.

## 10. An exact entropy-shape identity and sharper singlet stability

For mixed states in this section, F_s denotes the average entropy of the internal two-qubit marginals. It is an entanglement entropy across those cuts only when the four-qubit state itself is pure. It is not a mixed-state entanglement measure.

### Theorem 10.1. Entropy deficit is a binary relative-entropy cost of shape

For every rho(u,v,w), the pair marginal with swap expectation s has spectrum

$$\left(\frac{1-s}{2},\frac{1+s}{6},\frac{1+s}{6},\frac{1+s}{6}\right).$$

Writing h_2 for binary entropy in bits and Delta_s=F_*-F_s, one has

$$F_s=\frac13\sum_c h_2\left(\frac{1+s_c}{2}\right)+\frac12\log_2 3,$$

$$\boxed{\Delta_s=\frac1{3\ln2}\sum_c D_{\rm KL}\left(\left(\frac{1+s_c}{2},\frac{1-s_c}{2}\right)\middle\|\left(\frac12,\frac12\right)\right).} \tag{10.1}$$

Consequently, with r_perp^2=u^2+w^2,

$$\boxed{\frac{r_\perp^2}{4\ln2}\le\Delta_s\le\frac{r_\perp^2}{2}.} \tag{10.2}$$

Proof. Collective SU(2) invariance makes each marginal a mixture of the singlet projector P_s and its triplet complement: rho_pair=(1-s)P_s/2+(1+s)(I-P_s)/6. The singlet has swap eigenvalue -1, the triplet +1, so the weights and multiplicities are exact. Opposite pairs have equal marginals by the compressed swap identities. Evaluating the entropy and using sum_c s_c=0 proves (10.1). For |s|<=1, put

$$f(s)=\frac{(1+s)\ln(1+s)+(1-s)\ln(1-s)}2.$$

It obeys f(0)=f'(0)=0 and f''(s)=1/(1-s^2)>=1, so f(s)>=s^2/2. Its power series is sum_{n>=1} s^{2n}/[2n(2n-1)]. The positive coefficients sum to f(1)=ln2, whence f(s)<=ln2 s^2, including the endpoints by continuity. Sum these estimates and use (9.3). The lower constant in (10.2) is attained in the limit r_perp to zero. This is an independent proof within C; it does not replace the inherited all-state HS4 certificate. QED.

### Corollary 10.2. Pure-state orientation rigidity with square-root scaling

For a pure state in C, v^2=1-r_perp^2 and its best squared overlap with the two fixed endpoints is (1+|v|)/2. Therefore

$$\max_{s\in\{+,-\}}|\langle H_s|\psi\rangle|^2\ge1-2\ln2\,\Delta_s,$$

$$\min_{s,\theta}\|\psi-e^{i\theta}H_s\|_2\le2\sqrt{\ln2\,\Delta_s}. \tag{10.3}$$

The exponent 1/2 cannot be increased uniformly near these endpoints: take the pure Bloch vector (t,sqrt(1-t^2),0). Then Delta_s=t^2/(4ln2)+O(t^4), while the ray distance is |t|/2+O(|t|^3). The coefficient in (10.3) is conservative. The improvement over the preceding general Delta^(1/4) estimate assumes exact support in this calibrated singlet subspace; it is not an improved all-state exponent.

Proof. The infidelity equals (1-|v|)/2<=r_perp^2/2. Apply (10.2), then use ray distance squared <= twice the infidelity. The expansions follow from the positive series in the theorem and the displayed overlap. QED.

There is also a direct geometric uncertainty statement for these pure states:

$$\frac4{3\ln2}\operatorname{Var}(Q_{\rm geom})\le\Delta_s\le\frac83\operatorname{Var}(Q_{\rm geom}), \tag{10.4}$$

because Var(Q_geom)=3(1-v^2)/16. Within this sector, maximal average entropy is equivalent to zero signed-volume uncertainty. Volume magnitude alone, as (9.2) shows, gives no such criterion.

## 11. A boundary quotient is not automatically a quantum bonding map

The inverse-limit model in the cited dev Section 32 requires its bonding maps to be CPTP restrictions. The shape projection of Section 9 is a valid affine observation quotient, but converting its output back into a logical qubit introduces a further requirement.

### Theorem 11.1. Exact obstruction and optimal symmetric quantum approximation

The complex-linear map that keeps both visible logical components and removes only orientation is

$$\mathcal D(M)=\frac{M+M^T}{2},\qquad (u,v,w)\longmapsto(u,0,w).$$

It is positive, trace preserving and idempotent, but is not completely positive. With the normalized Bell-state convention, its Choi eigenvalues are

$$\frac34,\quad\frac14,\quad\frac14,\quad-\frac14. \tag{11.1}$$

More generally consider the explicitly declared unital family

$$\Phi_{\eta,\kappa}: (u,v,w)\longmapsto(\eta u,\kappa v,\eta w),\qquad \eta\ge0.$$

It is CPTP exactly when

$$-1\le\kappa\le1,\qquad 2\eta\le1+\kappa. \tag{11.2}$$

In particular exact orientation erasure, kappa=0, permits at most eta=1/2. This bound is attained by

$$\Phi_{1/2,0}(M)=\frac12 M+\frac14X_LMX_L+\frac14Z_LMZ_L. \tag{11.3}$$

Proof. D preserves the Bloch ball, giving positivity. Its Choi matrix is (id tensor D)(|Phi_+><Phi_+|), which has the spectrum (11.1); the singlet Bell vector has expectation -1/4. This already disproves complete positivity. For the general family the four Bell eigenvalues are

$$\frac{1+2\eta+\kappa}{4},\quad\frac{1-\kappa}{4},\quad\frac{1-2\eta+\kappa}{4},\quad\frac{1-\kappa}{4}.$$

Nonnegativity is (11.2), by the finite Choi criterion [C75]. Conversely these four nonnegative numbers are the probabilities for conjugation by I,X,Y,Z, proving sufficiency directly. Substitution gives (11.3). QED.

The 1/2 optimum is stated for this same-input/same-output logical-qubit family, without postselection or an extra output system. It is not a limit on extracting classical shape statistics. In fact the four POVM effects

$$E_{X\pm}=(I\pm X_L)/4,\qquad E_{Z\pm}=(I\pm Z_L)/4$$

define a CPTP classical record map, with probabilities (1+u,1-u,1+w,1-w)/4. The labelled probabilities recover u and w exactly as statistical parameters. A claimed CPTP decoder that turns these records into D(rho) for every input would compose to D and is therefore impossible. Finite samples introduce ordinary statistical uncertainty.

This provides two lawful options for the spatial hierarchy: retain a quantum cell with the noise tradeoff (11.2), or retain a classical labelled observation register. Keeping a disk of expectation values is a third, purely mathematical description; it must not silently be declared a same-qubit physical channel. The obstruction concerns all states on C, including their entangled extensions. On a single fixed fiber or a singleton domain a constant channel can agree with D, so the all-state scope is essential.

## 12. Assembling cells: local purity is a separate entanglement budget

Choose a finite graph with N vertices and explicitly use C^{tensor N} as its node-intertwiner Hilbert space. Edges specify possible couplings or constraints; no independent-source preparation is assumed. Let Omega be any density matrix on this space and rho_a its logical one-node marginal. Define zeta_a=1-Tr(rho_a^2), Delta_a as in Section 10, and choose H_{s_a} to have the sign of that node's Y_L expectation (either sign at zero).

### Theorem 12.1. A quantitative node-product bound

One has

$$\boxed{\langle\bigotimes_a H_{s_a}|\Omega|\bigotimes_a H_{s_a}\rangle\ge\max\left\{0,1-\sum_a\left(\zeta_a+2\ln2\,\Delta_a\right)\right\}.} \tag{12.1}$$

Thus requiring every node to be an exact pure HS endpoint forces the whole node-intertwiner state to be their product. Such a state has no entanglement between these node factors, although it has the already established internal four-spin entanglement.

Proof. At node a, 2zeta_a=1-u_a^2-v_a^2-w_a^2. Its infidelity to the selected endpoint is

$$(1-|v_a|)/2\le(1-v_a^2)/2=\zeta_a+(u_a^2+w_a^2)/2\le\zeta_a+2\ln2\,\Delta_a.$$

The N endpoint projectors commute since they act on different factors. Simultaneous diagonalization gives I-product_a P_a <= sum_a(I-P_a). Trace this inequality against Omega and substitute the local bounds. A rank-one projector with expectation one contains the full support of a positive trace-one matrix, proving exact product rigidity. QED.

The purity term cannot be deleted. For N>=2,

$$|\mathrm{cat}_N\rangle=\frac{|H_+\rangle^{\otimes N}+|H_-\rangle^{\otimes N}}{\sqrt2} \tag{12.2}$$

is entangled across every nontrivial node bipartition. Each node marginal is Pi/2, with Delta_a=0 and zeta_a=1/2. All six internal two-body marginals at every node are still R. The product |H_+>^{tensor N} has exactly the same individual-node pair observations. Consequently a hierarchy keeping only these local boundary statistics cannot distinguish absence of node entanglement from the correlations in (12.2). Correlations between records from distinct nodes are additional observations and are not covered by this blindness statement.

This is the specific tensor-factor version of the distinction emphasized by [L18, BBY18]: internal spin entanglement, link entanglement and intertwiner entanglement are different resources. It does not rule out boundary entanglement created by a subsequently specified spin-network contraction, nor identify (12.2) with a state generated by independent triangle sources.

For an increasing sequence of finite vertex sets V_j, a concrete lawful hierarchy is H_j=tensor_{a in V_j} C, K_j=D(H_j), with partial trace as q_{j+1,j}. These maps are surjective: append any fixed density matrix on the added nodes. Compactness then gives the consistent-state inverse limit of dev Section 32. Inter-node correlations reside in K_j and are lost by replacing it with merely a tuple of one-node means. This construction supplies compatible quantum states; a metric, manifold limit, geometric gluing constraints, physical time and gravitational equations still require their own definitions and proofs.

## 13. Source attribution and verification boundary for spatial completion

The quantum-tetrahedron carrier and volume convention are inherited from [B98, S13]. [AS26] is recent context for the entanglement/geometry question and uses a different principal entanglement measure. [L18, BBY18] motivate the distinction between node and boundary correlations. Complete positivity and the Choi criterion are established tools [C75]. The calculations here provide the exact HS4 disk/fiber map, entropy identity and scoped stability, the specified erasure-channel feasibility boundary, and the node-product budget. Their historical novelty has not been exhaustively investigated.

The three-copy roles remain separate: a face spin is a tensor factor of a quantum cell; an AURIC mode is a legal occupancy; an independent triangle source is a specified causal resource. No Fibonacci-to-intertwiner state-preparation functor, continuum spacetime, gravitational field equation, Bell/nonlocality certificate, or complete Renyi optimizer theorem is supplied.

Supporting code and actual finite-check output are in the companion experiments PR #11 under `docs/reports/hs4-rigidity/verify_space_completion.py` and `space_completion_result.json`. The universal parts of Sections 9-12 rest on the proofs above, not on random tests. No new Lean compilation, kernel certificate, Scribe emission, independent mathematical review or canonical admission result is asserted.

### Additional references

- [B98] A. Barbieri, *Quantum tetrahedra and simplicial spin networks*, Nuclear Physics B 518 (1998), 714-728. [arXiv:gr-qc/9707010](https://arxiv.org/abs/gr-qc/9707010). Historical source of the closure-constrained quantum tetrahedron; no novel-carrier claim is made here.
- [S13] J. Schliemann, *The Large-Volume Limit of a Quantum Tetrahedron is a Quantum Harmonic Oscillator*, [arXiv:1307.5979](https://arxiv.org/abs/1307.5979), Section 2, Eqs. (1)-(5). Only the exact closure and volume definitions are used; no large-spin approximation is applied at spin 1/2.
- [AS26] R. Amelung and H. Sahlmann, *Multipartite entanglement in the quantum tetrahedron*, Physical Review A 114 (2026), 022454. [arXiv:2601.14964](https://arxiv.org/abs/2601.14964), [DOI:10.1103/l1t8-84dk](https://doi.org/10.1103/l1t8-84dk). Publisher lists publication on 24 August 2026. The principal objective is entropic fill, distinct from F_s.
- [L18] E. R. Livine, *Intertwiner Entanglement on Spin Networks*, Physical Review D 97 (2018), 026009. [arXiv:1709.08511](https://arxiv.org/abs/1709.08511), [DOI:10.1103/PhysRevD.97.026009](https://doi.org/10.1103/PhysRevD.97.026009).
- [BBY18] B. Baytas, E. Bianchi and N. Yokomizo, *Gluing polyhedra with entanglement in loop quantum gravity*, Physical Review D 98 (2018), 026001. [arXiv:1805.05856](https://arxiv.org/abs/1805.05856), [DOI:10.1103/PhysRevD.98.026001](https://doi.org/10.1103/PhysRevD.98.026001). Its gluing construction is context, not a theorem reproduced by the cat example.
- [C75] M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra and its Applications 10 (1975), 285-290. [DOI:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0).

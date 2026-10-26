# Attenuator

## Abstract

The full bosonic attenuator and the coherent-state output-entropy question.

Corrected balanced Fock-two argument. The new analytic arguments in this narrative and the companion Entropy narrative are independently source-assessed mathematics pending formalization; the cited existing Lean declarations retain their own frozen scope and do not prove the new classification or countable entropy bridges. The parent problem is S(Phi(rho)) >= (3/2) log 2 for every density on completed Fock space, where Phi is the actual eta=1/2 channel with environment |2><2|. It remains open. More generally, Conjecture 1 of Van Herstraeten, Guha and Cerf, arXiv:2312.15623v2, Section IV, asks for coherent-state minimum output entropy for every eta and every number-state environment n, with possible additional minimizers. The rank-three result below is a restriction on the competing inputs, and the conditional determinant argument in Entropy leaves a universal premise unproved. Neither settles Conjecture 1 or the all-input partial-progress question in issue #17675. No finite input support, finite energy or finite entropy is assumed.

Physical coefficient correspondence. Write a completed-Fock vector as a=(a_k) in l2 and its Bargmann entire function as f(z)=sum_{k>=0} a_k z^k/sqrt(k!). The beamUnitary_fock convention sends f tensor |2> at eta=1/2 to F(z,w)=f((z+w)/sqrt(2)) (w-z)^2/(2 sqrt(2)). In normalized occupation coordinates, put N=i+j. Its coefficient matrix C_a has C_ij=0 for N<2 and C_ij=a_{N-2} sqrt(binomial(N,i)/2^N) ((i-j)^2-N)/sqrt(2N(N-1)) for N>=2. Indeed, expanding (w-z)^2(z+w)^{N-2}, the coefficient at z^i w^{N-i} is binomial(N-2,i)-2binomial(N-2,i-1)+binomial(N-2,i-2); division by binomial(N,i) gives ((N-2i)^2-N)/(N(N-1)), including the endpoint convention that out-of-range binomial coefficients vanish. Restoring occupation factorials gives the displayed C_ij. If I has binomial(N,1/2) law, E[((2I-N)^2-N)^2]=2N(N-1), so summing each anti-diagonal gives ||C_a||_HS^2=sum_k |a_k|^2. This is the exact completed-space isometry, not an assigned spectrum. With i retained, the pure output is C_a C_a^*, and its rank is the Schmidt or separation rank of F. The full square-root channel and its pure-input realization are the existing attenuatorOperator and pureAttenuatorOperator; their identification is also used inside PhaseCovariantAttenuatorCoherentRefutation.result.

Completed pure and density identification for the purity argument. At balance, the same orthogonal substitution turns V f into f(x)e2(y), so its isometry holds on the entire completed Fock space. A source DensityOperator is an arbitrary positive trace-class density: the sum of its full occupation diagonal is one, equivalently the positive square root has Hilbert-Schmidt norm one. The columns sqrt(rho)e_m satisfy sum_m |sqrt(rho)e_m><sqrt(rho)e_m|=rho in trace norm. Thus the source outputVector and attenuatorOperator are exactly the reduced beam-splitter map on rho tensor |2><2|, including off-diagonal and infinite-rank rho; pureOutputVector and pureAttenuatorOperator give its actual pure specialization C_a C_a^*. The completed-vector beam_displacement and partialTrace_pairDisplacement declarations, rather than only coherent_output_covariance, provide covariance for arbitrary inputs without a photon moment. The companion Entropy narrative uses this full identification for the two-copy compression, coherent equality and quantitative pure/density stability; these analytic consequences remain pending formalization.

Finite output rank forces an exponential polynomial. Rescaling the two complex variables preserves separation rank and replaces F by a nonzero scalar multiple of K(z,w)=(z-w)^2 f(z+w). For a finite-rank Hilbert-Schmidt coefficient operator, a singular-vector decomposition gives finitely many products of Bargmann entire functions; conversely a finite separation into entire factors bounds the analytic coefficient rank, which equals the operator rank when finite. Thus finite operator rank and finite analytic separation rank agree. Applying (partial_z-partial_w)^2 to K gives 8f(z+w). Differentiating a finite separated sum leaves a finite separated sum, so the ordinary Hankel kernel f(z+w) has finite rank. This operation takes place among entire functions and makes no assertion that differentiation is bounded on the Fock Hilbert space.

Let W be the span of all translates f(.+w), w in C. The finite-rank Hankel kernel puts W in a finite-dimensional space. Translation preserves W, and W is closed in the compact-open topology because it is finite dimensional. Difference quotients converge uniformly on compact sets to the derivative, so differentiation preserves W. If p is the characteristic polynomial of the linear map partial_z on W, Cayley-Hamilton gives p(partial_z)f=0. Factoring p over C and solving the constant-coefficient ODE gives f(z)=sum_alpha exp(alpha z) P_alpha(z), a finite sum with distinct alpha and nonzero polynomials P_alpha. Conversely each such function belongs to Bargmann Fock space, since polynomial growth times an exponential is square-integrable against the Gaussian, and its kernel K has finite separation rank by polynomial expansion. This proves the required entire-function statement directly. Engert, Finite dimensional translation invariant subspaces, Pacific J. Math. 32 (1970), 333-343, Theorem 1, printed p.340, DOI 10.2140/pjm.1970.32.333, treats a sigma-compact locally compact abelian group and measurable complex functions modulo almost-everywhere equality. Its group exponential-polynomial conclusion needs pointwise recovery and holomorphic specialization here. The direct ODE proof supplies precisely those analytic conditions. Primary text: https://msp.org/pjm/1970/32-2/pjm-v32-n2-p05-s.pdf. Engert also credits earlier continuous real-line work, including Anselone-Korevaar and Loewner; no priority inference is made.

Ranks add across distinct exponentials. For each alpha let m_alpha=deg P_alpha and use exp(alpha z) z^j, 0<=j<=m_alpha+2, as a basis in the first variable and the corresponding basis in the second. These exponential-polynomial spaces for different alpha are linearly independent: applying products of sufficiently high powers of partial_z-alpha isolates each summand, or equivalently uses the distinct generalized eigenspaces of differentiation. Since exp(alpha(z+w))=exp(alpha z)exp(alpha w), the finite coefficient matrix for K is block diagonal in these independent bases. Its rank is exactly the sum of the ranks of the nonzero polynomial blocks (z-w)^2 P_alpha(z+w). Lower coefficients and different exponentials therefore cannot cancel ranks between blocks.

All degrees in one polynomial block. Let P have nonzero leading coefficient and degree m, and set N=m+2. Apart from that leading coefficient, the coefficient on its top anti-diagonal z^i w^{N-i} is binomial(N,i) ((N-2i)^2-N)/(N(N-1)). At most two of the N+1 positions vanish, because the vanishing condition is quadratic in i. Choose all surviving row indices increasingly and their complementary column indices decreasingly. In the resulting square submatrix the diagonal is nonzero, and entries below it have total degree greater than N and vanish. The triangular minor is nonzero regardless of the lower coefficients of P. If m>=3 this gives rank at least N-1=m+1>=4. No exact rank formula for higher degrees is needed. For m=0 the three top anti-diagonal coefficients are nonzero and there are only three rows, so the rank is exactly three. For m=1 all four top anti-diagonal coefficients are nonzero and there are only four rows, so the rank is exactly four.

The quadratic block, including complex coefficients. Write P(z)=a0+a1 z+a2 z^2/sqrt(2), a2!=0. In the physical occupation basis the endpoint rows and columns give two nonzero pivots. Eliminating them leaves the 2 by 2 block [[-a0/sqrt(2),-a1/sqrt(8)],[-a1/sqrt(8),-a2/2]], hence rank C=2+rank of that block. It is never zero, and its determinant is a0 a2/(2 sqrt(2))-a1^2/8. Consequently it has rank one exactly when a1^2=2 sqrt(2) a0 a2, and otherwise rank two. This is precisely the zero-discriminant condition for P. Thus a quadratic double root gives rank three; a quadratic with distinct roots gives rank four. The argument is over C and does not assume real input coefficients.

Exhaustive pure-input classification. Every nonzero exponential block has rank at least three. Rank three therefore requires one exponential and a polynomial that is either constant or quadratic with a double root. For any nonzero completed-Fock pure input, rank Phi(|f><f|)=3 if and only if, up to a nonzero normalization factor, f(z)=exp(alpha z) or f(z)=exp(alpha z)(z-beta)^2. There is no nonzero pure input with output rank below three. A function outside the finite exponential-polynomial class has infinite output rank. These conclusions quantify over arbitrary completed vectors; the polynomial calculations are the consequence of finite output rank, not an imposed finite occupation cutoff.

Covariance and the shifted root. In the source Weyl convention D(gamma)f(z)=exp(-|gamma|^2/2+gamma z) f(z-conj(gamma)). Thus D(-alpha)[exp(alpha z)(z-beta)^2] is a nonzero constant times (z-(beta-conj(alpha)))^2. The invariant radial parameter after displacement is r=|beta-conj(alpha)|, not |beta|. The beam_displacement and partialTrace_pairDisplacement identities provide the completed-vector displacement transport; coherent_output_covariance is the coherent special case. For the number-state environment phase rotation is also covariant: replacing a_k by exp(ik theta)a_k changes C to exp(-2i theta) D_theta C D_theta^T, where D_theta is diagonal with entries exp(ij theta). Hence C C^* changes by unitary conjugation. This direct coefficient calculation supplies arbitrary-input phase covariance; it is not inferred from coherent_output_covariance. A phase can therefore put every noncoherent rank-three case in the form f_r(z)=(z+r)^2/sqrt(Z), r>=0, x=r^2, Z=x^2+4x+2, with Fock coefficients (x,2r,sqrt(2))/sqrt(Z). The source's unitary entropy transport is already used inside PhaseCovariantAttenuatorCoherentRefutation.result.

Compression of the actual occupation matrix. Before division by sqrt(Z), row 0 couples to rows 2,3,4 with entries x/2, sqrt(6)r/2, sqrt(3)/2, respectively. The block on rows and columns {1,2} is -(1/sqrt(2)) [[x,r],[r,1]]. Rotate its rank-one direction onto (r,1)/sqrt(x+1); its nonzero entry is -s, s=(x+1)/sqrt(2). Row 0 then couples to this direction with u=x/(2sqrt(x+1)). Its remaining coupling vector has squared norm v^2=x^3/(4(x+1))+3x/2+3/4=P/(4(x+1)), P=x^3+6x^2+9x+3; rotate that vector onto one further axis. The only nonzero compression is B/sqrt(Z), with B=[[0,u,v],[u,-s,0],[v,0,0]]. These are orthogonal changes of basis in the physical coefficient matrix. In particular det B=s v^2 is nonzero. Its three real nonzero eigenvalues mu_i are the roots of mu^3+s mu^2-T mu-s v^2=0, T=u^2+v^2=(x^2+6x+3)/4. The three nonzero physical output eigenvalues are mu_i^2/Z. The Entropy narrative derives the exact symmetric coefficients, strict entropy bound, mixed-support extension and equality cases from this compression.

Source scope and literature correspondence. The model correspondence uses BeamSplitter.beamUnitary_fock, Attenuator's square-root ensemble and pureAttenuatorOperator, and DisplacementCovariance's completed-vector identities at source revision 1ecf52f8c59f714ae936b8cea08c578355c80946 (Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679). Van Herstraeten, Guha and Cerf, https://arxiv.org/html/2312.15623v2, equation (44), gives displacement covariance for arbitrary environments; Lemma 1 requires rotation/reflection symmetry, satisfied by |2><2|, and equation (45) defines the physical Fock attenuator. Its Conjecture 1 does not supply the classification above. Lupu-Gladstein, Hertz, Heshami and Goldberg, Entanglement, loss, and quantumness: When balanced beam splitters are best, https://arxiv.org/html/2411.03423v1, Theorems 7,9,11, addresses respectively vacuum-loss purity for pure inputs, finite-support G-concurrence with an infinite-product warning, and mixed-input convex-roof entanglement with vacuum environment. Mode exchange and that mixed extension do not replace vacuum by fixed |2><2| with arbitrary competing input. Existing frozen vacuum-loss, Wigner-majorization and mixed-environment Conjecture 2 results likewise do not close the present Fock-two problem. These are checks of exact hypotheses in the cited literature and a bounded source overlap check, not an exhaustive absence or priority claim.

Three-copy realization on the full completed domain. Let H be Bargmann-Fock space with orthonormal basis e_k(z)=z^k/sqrt(k!), and write V f(z,w)=f((z+w)/sqrt(2))(w-z)^2/(2sqrt(2)). The orthogonal substitution x=(z+w)/sqrt(2), y=(w-z)/sqrt(2) preserves the Gaussian norm, and y^2/sqrt(2) has norm one. Hence V is an isometry for every a in complex l2, with no mean-photon-number assumption. Define the orthogonal antisymmetrizer P_alt=(1/6)sum_{pi in S3} sign(pi)U_pi on three retained outputs and Q=(V tensor3)^*(P_alt,A tensor I_B)(V tensor3). Then 0<=Q<=I and e3(C_a C_a^*)=<a tensor3,Q(a tensor3)>. The factor 1/6 belongs to the antisymmetrizer; there is no extra factorial in this expectation or in the increasing-triple exterior basis. The physical question is nonnegativity of Q-I/32 on actual tensor cubes a tensor3. The stronger assertion of positivity on every symmetric three-copy vector fails, as shown in Entropy.

Center and relative coordinates, without a center cutoff. For the three input variables put t=(x1+x2+x3)/sqrt(3), u=(x1-x2)/sqrt(2), v=(x1+x2-2x3)/sqrt(6), c=t/sqrt(3), and r_i=x_i-c. Then sum_i r_i=0, h2=sum_i r_i^2=u^2+v^2, and h3=r1 r2 r3=(3u^2v-v^3)/(3sqrt(6)). Apply the same orthogonal change to the environment and both output triples. The three identical splitters separate into center and relative splitters. A retained-output permutation acts identically on its center, so its conjugation cancels the center splitter. Taking the environment expectation yields Q=I_center tensor q. The transformed environment |2,2,2> still has six photons; writing it as sum_{d=0}^6 |6-d>_center tensor chi_d and tracing the center gives a positive trace-one relative density block diagonal in d. Relative photon conservation gives q=direct_sum_{M>=0}q_M. All steps use bounded unitaries and projections on completed spaces. No differentiation operator on H is used here.

The invariant relative sectors and their physical components. Simultaneous copy permutations intertwine the splitters, fix the environment and preserve P_alt; consequently q_M preserves the S3-invariant relative subspace. The fundamental theorem of symmetric polynomials with sum r_i=0 identifies its polynomial algebra as C[h2,h3], since h2=-2e2(r) and h3=e3(r). An exact basis at degree M is {h2^p h3^j:2p+3j=M}. The invariant space is one-dimensional for M=0,2,3,4,5, absent for M=1, and of dimension at most 11 for M<64. These dimensions concern the invariant subspaces, not the full relative degree-M spaces. Define F_a(t,u,v)=product_{i=1}^3 f(c+r_i) and let F_{a,M} be its orthogonal relative-degree-M projection. It is the transformed physical tensor cube, so every component is invariant and sum_M ||F_{a,M}||^2=||a||^6. Every center coefficient is retained as a vector of the entire completed center space.

Exact same-function differential polynomials. Every prime in this paragraph denotes the ordinary complex derivative in the Bargmann argument c, and every occurrence of f or a derivative is evaluated at c. Define P3=(f^2 f'''-3f f' f''+2(f')^3)/2, P4=(f^2 f''''-4f f' f'''+3f(f'')^2)/48, and P5=(f^2 f'''''-5f f' f''''+2f f'' f'''+8(f')^2 f'''-6f'(f'')^2)/48. The full projected vectors are F_{a,3}=P3(t/sqrt(3))h3, F_{a,4}=P4(t/sqrt(3))h2^2, and F_{a,5}=P5(t/sqrt(3))h2h3. They obey the entire identity f(c)P5(c)=f(c)P4'(c)-3f'(c)P4(c). If the center coefficient is differentiated in t instead, P4'(c) is sqrt(3) times d[P4(t/sqrt(3))]/dt. Thus changing derivative variables changes that coefficient.

Derivation and behavior at zeros. The power sums of r_i are p2=h2, p3=3h3, p4=h2^2/2 and p5=5h2h3/2. On any disk where f is nonzero, choose a local g=log f and expand exp(sum_i g(c+r_i)). Its relative degrees three, four and five are f^3 g''' h3/2, f^3(g''''/48+(g'')^2/8)h2^2, and f^3(g'''''/48+g''g'''/4)h2h3. Expanding the logarithmic derivatives gives exactly P3,P4,P5 above. Differentiating the expression for P4 gives P4'=3(f'/f)P4+P5. Multiplication by f yields the displayed polynomial identity. Since all final expressions are polynomial in entire derivatives, analytic continuation extends them across every zero; f identically zero is immediate. Direct differentiation of the polynomial P4 also verifies fP4'-3f'P4=fP5 without division. These formulas supply no global logarithm and require no zero-free hypothesis.

Weighted norms with exact Gaussian and factorial normalization. Define ||P||_3^2=(3/pi)integral_C |P(c)|^2 exp(-3|c|^2)d^2c. The change t=sqrt(3)c gives ||P(t/sqrt(3))||_center^2=||P||_3^2, and ||c^k||_3^2=k!/3^k. Orthogonality of Bargmann monomials gives ||h3||^2=2!/6+3!/54=4/9; ||h2^2||^2=4!+4(2!2!)+4!=64; and, since h2h3=(u^4v+(2/3)u^2v^3-v^5/3)/sqrt(6), ||h2h3||^2=4+8/9+20/9=64/9. It follows that ||F_{a,3}||^2=(4/9)||P3||_3^2, ||F_{a,4}||^2=64||P4||_3^2 and ||F_{a,5}||^2=(64/9)||P5||_3^2. The center Gaussian is part of every norm; evaluating only at center vacuum would change the assertion.

Why the projected identities and weighted integrability hold for every complex l2 input. Cauchy-Schwarz gives |f(z)|<=||a||exp(|z|^2/2), hence f is entire. The three-mode orthogonal coordinate change is unitary on completed Fock space and maps a tensor3 to F_a, of squared norm ||a||^6. For truncations a_L, their tensor cubes converge in Hilbert norm, while the corresponding f_L and every fixed derivative converge uniformly on compact disks by reproducing estimates and Cauchy's formula. The projected polynomial identities hold for f_L. Orthogonal projection is bounded; projected Hilbert convergence and continuous center evaluation therefore identify the limiting coefficients with Pj(f)(t/sqrt(3)). The degree-three, four and five invariant spaces are exactly the one-dimensional lines already identified, so these are the whole projected vectors. Their norms are finite because they are bounded projections of F_a. This proves the weighted integrability of the displayed derivative combinations without assuming that differentiation is bounded on H or that the individual derivatives belong to H. Infinite support, arbitrary phases, unbounded mean photon number, and the full center coordinate remain in scope.

Evidence and literature boundary for this package. The same-function identities, relative-sector estimates and physical perturbation arguments here and in Entropy are independently source-assessed analytic mathematics pending formalization. The analytic evidence includes independent source assessment of the pinned owner definitions and their model correspondence; source reading is not kernel verification. No successful Pro source audit of those owners is part of this evidence. Further literature checks preserve exact settings: arXiv:1301.5229, Section III and equations (11)-(14), has a vacuum second input; arXiv:2411.03423v1, Lemma 6 and Theorem 7, uses two vacuum environment modes in its two-copy overlap mechanism. Neither supplies this three-copy two-photon estimate. The coherent-transform convex-functional theorem in arXiv:2210.14798, Theorem 1, does not identify its phase-space integral with 2p3-3s p2+(13/16)s^3. No such missing bridge is assumed. These bounded checks make no worldwide novelty or priority claim.

The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.

**Definition 1.1 (ProbabilityVector).**

$$\begin{aligned}\forall p : ProbabilityVector, (\operatorname{weight}\left(p\right):\mathbb{N} \to \mathbb{R})\\\forall p : ProbabilityVector, (\forall n : \mathbb{N}, (0 \le \operatorname{weight}\left(p, n\right)))\\\forall p : ProbabilityVector, (\operatorname{HasSum}\left(\operatorname{weight}\left(p\right), 1\right))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.ProbabilityVector` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The structure has precisely the data field weight: Nat -> Real and proof fields nonneg and normalized displayed as separate rows above; its support is unrestricted.

**Definition 1.2 (DensityOperator).**

$$\begin{aligned}\forall rho : DensityOperator, (\operatorname{operator}\left(rho\right):\operatorname{ContinuousLinearMap}\left(\mathbb{C}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right))\\\forall rho : DensityOperator, (\operatorname{IsPositive}\left(\operatorname{operator}\left(rho\right)\right))\\\forall rho : DensityOperator, (\operatorname{HasSum}\left((n:\mathbb{N})\mapsto(\operatorname{Re}\left(\operatorname{inner}\left(\mathbb{C}, \operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right), \operatorname{operator}\left(rho\right)\left(\operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right)\right)\right)\right)), 1\right))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.DensityOperator` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The structure has precisely the data field operator and proof fields positive and trace_one displayed as separate rows above. For a positive bounded operator, finite full-basis diagonal sum characterizes trace class. No Fock-diagonality assumption is made on inputs.

**Definition 1.3 (outputVector).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall rho : DensityOperator, (\forall q : \operatorname{Prod}\left(\mathbb{N}, \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right), (\operatorname{outputVector}\left(eta, hEta, p, rho, q\right) = \operatorname{smul}\left(\operatorname{ComplexofReal}\left(\operatorname{sqrt}\left(\operatorname{weight}\left(p, \operatorname{fst}\left(q\right)\right)\right)\right), \operatorname{beamSplitter}\left(eta, hEta, \operatorname{tensor}\left(\operatorname{CFCsqrt}\left(\operatorname{operator}\left(rho\right)\right)\left(\operatorname{lpsingle}\left(2, \operatorname{fst}\left(\operatorname{snd}\left(q\right)\right), \operatorname{ComplexofReal}\left(1\right)\right)\right), \operatorname{lpsingle}\left(2, \operatorname{fst}\left(q\right), \operatorname{ComplexofReal}\left(1\right)\right)\right)\right)\left(\operatorname{snd}\left(\operatorname{snd}\left(q\right)\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.outputVector` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

q=(n,m,l) indexes the environment number n, the square-root column m of the input, and the discarded-mode slice l. This is the square-root Kraus realization of Tr_2[U_eta(rho tensor sum_n p_n|n><n|)U_eta^dagger], including off-diagonal inputs.

**Definition 1.4 (attenuatorOperator).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall rho : DensityOperator, (\operatorname{attenuatorOperator}\left(eta, hEta, p, rho\right) = \operatorname{mixture}\left(\operatorname{Prod}\left(\mathbb{N}, \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right), (q:\operatorname{Prod}\left(\mathbb{N}, \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right))\mapsto(\operatorname{outputVector}\left(eta, hEta, p, rho, q\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.attenuatorOperator` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.5 (attenuator).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall rho : DensityOperator, (\operatorname{operator}\left(\operatorname{attenuator}\left(eta, hEta, p, rho\right)\right) = \operatorname{attenuatorOperator}\left(eta, hEta, p, rho\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.attenuator` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The state constructor has this operator field. Summability, positivity and trace one of the full triple-index ensemble are checked in Lean.

**Definition 1.6 (pureDensity).**

$$\forall v : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\forall hv : \left\lVert v \right\rVert = 1, (\operatorname{operator}\left(\operatorname{pureDensity}\left(v, hv\right)\right) = \operatorname{rankOne}\left(\mathbb{C}, v, v\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureDensity` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The normalized vector gives its existing Mathlib rank-one projector as the operator field; positivity and trace-one proofs complete the density structure.

**Definition 1.7 (pureOutputVector).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall v : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\forall q : \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right), (\operatorname{pureOutputVector}\left(eta, hEta, p, v, q\right) = \operatorname{smul}\left(\operatorname{ComplexofReal}\left(\operatorname{sqrt}\left(\operatorname{weight}\left(p, \operatorname{fst}\left(q\right)\right)\right)\right), \operatorname{beamSplitter}\left(eta, hEta, \operatorname{tensor}\left(v, \operatorname{lpsingle}\left(2, \operatorname{fst}\left(q\right), \operatorname{ComplexofReal}\left(1\right)\right)\right)\right)\left(\operatorname{snd}\left(q\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureOutputVector` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.8 (pureAttenuatorOperator).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall v : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\operatorname{pureAttenuatorOperator}\left(eta, hEta, p, v\right) = \operatorname{mixture}\left(\operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right), (q:\operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right))\mapsto(\operatorname{pureOutputVector}\left(eta, hEta, p, v, q\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureAttenuatorOperator` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The pure-input ensemble agrees with the full square-root attenuator. The environment expansion sums p_n times the partial trace of U_eta(v tensor |n>).

**Theorem 1.9 (coherent_output_covariance).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall alpha : \mathbb{C}, (\operatorname{pureAttenuatorOperator}\left(eta, hEta, p, \operatorname{displacement}\left(alpha, \operatorname{lpsingle}\left(2, 0, \operatorname{ComplexofReal}\left(1\right)\right)\right)\right) = \operatorname{conjStarAlgEquiv}\left(\operatorname{displacement}\left((\operatorname{ComplexofReal}\left(\operatorname{sqrt}\left(eta\right)\right)) \cdot (alpha)\right), \operatorname{pureAttenuatorOperator}\left(eta, hEta, p, \operatorname{lpsingle}\left(2, 0, \operatorname{ComplexofReal}\left(1\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.coherent_output_covariance` (`✓ std3`). ∎

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

For every countably supported phase-invariant environment, every coherent input has a displaced vacuum output. The assertion concerns the full operator, including its coherences.

**Definition 1.10 (coherentDensity).**

$$\forall alpha : \mathbb{C}, (\operatorname{operator}\left(\operatorname{coherentDensity}\left(alpha\right)\right) = \operatorname{rankOne}\left(\mathbb{C}, \operatorname{coherent}\left(alpha\right), \operatorname{coherent}\left(alpha\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.coherentDensity` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.11 (fockDensity).**

$$\forall n : \mathbb{N}, (\operatorname{operator}\left(\operatorname{fockDensity}\left(n\right)\right) = \operatorname{rankOne}\left(\mathbb{C}, \operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right), \operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.fockDensity` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.DensityOperator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.ProbabilityVector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.attenuator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.attenuatorOperator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.coherentDensity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.coherent_output_covariance`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.fockDensity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.outputVector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureAttenuatorOperator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureDensity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureOutputVector`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance](DisplacementCovariance.md)

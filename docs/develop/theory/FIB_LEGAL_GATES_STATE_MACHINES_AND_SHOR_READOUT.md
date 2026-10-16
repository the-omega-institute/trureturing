# FIB legal gates, reversible state machines and Shor-type readout

## 1. Independent scope and existing owners

This is an independent algorithmic continuation of the existing gate and observation theories. It does not depend on the HS4 maximum, singlet cells, spatial interpretation or many-body Hamiltonians. It distinguishes an ordinary mathematical construction, a compiled reversible circuit, a hardware experiment and a complexity advantage. The mathematical constructions below use explicit ideal control and observation hypotheses.

The following sources supply distinct mathematical interfaces:

| Existing owner | Object consumed here | Retained boundary |
| --- | --- | --- |
| [Legal interference](FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md), Chapter 8, especially Definitions 8.3 and 8.16 | The no11 Hilbert space, explicit conditional pulses, ordered gate words and full output records | A legal pulse and its phase are supplied controls; the occupancy grammar alone supplies neither |
| [Output-resolved instrument closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md), Section 15 with its editorial conditions | Actual branch maps and dependence of future observations on retained records | Classical recorded histories and unmeasured coherent work registers are different carriers |
| [Fusion-chain QCA](FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md), Sections 1.1-1.3 and 8.1-8.2 | Actual window algebras, their embeddings and the restricted finite-depth gate menu | A finite register permutation is not automatically a local implementation on an infinite fusion chain |
| `D5/S1/Recurrence/LucasCompanion.lean` | `matrixPeriod`, `companion_zpow_eq_one_iff`, `matrixPeriod_pos`, `companion_power_shape` | These are algebraic period declarations; these algebraic declarations do not themselves specify a quantum circuit |

Shor [S97] and Kitaev [K95] supply the established order-finding and eigenphase-estimation framework. The integration below specifies the phase information, reversible work space and power-access hypotheses needed to apply that framework to these project objects. It does not claim a new factoring algorithm or a solution of arbitrary state-machine prediction.

## 2. The gate-state-machine interface must retain amplitude phases

Let S be a finite nonempty set with orthonormal basis {|s>}. A deterministic map f:S->S has a same-register unitary realization U|s>=|f(s)> exactly when f is bijective. Necessity follows by preservation of inner products; sufficiency follows because a permutation of an orthonormal basis is unitary.

For a general finite map f:S->T, reversibility can instead retain a residual label:

$$V|s\rangle=|f(s)\rangle|g_s\rangle.$$

Within each fiber of f the normalized residual vectors must be pairwise orthogonal. Thus their Hilbert space needs dimension at least max_t |f^{-1}(t)|. This is attained by numbering each fiber in a common residual basis. It constructs an isometry, extendible to a unitary after choosing sufficiently large padded registers. An efficient numbering algorithm, padding rule and reset procedure are further requirements. Keeping the original input as work is another standard construction, whose interference cost is examined in Section 6.

### Proposition 2.1. Legal full-flip pulses are phase-decorated permutations

Use the Chapter 8 space K_n=span{|s>:s in B_n}, where B_n consists of length-n bit strings with no consecutive ones. Let tau_i flip bit i exactly when both existing neighbors are zero, and otherwise fix the word. Then tau_i is an involution of B_n. The actual pulse R_i(beta,pi/2) from that chapter obeys

$$R_i(\beta,\pi/2)|s\rangle=
\begin{cases}
-i e^{i\beta}|\tau_i(s)\rangle,&s_i=0\text{ and enabled},\\
-i e^{-i\beta}|\tau_i(s)\rangle,&s_i=1\text{ and enabled},\\
|s\rangle,&\text{blocked}.
\end{cases} \tag{2.1}$$

A finite ordered word of these pulses therefore has the form

$$U|s\rangle=e^{i\gamma_s}|\tau(s)\rangle,\qquad \tau\in\operatorname{Sym}(B_n). \tag{2.2}$$

Proof. Enabled insertion and deletion preserve legality and reverse each other without changing the neighbors. Formula (2.1) is the supplier's explicit two-state exponential at angle pi/2. Multiplying its monomial matrices composes the permutations and adds the phases along the actual traversed path. QED.

The pair (tau,gamma) is the required coherent transition description. For two gates U_1,U_2, the composite phase is gamma_1(s)+gamma_2(tau_1(s)). Retaining only the transition table tau loses this information. General pulse angles yield superpositions of words and need not admit (2.2); the results specific to monomial gates below do not apply to those angles automatically.

### Theorem 2.2. Classical orbit length and quantum return phase

Let s_k=tau^k(s_0) be a cycle of length r, and put

$$\Gamma_k=\sum_{h=0}^{k-1}\gamma_{s_h},\qquad
\Phi_C=\Gamma_r\pmod{2\pi}.$$

On the cycle span U^r=e^{i Phi_C}I. Its r eigenphases are

$$\theta_j=\frac{\Phi_C+2\pi j}{r}\pmod{2\pi},\qquad j=0,\ldots,r-1, \tag{2.3}$$

with an orthonormal eigenbasis

$$|\chi_j\rangle=\frac1{\sqrt r}\sum_{k=0}^{r-1}
 e^{i\Gamma_k-ik\theta_j}|s_k\rangle.$$

Proof. Substitute (2.2), shift the index and use r theta_j=Phi_C modulo 2pi for the wraparound term. Orthogonality is finite Fourier orthogonality. Changing |s> to e^{i b_s}|s> changes gamma_s to gamma_s+b_s-b_{tau(s)}, whose sum on a cycle is unchanged. All phases can be removed by such a diagonal basis change exactly when every cycle has Phi_C=0 modulo 2pi: choose b successively along each cycle; the last edge is consistent exactly under that condition. QED.

These cycle phases belong to gate amplitudes, not to the pure-state edge-phase gradients of the supplier's Proposition 8.9. The latter telescope around their graph cycle. A gate cycle can have a nontrivial return phase even though its classical permutation returns.

### Proposition 2.3. The actual three-position gate word

Take U=R_3(0,pi/2) R_2(0,pi/2) R_1(0,pi/2), with the rightmost factor first. Its permutation cycles are

$$000\leftrightarrow101,\qquad001\longrightarrow100\longrightarrow010\longrightarrow001.$$

Each input undergoes exactly two enabled flips in one sweep, so U=-P_tau on all five legal words. On the three-cycle, U^3=-I and the literal operator order is six although the classical and ray-return periods are three. Its phases modulo one are 1/6,1/2,5/6. With a six-dimensional Fourier clock the output peaks are 1,3,5, each with probability 1/3. The phase-free permutation has peaks 0,2,4 instead.

Thus phase estimation of U is working correctly; interpreting its denominators as the classical orbit period without accounting for the phase would be incorrect. Here the known global minus sign can be compensated by a phase on the control register. A general gate word can have different cycle phases, so one global correction need not suffice.

## 3. A paired-register construction that cancels monomial phases

### Theorem 3.1. Exact intertwining without knowledge of the individual phases

For a monomial U as in (2.2), assume a supplied implementation of its entrywise conjugate bar U in the specified word basis. Define D|s>=|s>|s>, an isometry into two registers. Then

$$\boxed{(U\otimes\overline U)D=D P_\tau.} \tag{3.1}$$

Consequently (U^k tensor bar U^k)D=D P_tau^k for every nonnegative integer k. The cycle length measured on this diagonal code is exactly the classical cycle length, with no return-phase offset.

Proof. The two factors on |s,s> contribute e^{i gamma_s} and e^{-i gamma_s}, which cancel, leaving |tau(s),tau(s)>. Linear extension proves the isometry identity and its preservation of coherence for arbitrary code inputs, including reference-entangled inputs. Induction gives the powers. QED.

D is basis copying: it sends sum_s a_s|s> to sum_s a_s|s,s>. This is generally entangled and differs from copying an unknown quantum state into two product copies. It can be obtained from a known computational encoding and a blank register; those register operations are additional to the original single-position pulse menu.

For the supplied pulses, entrywise conjugation has an explicit formula:

$$\overline{R_i(\beta,t)}=R_i(-\beta,-t). \tag{3.2}$$

It follows by conjugating the Hamiltonian and exponential. A known gate word therefore supplies a mathematical conjugate word. This is not an oracle for conjugating an arbitrary unknown unitary. Nor does (3.1) hold for arbitrary nonmonomial gates: for the Hadamard matrix H, (H tensor H)|00>=|++>, which is outside span{|00>,|11>}.

Constructing controlled paired powers still requires the control and power resources described in Section 5. Equation (3.1) cancels amplitude phases; it does not make exponentially long gate words cheap.

## 4. The precise Fourier observation and what it can distinguish

### Theorem 4.1. Recorded clock effects for an arbitrary unitary

Given a unitary U with fixed phase convention, a clock size Q, controlled U^a for a=0,...,Q-1, and an inverse Q-point Fourier transform, define

$$B_y=\frac1Q\sum_{a=0}^{Q-1}e^{-2\pi iay/Q}U^a,\qquad E_y=B_y^\dagger B_y.$$

On any target density matrix rho the clock probabilities are

$$\Pr_\rho(y)=\operatorname{Tr}(\rho E_y),\qquad \sum_y E_y=I. \tag{4.1}$$

If U=sum_lambda lambda Pi_lambda, then

$$\Pr_\rho(y)=\sum_\lambda\operatorname{Tr}(\rho\Pi_\lambda)
\left|\frac1Q\sum_{a=0}^{Q-1}\lambda^a e^{-2\pi iay/Q}\right|^2. \tag{4.2}$$

Proof. Prepare the uniform clock, apply the controlled powers, and expand its inverse Fourier amplitudes. Summing B_y^dagger B_y uses sum_y exp(2pi i(a-b)y/Q)=Q delta_ab. Spectral projectors eliminate cross terms in B_y^dagger B_y. This proves both the probability formula and normalization. QED.

An arbitrary coherent target thus gives a mixture of spectral weights in this readout. The clock alone does not recover coherences between eigenvectors, all internal states, or every recorded future of a gate system. For U with U^Q=I, the E_y are its exact character projectors. A permutation-cycle basis state has weight 1/r on every cycle eigenphase; there is no need to prepare a uniform superposition over an unknown cycle beforehand.

The original legal-edge quadrature measurements, sequential instrument records and these clock effects are different observations. A joint protocol may use all of them, but sufficiency must be proved for that actual menu rather than inferred from the word "Fourier".

### Proposition 4.2. Denominators from ideal spectral samples

For a phase-free r-cycle, an ideal spectral outcome j/r is uniform over j=0,...,r-1. Its reduced denominator is r/gcd(j,r). For k independent such samples,

$$\Pr\left(\operatorname{lcm}(d_1,\ldots,d_k)=r\right)
=\prod_{p\mid r}(1-p^{-k}). \tag{4.3}$$

Proof. The least common multiple misses a prime's full exponent exactly when all numerators are divisible by that prime. Independent uniform residues, and then the Chinese remainder theorem over the distinct prime divisors of r, give the product. The empty product for r=1 is one. QED.

This identity concerns ideal eigenphase labels. An implemented finite binary clock yields approximations with the distribution (4.2). For a supplied bound r<=R and Q=2^m>=2R^2, a nearest clock outcome is within circular error 1/(2Q)<1/(2r^2), so continued fractions recover the reduced j/r, with the usual treatment of the 0/1 wraparound. The nearest-outcome probability for each eigenphase is at least 4/pi^2: the geometric sum in (4.2), |sin(pi Q delta)|>=2Q|delta| for |Q delta|<=1/2, and |sin(pi delta)|<=pi|delta| prove the bound. Other outcomes remain possible. Classical candidate validation and repeated samples are not omitted.

If only P_tau^d s=s has been verified, d is a returning exponent, possibly a multiple of the true period. A primitive certificate consists of a complete prime factorization of d together with nonreturn at d/p for every distinct prime divisor p. This certifies minimality because the true period divides d. Obtaining that factorization has a computational cost; it is not a free byproduct of measuring the clock.

## 5. Control, phase reference and large powers are part of the specification

The same-channel equality Ad_U=Ad_{e^{i phi}U} does not identify controlled U and controlled e^{i phi}U. Their relative control phase is measurable. In particular U=I and -I are the same standalone channel, while their controlled versions act differently on a |+> control. A transition kernel or an unlabelled CPTP channel therefore does not by itself specify the phase-referenced oracle required by (4.1).

The black-box control obstruction of [AFCB14] applies to its stated oracle model, not to every physical implementation. Tang-Wright [TW26], revised April 2026, further shows that many phase-invariant tasks admit efficient decontrolling with phase-averaged output and suitable forward/inverse access. The lesson here is to specify the task and access model. We do not claim every period-related task fundamentally needs direct controlled access, nor claim to have implemented their decontrolling construction. Our explicit protocol supplies controlled gates or requires a separately proved compilation of them.

For an m-bit clock, the usual circuit uses controlled U^(2^j), j=0,...,m-1. If these are produced merely by repeating a one-step gate, the number of calls is 2^m-1. This accounting does not exclude specialized fast implementations; it shows that a diagram of a controlled high power is not evidence of one. A generic finite gate menu or QCA does not automatically provide a polynomial-cost large-power oracle.

If implemented controlled powers have operator-norm errors epsilon_j and the inverse Fourier transform has error epsilon_F, then the final output total-variation distance from the ideal protocol is at most min(1,epsilon_F+sum_j epsilon_j). Expand the difference of the two unitary products as a telescoping sum, use norm preservation of each factor, and then pure-state trace-distance and measurement contraction. Purifying a mixed input gives the same bound. This is an error budget once concrete compiled gates are supplied, not a gate-synthesis or fault-tolerance result.

## 6. Retained histories can destroy the intended interference

### Theorem 6.1. Exact work-register condition for a clean period function

Consider the normalized state

$$|\Psi\rangle=\frac1{\sqrt Q}\sum_{a=0}^{Q-1}|a\rangle|f(a)\rangle|g_a\rangle,$$

where f(a) are orthogonal computational labels and g_a are normalized work states. Tracing out the last two registers gives clock entries

$$\rho_C(a,b)=\frac1Q\mathbf1_{f(a)=f(b)}\langle g_b|g_a\rangle. \tag{6.1}$$

It equals the clean computation's clock matrix exactly if and only if g_a=g_b whenever f(a)=f(b), in the specified phase convention.

Proof. Partial trace gives (6.1). For each equal-output pair the clean entry is 1/Q, so equality requires inner product one. Normalized vectors have inner product one exactly when their squared difference norm is zero. The converse is immediate. QED.

Keeping g_a=|a> destroys every off-diagonal clock entry, giving I/Q and a uniform Fourier output even when f is perfectly periodic. A residual state depending only on f(a) causes no additional suppression. Merely proportional work states can still introduce relative phases, already covered by (6.1). Compute-copy-uncompute is the standard remedy when its reversible circuit is supplied.

This refines the project's recorded-output distinction. A classical experimental label may need to be retained for inference; a quantum work register that distinguishes paths meant to interfere may need to be uncomputed before readout. Keeping all histories or deleting all histories is not a universal rule. The reduced state and the intended probability law decide which operation is valid.

## 7. Fibonacci/Lucas arithmetic supplies a separate fast-power target

Fix N>=2 and units Q_0 modulo N. Write

$$A_{P,Q_0}=\begin{pmatrix}P&-Q_0\\1&0\end{pmatrix},\qquad
T_{P,Q_0}(x,y)=(Px-Q_0y,x)\pmod N.$$

Its determinant Q_0 is a unit, so this is a permutation of (Z/NZ)^2 and hence defines a permutation unitary on the corresponding register. The companion convention agrees with `LucasCompanion.lean`. Only finite-ring instances are used here; an arbitrary real companion matrix is not directly declared unitary.

### Theorem 7.1. One faithful probe determines the whole matrix order

Put v=(1,0)^T. For every nonnegative k,

$$\boxed{A_{P,Q_0}^k v=v\quad\Longleftrightarrow\quad A_{P,Q_0}^k=I.} \tag{7.1}$$

Proof. The two columns v and Av=(P,1)^T have determinant one and form a basis over Z/NZ, including composite moduli. If A^k fixes v, commutation with A makes it fix Av too, hence every vector. The reverse implication is immediate. QED.

The orbit length r equals the existing algebraic `matrixPeriod` and satisfies r<=N^2-1, because the nonzero vector v stays in a nonzero permutation orbit. For P=1,Q_0=-1 this is the Fibonacci update (x+y,x), with A^k v=(F_{k+1},F_k) modulo N. Its return period is exactly the Pisano period, without requiring that every state have the same orbit length. A single occurrence of F_k=0 is insufficient; the adjacent coordinate must also return to one.

### 7.2. An explicit clean large-power architecture

Let n=ceil(log_2 N). Encode each residue in n bits and extend a matrix permutation by the identity when either register is an invalid residue. Compute M_j=A^(2^j) modulo N by repeated squaring. M_j and M_j^{-1} have descriptions of O(n) bits because their matrix size is fixed. Reversible modular arithmetic can implement the extended bijection f_j and its inverse.

The clean in-place construction uses a blank second pair of residue registers: compute f_j(x) into it, swap the two pair registers, and XOR the reversible computation of f_j^{-1} into the old-input register to return that register to zero. Arithmetic scratch must be uncomputed in both computations. This realizes |x>|0> -> |f_j(x)>|0>, not an oracle leaving hidden x-dependent work. A control is added to the specified reversible elementary circuit. The padding rule is preserved on the full bit-string domain.

For r<=N^2-1, a binary clock with Q>=2(N^2-1)^2 uses O(log N) clock bits. Repeated squaring and classical modular arithmetic have polynomial bit complexity; standard reversible compilation gives a polynomial-size circuit family for this arithmetic target, followed by the established phase-estimation and classical postprocessing framework [S97,K95,IBM]. This is an architectural application of known algorithms. A primitive gate list, gate count and physical error correction are additional implementation requirements. By contrast, no such fast-power construction is supplied here for an arbitrary no11 sweep or fusion-chain QCA.

The Fibonacci matrix also satisfies q(A(x,y))=-q(x,y) for q=x^2-xy-y^2, so its square preserves a hyperbolic quadratic form over the reals. This real-coordinate identity and the finite permutation unitary concern different representations. Neither determines the other carrier's Hilbert norm, physical dimension or quantum speed advantage.

## 8. What transfers to fusion gates and what remains distinct

For a finite fusion window with its specified algebra, any chosen legal unitary gate word has the spectral readout (4.1) if a representation, clock coupling and controlled powers are supplied. One must retain fusion-charge blocks and multiplicity spaces required by that algebra. A finite-dimensional unitary need not have finite order, so phase estimation does not automatically yield an integer period. An infinite-chain QCA further needs an actual finite-register boundary rule before this clock circuit is defined.

The QCA volume distinguishes an abstract compatible automorphism from a finite-depth circuit in the allowed local algebra. This continuation does not bypass that distinction. It also does not infer a compilation of Fibonacci modular arithmetic into Fibonacci-anyon gates merely from their common Fibonacci name. The legal occupancy grammar, the fusion category and the modular recurrence are three explicitly different carriers.

The common interface now has precise content: state encoding; allowed gate and work-register specification; monomial phase or general unitary spectrum; power implementation; clock effects; classical validation; and resource/error accounting. Every claimed transfer must supply those maps. This lets gate/state-machine research develop independently of any HS4 or many-body interpretation.

## 9. Remaining mathematical interfaces

The remaining implementation obligations are a primitive reversible arithmetic circuit with cleaned scratch and explicit costs; controlled-pulse or decontrolled-task compilation in the declared hardware model; finite-clock extraction with a complete validation policy. No arbitrary-QCA fast-forwarding, optimal resource theorem, new factoring speedup, WSS exclusion, original HS4 proof or universal state tomography is claimed.

### Primary references and ownership

- [S97] P. W. Shor, *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer*, SIAM Journal on Computing 26 (1997), 1484-1509. [arXiv:quant-ph/9508027](https://arxiv.org/abs/quant-ph/9508027), DOI 10.1137/S0097539795293172. Established reversible arithmetic, Fourier period finding and classical factoring reduction.
- [K95] A. Yu. Kitaev, *Quantum measurements and the Abelian Stabilizer Problem*, [arXiv:quant-ph/9511026](https://arxiv.org/abs/quant-ph/9511026). Established eigenvalue measurement and Abelian-action formulation.
- [AFCB14] M. Araujo, A. Feix, F. Costa and C. Brukner, *Quantum circuits cannot control unknown operations*, New Journal of Physics 16 (2014), 093026. [arXiv:1309.7976](https://arxiv.org/abs/1309.7976), DOI 10.1088/1367-2630/16/9/093026. The oracle-model distinction between an unknown channel and phase-referenced coherent control.
- [TW26] E. Tang and J. Wright, *Are controlled unitaries helpful?*, [arXiv:2508.00055v2](https://arxiv.org/abs/2508.00055v2), revised 23 April 2026. Phase-averaged decontrolling for the paper's access/task model. Cited to delimit the no-go inference, not as an implementation performed here.
- [IBM] IBM Quantum Learning, *Phase-estimation and factoring*, especially *Shor's algorithm*, [course](https://quantum.cloud.ibm.com/learning/en/courses/fundamentals-of-quantum-algorithms/phase-estimation-and-factoring/shor-algorithm) and [implementation tutorial](https://quantum.cloud.ibm.com/docs/en/tutorials/shors-algorithm). Explicit power-access, clock-precision and classical-reconstruction explanation.

Monomial spectral decomposition, tensor-conjugate cancellation, finite Fourier orthogonality and reversible computation are established mathematical tools. The work here supplies their concrete gate-word correspondence, phase-offset counterexample, clean-work criterion and modular companion interface. Their historical novelty has not been established.

## 10. Continuation: controllable states, observable states and circuit costs

The native pulse supplier’s Definition 8.3 specifies independently addressed single-position pulses with arbitrary phase and angle. Sections 10–15 use those ideal projected generators. A scalable modular-arithmetic compiler and physical error model are separate hypotheses.

Let d=|B_n|=F_{n+2} for n>=1, X_i=H_i(0), Y_i=H_i(pi/2), and P_s=|s><s| on K_n. Both X_i and Y_i are traceless Hermitian matrices. The site-i edges form a matching; on each oriented edge their matrices are the usual Pauli X and Y, and on blocked words they vanish. Pulse angles are real and inverses are available. Negative angles can also be replaced modulo 2pi for these generators. The following controllability assertions do not bound duration, pulse count or precision.

The external combinatorial input is Numata-Yamanouchi [NY22], Theorem 3.7: the toggles of independent sets of the open path generate the entire symmetric group on those independent sets. Its vertices 1,...,n and independent-set indicator strings map literally to our B_n and tau_i. It is a theorem about permutations, not a theorem about their phases or quantum control. The added lifting argument appears below.

## 11. A phase restriction has an exact blind sector; one extra quadrature removes it

### Proposition 11.1. The phase-zero obstruction

Define W|s>=i^{|s|}|s>, where |s| is the number of occupied sites, and Z_par|s>=(-1)^{|s|}|s>. With only pulses exp(-it X_i), their conjugates W^dagger U W are real orthogonal matrices of determinant one. Equivalently, the antiunitary A=Z_par times coordinate conjugation commutes with every allowed U. The ray quantity |psi^T Z_par psi| is invariant.

Consequently every finite adaptive protocol consisting of these pulses, word-basis projective measurements and hypothesis-independent classical choices gives identical complete-record probabilities on rho and A rho A^{-1}. In particular the orthogonal states

$$|\psi_\pm\rangle=\frac{|0^n\rangle\pm|10^{n-1}\rangle}{\sqrt2} \tag{11.1}$$

cannot be distinguished by that entire menu. A single pulse R_1(pi/2,pi/4) followed by word measurement distinguishes them perfectly.

Proof. An enabled edge changes |s| by one, so W^dagger(-i X_i)W is real antisymmetric. Exponentiation proves the orthogonal statement. The identity Z_par X_i Z_par=-X_i, together with conjugation of i, gives A U A^{-1}=U and U^T Z_par U=Z_par. Word projectors also commute with A. Every fixed branch Kraus product therefore intertwines A, and its nonnegative probability on the two conjugate hypotheses is equal. The same conditional policy weights preserve equality for adaptive complete histories; summing records preserves it too. A exchanges the two vectors in (11.1). On their enabled two-dimensional block exp(-i pi Y/4) sends psi_+ to the occupied word and psi_- to the empty word. QED.

This result is stronger than failure of one selected experiment. It describes a whole allowed control-and-readout class. It excludes coherent clock couplings or phase gates absent from that class. Full-flip monomial gates followed only by word measurement have the still smaller diagonal observable space of dimension d.

### Theorem 11.2. Any one site with a second quadrature gives full finite control

Fix any j in {1,...,n}. The real dynamical Lie algebra is

$$\boxed{\operatorname{Lie}_{\mathbb R}\{-iX_1,\ldots,-iX_n,-iY_j\}=\mathfrak{su}(d).} \tag{11.2}$$

Thus arbitrary finite products with real pulse angles generate SU(d). All pure states in K_n are mutually reachable up to a phase; a mixed state's spectrum is preserved by these unitary controls. The theorem uses independently addressable X_i at every site and the additional Y quadrature at one site. Global, translation-invariant control alone does not satisfy these hypotheses.

Proof. Denote the Lie algebra by l. The commutator of -iX_j and -iY_j supplies iD for a nonconstant traceless real diagonal D: its diagonal entries on each enabled pair are opposite and nonzero. For every full-flip word G, Ad_G l=l, since its factors are exponentials of generators of l. By Section 2 each such G is monomial, and its conjugation on diagonal matrices is the underlying permutation. By [NY22], these permutations cover Sym(B_n); the pulse phases cancel in diagonal conjugation.

It follows that l contains i pi(D) for every permutation pi. Choose two unequal entries of D. For any distinct a,b, permute those entries to a,b and subtract the conjugate under the transposition (ab). This gives a nonzero real multiple of i(P_a-P_b). Hence l contains every traceless imaginary diagonal matrix.

Take any enabled pair (u,v) in X_j. Commuting i(P_u-P_v) with -iX_j isolates a nonzero multiple of |u><v|-|v><u|, because the support of X_j is a matching and every other matched pair is disjoint from u,v. A second bracket with i(P_u-P_v) yields i(|u><v|+|v><u|). Conjugating these two matrices by the available monomial words moves the pair to any ordered pair (a,b). Any accompanying phase merely rotates this two-dimensional real span. Therefore l contains both off-diagonal generators for every pair, as well as every traceless imaginary diagonal. These form a basis of su(d). All original generators are traceless skew-Hermitian, giving the reverse inclusion.

The final reachability assertion uses the standard finite-dimensional driftless Lie-group controllability theorem [AD01, D03]: the connected subgroup generated by the supplied one-parameter subgroups has this Lie algebra. Since its Lie algebra is all su(d), it is an open subgroup of the connected group SU(d), hence equals SU(d). This external control principle is distinct from the explicitly proved Lie-algebra calculation. QED.

This proof can be reused for a finite family of matching-supported flips whenever their underlying permutations generate the full symmetric group and one matching has both quadratures. The open-path conclusion uses an existing nontrivial combinatorial theorem rather than guessing full controllability from connectedness alone. With all phases fixed to zero, Proposition 11.1 prevents full su(d); within these stated menus the extra quadrature is an actual resource.

## 12. Exact observation consequences, with a generic complexity boundary

### Corollary 12.1. Full controlled observations separate every density matrix

With the controls of Theorem 11.2 and final word measurement,

$$\mathcal W=\operatorname{span}_{\mathbb R}\{U^\dagger P_sU:U\text{ reachable},\ s\in B_n\}
=\operatorname{Herm}(d). \tag{12.1}$$

For any two density matrices rho,sigma,

$$\sup_U\operatorname{TV}\bigl((\operatorname{Tr}\rho U^\dagger P_sU)_s,
(\operatorname{Tr}\sigma U^\dagger P_sU)_s\bigr)
=\frac12\|\rho-\sigma\|_1. \tag{12.2}$$

Proof. SU(d) acts transitively on unit vectors, so the effects include all rank-one projectors. Their real span is Herm(d): projectors on (|a>+|b>)/sqrt(2) and (|a>+i|b>)/sqrt(2), together with P_a, extract both off-diagonal quadratures. For (12.2), choose a reachable U that diagonalizes rho-sigma; multiplying a diagonalizing unitary by a global phase adjusts its determinant without changing the measurement. The output absolute differences sum to the sum of absolute eigenvalues. The reverse inequality is trace-norm contraction under measurement, or trace duality for the signed sum of these orthogonal effects. QED.

This is informational completeness across a family of settings, not exact tomography from one specimen. The optimal U in (12.2) depends on the two specified hypotheses. Unitary evolution preserves trace distance; control exposes its existing distinguishability to the chosen measurement. In contrast, the clock alone for a single fixed U in Section 4 depends only on spectral weights and remains blind to coherences between its eigenvectors.

For an affine-linear predictive representation that must reproduce all these probabilities for all initial density matrices, the traceless state coordinates must have rank at least d^2-1. Otherwise a nonzero traceless Hermitian kernel vector A gives valid states I/d plus or minus epsilon A, for sufficiently small epsilon, with the same representation but different output probabilities by (12.1). A representation including normalization needs d^2 real linear coordinates. This statement concerns linear state representations, not unrestricted nonlinear encodings or a claimed classical simulation lower bound in time.

### Proposition 12.2. Full controllability does not imply short synthesis

For the finite generator menu in Theorem 11.2, almost every U in SU(d) requires at least d^2-1 one-parameter pulses for exact synthesis. With arbitrary independently chosen phase and angle on each pulse, the analogous generic lower bound is ceil((d^2-1)/2). For a fixed pure input the corresponding generic bounds are 2d-2 and d-1 pulses, respectively.

Proof. A fixed word of L generator labels defines a smooth map from R^L to SU(d), whose dimension is d^2-1. For L<d^2-1 its image has Haar measure zero by the smooth dimension/Sard theorem. There are finitely many label words at any fixed length, and countably many bounded parameter charts, so their union remains null. Two continuous parameters per pulse replace L by 2L. Apply the same argument to the orbit in complex projective space of dimension 2d-2 for pure-state preparation. QED.

These are generic exact-synthesis statements, not worst-case approximation bounds or lower bounds for a particular structured circuit. Since d is Fibonacci-sized, a generic unitary on all legal states can require exponentially many pulses. A structured algorithm can use a small computational subspace and a structured gate list. The next section supplies such a compilation interface.

## 13. A clean encoded circuit compiler inside the existing legal pulse model

For m>=1 set n=2m-1 and define the isometry

$$J_m|b_1\cdots b_m\rangle=|b_1\,0\,b_2\,0\cdots0\,b_m\rangle. \tag{13.1}$$

Odd sites carry data; the m-1 even sites are separators initialized to zero. Every encoded word is legal. During an entangling pulse a separator may be excited, but no11 legality is maintained and the separator is restored at the gate boundary. This is an explicit map from ordinary qubit registers into the no11 carrier. It makes no identification with Fibonacci fusion-category gates.

Write R_x(t)=exp(-itX), R_y(t)=exp(-itY). On the encoded space, R_{2q-1}(0,t) and R_{2q-1}(pi/2,t) implement those single-qubit rotations at data bit q, because both neighboring separators are zero. Euler decomposition implements any one-qubit SU(2) gate with at most three such pulses.

### Theorem 13.1. Five-pulse CZ and nine-pulse nearest-neighbor CNOT

The separator pulse D_q=R_{2q}(0,pi) satisfies

$$D_qJ_m=J_m\,\operatorname{diag}(-1,1,1,1)_{q,q+1}. \tag{13.2}$$

Let S_q=R_{2q+1}(0,pi/2)R_{2q-1}(0,pi/2). Then

$$S_q^\dagger D_q S_qJ_m=J_m\operatorname{CZ}_{q,q+1}. \tag{13.3}$$

Define h_q=R_{2q-1}(0,pi/2)R_{2q-1}(pi/2,pi/4). Its encoded action is -i times the Hadamard gate. For either orientation of adjacent data bits c,t,

$$h_t(S_q^\dagger D_q S_q)h_t^\dagger J_m
=J_m\operatorname{CNOT}_{c\to t},\qquad q=\min(c,t). \tag{13.4}$$

The pulse counts in (13.3) and (13.4) are five and nine, respectively, counting inverses separately.

Proof. If the adjacent data bits are 00, the separator is an enabled two-state block and exp(-i pi X)=-I on it. It returns to zero with phase minus one. If either data bit is one, the separator is blocked and the pulse is the identity. This gives (13.2), including exact restoration of the work bit. On code states S_q acts as -X_q X_{q+1}, so conjugation moves the minus sign from 00 to 11; its global minus sign cancels with its adjoint. This gives (13.3). Direct Pauli multiplication gives R_x(pi/2)R_y(pi/4)=-i H. The two opposite phases of h_t and h_t^dagger cancel, and H_t CZ H_t=CNOT. Every identity is an equality on the entire encoded Hilbert space, and thus also holds with an arbitrary external reference system. QED.

For a CNOT between data bits a,b at distance delta=|a-b|, move the control next to the target with delta-1 adjacent SWAPs, apply the adjacent CNOT, then undo the SWAPs. Each SWAP uses three adjacent CNOTs. Thus one such gate needs at most 6(delta-1)+1 adjacent CNOTs, or 9[6(delta-1)+1] native pulses. No layout information is discarded.

### Corollary 13.2. Circuit-level intertwining and an explicit overhead

Given a known m-qubit circuit C with G_1 one-qubit SU(2) gates and CNOT pairs at distances delta_1,...,delta_{G_2}, the construction yields a finite native word V_C with

$$\boxed{V_CJ_m=J_mC,\qquad
L\le3G_1+9\sum_{e=1}^{G_2}[6(\delta_e-1)+1].} \tag{13.5}$$

For general U(2) single-qubit gates, the same statement has an explicitly tracked input-independent phase e^{i theta_C}. The clock and arithmetic work qubits of a known algorithm are included among the m data bits. In particular, a supplied ordinary Shor/phase-estimation circuit can be compiled with linear space overhead and at most linear-in-m pulse overhead per source two-qubit gate.

Proof. The elementary identities return the separators to zero, so they compose by induction without entangling the final data with residual separator records. SWAP routing restores the original order. Removing the determinant phase of each single-qubit U(2) gate produces only a tracked global phase on the full m-qubit register. The gate universality of one-qubit gates and CNOT is established [B95]; (13.2)-(13.5) supply their present native realization. QED.

This compilation translates a known circuit including its controlled operations. It does not attach a new control to an unknown compiled black box, so the phase-reference issue in Section 5 is retained. It also does not itself produce cheap large powers for a generic state machine. Section 7's modular-arithmetic structure still supplies that separate ingredient. The blocker-controlled phase mechanism has established neutral-atom gate precedent [J00]; the present theorem is a precise ideal-model encoding and pulse-count construction, without a novelty or experimental-fidelity claim.

## 14. The five-qubit modulus-two clock circuit

The circuit has three binary clock qubits and two target qubits. Its target permutation is the actual modulus-two Fibonacci map

$$(x,y)\longmapsto(x+y,x)\pmod2,$$

implemented by CNOT_{2->1} followed by CNOT_{1->2}. Clock-controlled powers 1,2,4 are expanded into Toffoli circuits, then an inverse eight-point Fourier transform is applied to the clock. This finite circuit uses repeated powers and proves no fast-forwarding result. All five qubits are encoded on nine native sites, whose complete legal Hilbert space has dimension 89.

For initial clock 000 and target 10, the ideal clock law is obtained directly from

$$p(y)=\frac1{64}\sum_{r=0}^{2}\left|\sum_{0\le a<8,\ a\equiv r\ (3)}e^{-2\pi iay/8}\right|^2. \tag{14.1}$$

The eight-point clock has finite precision; a single outcome does not certify the integer period. Equation (14.1) is an ideal probability law.

## 15. Consequences for state machines

The all-n Lie-algebra argument uses the published open-path toggle-group theorem [NY22], followed by the explicit diagonal-orbit and matching-edge commutators of Theorem 11.2. It does not infer Lie rank from a few tested values. The native compiler and its register-cleaning claims use the exact gate identities of Section 13. The general control/observability and universal-gate principles remain attributed to their existing sources.

The state-machine consequence is precise: gates act on amplitudes and coherences, and their composition changes which effects can be measured. In the native ideal model, a single extra local phase quadrature removes an exact symmetry obstruction, while a clean separator encoding compiles known quantum circuits with explicit overhead. Computational advantage still requires an efficient task-specific circuit, meaningful output statistics, state preparation and error control. Full controllability, state identifiability and computational speed are separate properties.

### Additional primary sources

- [NY22] Y. Numata and Y. Yamanouchi, *On the action of the toggle group of the Dynkin diagram of type A*, Algebraic Combinatorics 5 (2022), 149-161, Theorem 3.7, printed p.155. [arXiv:2103.16217](https://arxiv.org/abs/2103.16217), [DOI:10.5802/alco.204](https://doi.org/10.5802/alco.204). Its complete open-path toggle group is the only nontrivial external combinatorial input to Theorem 11.2. The source also credits earlier automaton-theoretic work; no toggle-group priority is claimed here.
- [AD01] F. Albertini and D. D'Alessandro, *Notions of controllability for quantum mechanical systems*, [arXiv:quant-ph/0106128](https://arxiv.org/abs/quant-ph/0106128). Established finite-dimensional operator/state controllability distinction and Lie criteria.
- [D03] D. D'Alessandro, *On Quantum State Observability and Measurement*, Journal of Physics A 36 (2003), 9721, [arXiv:quant-ph/0307127](https://arxiv.org/abs/quant-ph/0307127), [DOI:10.1088/0305-4470/36/37/310](https://doi.org/10.1088/0305-4470/36/37/310). Sections 1-2 distinguish controlled evolution, state-equivalence classes and the observation space. The present full-space identification follows directly from Theorem 11.2 and the projector argument above.
- [B95] A. Barenco et al., *Elementary gates for quantum computation*, Physical Review A 52 (1995), 3457. [arXiv:quant-ph/9503016](https://arxiv.org/abs/quant-ph/9503016), [DOI:10.1103/PhysRevA.52.3457](https://doi.org/10.1103/PhysRevA.52.3457). Established one-qubit/CNOT universality and finite circuit decomposition. Generic dimension-counting barriers retain their standard ownership.
- [J00] D. Jaksch et al., *Fast Quantum Gates for Neutral Atoms*, Physical Review Letters 85 (2000), 2208-2211. [arXiv:quant-ph/0004038](https://arxiv.org/abs/quant-ph/0004038), [DOI:10.1103/PhysRevLett.85.2208](https://doi.org/10.1103/PhysRevLett.85.2208). Historical context for blockade-mediated conditional phases; its physical level scheme and error analysis are not asserted to be implemented by the ideal occupancy compiler.

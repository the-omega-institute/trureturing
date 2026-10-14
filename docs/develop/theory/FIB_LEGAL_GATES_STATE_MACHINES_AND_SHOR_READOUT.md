# FIB legal gates, reversible state machines and Shor-type readout

## 1. Independent scope and existing owners

This is an independent algorithmic continuation of the existing gate and observation theories. It does not depend on the HS4 maximum, singlet cells, spatial interpretation or many-body Hamiltonians. It distinguishes an ordinary mathematical construction, a compiled reversible circuit, a hardware experiment and a complexity advantage. Only the first, with supporting finite checks, is supplied here. No new Lean theorem or historical-priority claim is made.

The base read for this continuation is dev `5d0de9dcddea52e5f7b5329c25f960dc098fd5c9`. The following actual sources supply different interfaces:

| Existing owner | Object consumed here | Retained boundary |
| --- | --- | --- |
| [Legal interference](FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md), Chapter 8, especially Definitions 8.3 and 8.16 | The no11 Hilbert space, explicit conditional pulses, ordered gate words and full output records | A legal pulse and its phase are supplied controls; the occupancy grammar alone supplies neither |
| [Output-resolved instrument closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md), Section 15 with its editorial conditions | Actual branch maps and dependence of future observations on retained records | Classical recorded histories and unmeasured coherent work registers are different carriers |
| [Fusion-chain QCA](FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md), Sections 1.1-1.3 and 8.1-8.2 | Actual window algebras, their embeddings and the restricted finite-depth gate menu | A finite register permutation is not automatically a local implementation on an infinite fusion chain |
| `D5/S1/Recurrence/LucasCompanion.lean` | `matrixPeriod`, `companion_zpow_eq_one_iff`, `matrixPeriod_pos`, `companion_power_shape` | These are algebraic period declarations; this continuation does not recompile them or claim they contain a quantum circuit |

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

### Example 2.3. The actual three-position gate word

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

For r<=N^2-1, a binary clock with Q>=2(N^2-1)^2 uses O(log N) clock bits. Repeated squaring and classical modular arithmetic have polynomial bit complexity; standard reversible compilation gives a polynomial-size circuit family for this arithmetic target, followed by the established phase-estimation and classical postprocessing framework [S97,K95,IBM]. This is an architectural application of known algorithms. No primitive gate list, gate count, error-corrected realization or comparative speedup has been compiled in this delivery. By contrast, no such fast-power construction is supplied here for an arbitrary no11 sweep or fusion-chain QCA.

The Fibonacci matrix also satisfies q(A(x,y))=-q(x,y) for q=x^2-xy-y^2, so its square preserves a hyperbolic quadratic form over the reals. This real-coordinate identity and the finite permutation unitary concern different representations. Neither determines the other carrier's Hilbert norm, physical dimension or quantum speed advantage.

## 8. What transfers to fusion gates and what remains distinct

For a finite fusion window with its specified algebra, any chosen legal unitary gate word has the spectral readout (4.1) if a representation, clock coupling and controlled powers are supplied. One must retain fusion-charge blocks and multiplicity spaces required by that algebra. A finite-dimensional unitary need not have finite order, so phase estimation does not automatically yield an integer period. An infinite-chain QCA further needs an actual finite-register boundary rule before this clock circuit is defined.

The QCA volume distinguishes an abstract compatible automorphism from a finite-depth circuit in the allowed local algebra. This continuation does not bypass that distinction. It also does not infer a compilation of Fibonacci modular arithmetic into Fibonacci-anyon gates merely from their common Fibonacci name. The legal occupancy grammar, the fusion category and the modular recurrence are three explicitly different carriers.

The common interface now has precise content: state encoding; allowed gate and work-register specification; monomial phase or general unitary spectrum; power implementation; clock effects; classical validation; and resource/error accounting. Every claimed transfer must supply those maps. This lets gate/state-machine research develop independently of any HS4 or many-body interpretation.

## 9. Supporting checks and remaining obligations

The independent checker `docs/reports/gate-shor-integration/verify_gate_shor.py` in the experiments repository checks legal sweeps for n=1,...,8, cycle return phases and paired cancellation, the actual five-word sign-offset example, clock probabilities, which-path erasure of interference, and Fibonacci return/power identities for moduli 2,...,128. It also checks the ideal two-sample denominator formula for r=1,...,40. These are bounded exact and floating checks; the all-input and all-length claims rest on the proofs above. No quantum processor or Lean compilation is involved.

The remaining implementation obligations are a primitive reversible arithmetic circuit with cleaned scratch and explicit costs; controlled-pulse or decontrolled-task compilation in the declared hardware model; finite-clock extraction with a complete validation policy; and corresponding admissible Lean/Scribe formalization. No arbitrary-QCA fast-forwarding, optimal resource theorem, new factoring speedup, WSS exclusion, original HS4 proof or universal state tomography is claimed.

### Primary references and ownership

- [S97] P. W. Shor, *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer*, SIAM Journal on Computing 26 (1997), 1484-1509. [arXiv:quant-ph/9508027](https://arxiv.org/abs/quant-ph/9508027), DOI 10.1137/S0097539795293172. Established reversible arithmetic, Fourier period finding and classical factoring reduction.
- [K95] A. Yu. Kitaev, *Quantum measurements and the Abelian Stabilizer Problem*, [arXiv:quant-ph/9511026](https://arxiv.org/abs/quant-ph/9511026). Established eigenvalue measurement and Abelian-action formulation.
- [AFCB14] M. Araujo, A. Feix, F. Costa and C. Brukner, *Quantum circuits cannot control unknown operations*, New Journal of Physics 16 (2014), 093026. [arXiv:1309.7976](https://arxiv.org/abs/1309.7976), DOI 10.1088/1367-2630/16/9/093026. The oracle-model distinction between an unknown channel and phase-referenced coherent control.
- [TW26] E. Tang and J. Wright, *Are controlled unitaries helpful?*, [arXiv:2508.00055v2](https://arxiv.org/abs/2508.00055v2), revised 23 April 2026. Phase-averaged decontrolling for the paper's access/task model. Cited to delimit the no-go inference, not as an implementation performed here.
- [IBM] IBM Quantum Learning, *Phase-estimation and factoring*, especially *Shor's algorithm*, [course](https://quantum.cloud.ibm.com/learning/en/courses/fundamentals-of-quantum-algorithms/phase-estimation-and-factoring/shor-algorithm) and [implementation tutorial](https://quantum.cloud.ibm.com/docs/en/tutorials/shors-algorithm), consulted 14 October 2026. Explicit power-access, clock-precision and classical-reconstruction explanation. No tutorial hardware result or library-version claim is transferred to these checks.

Monomial spectral decomposition, tensor-conjugate cancellation, finite Fourier orthogonality and reversible computation are established mathematical tools. The work here supplies their concrete gate-word correspondence, phase-offset counterexample, clean-work criterion and modular companion interface. Their historical novelty has not been established.

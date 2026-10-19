# FIB legal gates: one phase address, efficient routing and certified readout

## 1. Scope and source interfaces

This is a result-specific continuation of [FIB legal gates and Shor readout](FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md), Sections 11-15. It keeps that source unchanged and remains independent of HS4 and its many-body model.

The [four-corner coherence and single-copy certification volume](AURIC_FIB_ATOM_FOUR_CORNER_COHERENCE_AND_SINGLE_COPY_CERTIFICATION.md), C-117 and C-121, supplies the precise witness and conditional source assumptions consumed below. C-121.1 explicitly assumes an actual three-outcome PVM. Section 4 supplies its effects from the native gates; it does not change the original conditional separability or setting-independence assumptions.

The native generator is the existing ideal open-path operator H_i(beta)=P_(i-1)(cos(beta) X_i+sin(beta) Y_i)P_(i+1), with missing endpoint projectors equal to I, and R_i(beta,t)=exp(-it H_i(beta)). Let J_m embed m ordinary qubits into 2m-1 sites by inserting a zero between consecutive data bits. Site numbers are one-based in the formulas.

The retained control contract is independently addressed phase-zero pulses at every site, real pulse angles, and a second quadrature at exactly one chosen data site 2q_*-1. Other data and separator sites have no second quadrature. Pulse angles, ordering, computational-word initialization, and final complete-word measurement are supplied. This is not global-only control, a finite-blockade approximation, or a noise-calibration claim.

Reduced-address quantum control is established research. Cesa-Pichler [CP23] construct universal Rydberg computation with species-selective global drives in a different dual-species geometry. Their result is stronger concerning removal of local addressing but has different space and architecture costs. Here we retain local X addressing and solve the explicit compilation problem left between the preceding one-reference controllability theorem and its all-sites-phase compiler. Controlled-Pauli identities and circuit routing are established algebraic tools; the new integration is their native pulse realization and quantitative connection to the current AURIC measurement contract.

## 2. Zero-phase gates can route an arbitrary encoded quantum state

Write R_x(t)=exp(-itX), R_y(t)=exp(-itY) on an encoded data qubit. Let C_Z(a,b) denote the five-pulse adjacent CZ from the preceding Theorem 13.1. Every pulse in that construction has beta=0, and every separator returns to zero at the gate boundary. Define on adjacent data qubits

$$C_Y(c,t)=R_{x,t}(-\pi/4)\,C_Z(c,t)\,R_{x,t}(\pi/4). \tag{2.1}$$

### Theorem 2.1. Clean seven-pulse CY and twenty-one-pulse SWAP

The native implementation of (2.1) restricts exactly to

$$C_Y=|0\rangle\langle0|_c\otimes I_t+|1\rangle\langle1|_c\otimes Y_t.$$

Moreover,

$$\boxed{C_Y(a,b)C_Y(b,a)C_Y(a,b)=\operatorname{SWAP}_{a,b}.} \tag{2.2}$$

Both native gates use only beta=0. They cost at most seven and twenty-one native pulses, respectively, and preserve the entire encoded space with all separators reset. The equalities hold for arbitrary encoded inputs, including inputs entangled with external systems.

Proof. The identity R_x(-pi/4) Z R_x(pi/4)=Y proves (2.1), using the exact native CZ intertwiner. In (2.2), direct action on the four basis states fixes 00 and 11 and exchanges 01 and 10. The factors i and -i from controlled Y cancel, so no residual computational-state-dependent phase remains. Linearity gives the operator identity. Composing native intertwiners gives the all-input and clean-separator assertions. The costs are 1+5+1 and three times that number. QED.

On three physical sites, the full native SWAP acts as minus one on the extra legal state 010. It need not be the identity outside the four-dimensional code. This extra phase is compatible with the phase-zero antiunitary restriction and is retained in Section 4's full five-state effect calculation.

## 3. A constructive polynomial compiler with one second-quadrature address

For a data location q, let W_(q->q_*) be an ordered product of adjacent SWAPs moving that data state to q_*, at cost at most 21|q-q_*|. Other data states move coherently; they are not measured, copied into product states, or discarded. Applying the inverse route restores their original locations.

### Theorem 3.1. Remote rotations and circuit cost

One can implement

$$\boxed{W_{q\to q_*}^{\dagger}R_{y,q_*}(t)W_{q\to q_*}=R_{y,q}(t)} \tag{3.1}$$

with at most 42|q-q_*|+1 pulses and exactly one second-quadrature call, always at native site 2q_*-1. A CZ between data sites a,b costs at most 42(|a-b|-1)+5 pulses, all phase zero, by routing one endpoint next to the other and restoring it.

For a known circuit C written using R_x, R_y and CZ, with G_x R_x gates, Y-rotation locations q_l and CZ pairs (a_e,b_e), there is an explicitly generated native word V_C with

$$V_CJ_m=J_m C,$$
$$\boxed{L\le G_x+\sum_l[42|q_l-q_*|+1]+\sum_e[42(|a_e-b_e|-1)+5].} \tag{3.2}$$

Thus compilation has O(mG) native-pulse overhead for a G-gate source circuit, linear native-site overhead, and one fixed second-quadrature address. The pulse-list generation has polynomial classical cost. Dense matrix validation is a separate exponential-size calculation and is not part of the compiler's claimed efficiency.

Proof. SWAP conjugates every single-qubit operator on the moved factor to the reference factor. Equation (3.1) and its count follow from Theorem 2.1. For CZ, route over |a-b|-1 neighboring pairs, use the five-pulse adjacent gate, and reverse the route. The resulting intertwiners restore every separator and layout, so induction over the circuit gives (3.2). Euler decomposition gives arbitrary one-qubit SU(2) gates using X-Y-X rotations. CNOT follows by Hadamard conjugation of CZ. General U(2) gates have an explicitly tracked input-independent phase. Known controlled gates must first be decomposed in this source basis; this does not add coherent control to an unknown black box. QED.

The preceding SU(d) result acts on the entire d=F_(n+2) legal space. The efficient compiler here instead acts on the specified 2^m-dimensional code. It does not claim efficient synthesis of a generic unitary on the whole legal space, nor cheap high powers for arbitrary state machines.

### Corollary 3.2. One is necessary and sufficient for this fixed encoding and action task

With computational-word initialization and no additional state or operation breaking the original parity-conjugation symmetry, zero second-quadrature addresses cannot implement every complex qubit unitary under J_m. One data address suffices with the bound (3.2).

Proof. The parent Proposition 11.1 gives the antiunitary A=Z_par K commuting with every phase-zero pulse. The input |0^(2m-1)> is fixed by A. Every reachable ray from it is therefore A-invariant. The encoded target |+> on one data qubit and zeros elsewhere is sent by A to the orthogonal encoded |-> state, so it is unreachable even up to global phase. A compiler realizing all standard complex qubit actions must implement this preparation and hence cannot use the zero-address menu. Sufficiency is Theorem 3.1. QED.

The minimality is only for this fixed complex encoding, initialization and all-input action task. It is not a statement that real-amplitude computing lacks quantum computational power. Real-amplitude simulations with altered encodings are established [RG02]; extra coherent reference states or a different encoding change the resource contract. No minimal-pulse, optimal-time or all-hardware actuator theorem is claimed.

### 3.3. Finite order-probe application

The three-clock-bit, two-target-bit modulus-two companion circuit in the parent Section 14 is a known five-qubit circuit. Theorem 3.1 therefore gives an exact native implementation on nine sites with a single chosen second-quadrature data address. Its all-input intertwiner retains the complete clock distribution (14.1); this finite-clock law alone does not certify an integer period.

## 4. Native implementation of the four-corner measurement effects

Use the five legal three-site states. The encoded bottom space is the image of J_2; let P_b=J_2J_2^dagger and let a=|010> be the apex. The C-117/C-121 operators are exactly

$$K_1=J_2(X\otimes Z)J_2^\dagger,\qquad K_2=J_2(Z\otimes X)J_2^\dagger,$$
$$E_{j,\pm}=(P_b\pm K_j)/2,\qquad E_{j,0}=I_5-P_b. \tag{4.1}$$

The bottom word dictionary is 00->000, 10->100, 01->001, 11->101. No tensor-product decomposition of the whole five-dimensional space is assumed.

Let h_1 be the parent's two-pulse implementation of -i times Hadamard on the first data qubit, with identity action on the apex. Let S be the native twenty-one-pulse data SWAP. Define

$$V_1=h_1^\dagger C_Z,\qquad V_2=V_1 S. \tag{4.2}$$

Here only native site one has the second quadrature. After V_j, measure the complete legal word. Record 0 for apex 010; on the bottom record + or - according to whether the first data bit is zero or one. Keep the setting label j.

### Theorem 4.1. Exact five-state measurement effects with one phase address

This native experiment implements the three effects in (4.1) on every five-state density matrix, including bottom-apex coherences. Setting 1 uses seven pulses; setting 2 uses twenty-eight. Each uses exactly one second-quadrature pulse at site one. Uniform random settings cost 35/2 pulses per round on average, excluding preparation and final readout.

Proof. On the bottom, the diagonal output observable is Z tensor I. Pulling it back by V_1 gives CZ (X tensor I) CZ=X tensor Z. S conjugates this operator to Z tensor X, proving setting 2. Every constituent preserves bottom and apex at its boundary. Native CZ and S act by -1 on the apex, while h_1 fixes it, so V_1 and V_2 act there by -1 and +1. Therefore both preserve the apex projector exactly and have no bottom-apex blocks. Pulling back the bottom outcome projectors gives (4.1) as full five-by-five identities. The pulse counts are 5+2 and 21+5+2. QED.

Only the effects and their outcome probabilities have been equated. The implemented complete-word measurement refines the degenerate +/- eigenspaces. Its postmeasurement channel is not asserted to equal a minimally disturbing Lueder instrument for the coarse PVM. For sequential sources, the conditional-null assumptions must refer to the history actually retained by the experiment, including any retained refined outcomes. No future source independence is inferred from these effect identities.

This closes the ideal native-realization premise singled out in C-121.1. Trusted apparatus calibration, source assumptions, sample complexity and physical leakage are separate. The witness remains incomplete: failure to violate its separable bound does not prove that the state is separable.

## 5. From gate error to a time-uniform false-positive bound

For round n, condition on the full retained past F_(n-1). The current state is selected before the independent uniform setting J_n in {1,2}. Under the null, its conditional bottom state is separable whenever its bottom probability is nonzero, exactly as in C-121.1. Let the actual three-outcome distribution at setting j differ from the ideal one in total variation by at most epsilon_(n,j), uniformly over the current state. The two error bounds are known from the past or a prespecified calibration contract. Put bar epsilon_n=(epsilon_(n,1)+epsilon_(n,2))/2.

Use the inherited score V_n=1,-3,0 on +,-,0. No failed or outside-bottom round is discarded. For leakage outside the ideal carrier, an implementation may use a flagged zero-score outcome, but its probability must be included in the stated total-variation comparison.

### Theorem 5.1. Calibrated imperfect measurements admit a valid anytime test

Choose a predictable 0<=lambda_n<1/(3+4 bar epsilon_n), and define

$$Z_n=V_n-4\bar\epsilon_n,\qquad
M_0=1,\quad M_N=\prod_{n=1}^N(1+\lambda_n Z_n).$$

Then, under the conditional null,

$$\boxed{\Pr(\exists N\ge1:M_N\ge1/\alpha)\le\alpha,\qquad0<\alpha<1.} \tag{5.1}$$

No independence of different preparations is required. The error contract and conditional separability cannot be replaced by an assertion only about unconditional average states.

Proof. An observable score in [-3,1] changes its expectation by at most four times the total-variation change. This follows by subtracting its minimum and using the signed mass's positive and negative variations. Averaging the two settings gives E[V_n|F_(n-1)]<=4 bar epsilon_n because the ideal expectation is Tr rho_n(K_1+K_2-P_b)<=0 under the supplied separability premise. Hence E[Z_n|F_(n-1)]<=0. The chosen lambda makes every multiplier nonnegative, so M_N is a nonnegative supermartingale. Stopping at the first crossing and an arbitrary finite horizon gives P(crossing by horizon)<=alpha; increasing the horizon proves (5.1). This is the standard Ville/supermartingale method [HRMS20] with the explicit native measurement error correction above. QED.

The factor four is sharp given only the three-outcome total-variation contract: the null boundary distribution (3/4,1/4,0) has mean zero; moving epsilon mass from minus to plus gives mean 4epsilon. Without a correction, even a valid small measurement error can give positive null drift. This sharp distributional example is not claimed to identify the worst calibrated physical gate error.

### Corollary 5.2. Explicit per-pulse calibration and detectable signal

If every actual pulse differs in operator norm by at most delta from its ideal unitary on a common full physical carrier, telescoping and measurement contraction give epsilon_1<=min(1,7delta) and epsilon_2<=min(1,28delta). Any preparation or detector error must be included separately. Consequently bar epsilon<=min(1,35delta/2).

For the fixed calibrated family C-120.1 with bottom weight r and real coherence gamma, the ideal score mean is r gamma. Its corrected mean is at least

$$\mu=r\gamma-4\bar\epsilon.$$

In particular delta<r gamma/70 is a sufficient, conservative gate-error condition for a positive corrected mean when the pulse errors are the only implementation errors. Delta here is a unitary operator-norm error, not average gate infidelity, and this inequality is not a fault-tolerance threshold or a measured hardware specification.

For completeness, suppose constant error bounds and an alternative source/implementation guarantee E[Z_n|F_(n-1)]>=mu>0 at every round. Set B=3+4 bar epsilon and lambda=mu/(2B^2). For tau the first crossing of 1/alpha,

$$\boxed{\mathbb E\tau\le\frac{4B^2}{\mu^2}\,[\log(1/\alpha)+\log(1+\lambda)].} \tag{5.2}$$

Indeed |lambda Z_n|<=1/2 and log(1+x)>=x-x^2 on that interval, so the conditional log-growth is at least mu^2/(4B^2). The stopped log process is pathwise at most log(1/alpha)+log(1+lambda). Summing conditional drifts up to tau wedge N bounds E[tau wedge N]; monotone convergence proves (5.2) and finite stopping. Because each fresh setting is uniform given the past, Tonelli and conditioning give expected total native pulse count (35/2)E tau. This cost bound concerns the stated positive-drift alternative and excludes preparation/readout overhead.

The sequential witness tests conditional separability of the supplied source, not an arbitrary fixed initial marginal of a correlated stream. C-116's common-label example retains its full force. The new native implementation and calibration correction do not certify source independence.

## 6. Remaining bounds and source attribution

The chapter settles a precisely specified efficient one-phase-address compilation task and supplies a native realization of the specified four-corner measurement effects, with a conditional calibrated error guarantee. These are model-specific quantum control and certification results. No named universal quantum-information conjecture is declared solved. The established ingredients remain standard circuit algebra, routing, antiunitary invariance, trace-distance contraction and nonnegative-supermartingale theory.

The next genuinely unfinished targets are tighter or optimal native routing costs, a primitive large-modulus arithmetic compiler with resource counts, finite-blockade and drift-derived calibration bounds, and explicit implementation-error models. Efficient generic state tomography, arbitrary-state-machine fast forwarding and quantum fault tolerance are not obtained from this construction.

### Primary references and exact roles

- [CP23] F. Cesa and H. Pichler, *Universal Quantum Computation in Globally Driven Rydberg Atom Arrays*, Physical Review Letters 131 (2023), 170601, DOI 10.1103/PhysRevLett.131.170601, arXiv:2305.19220. Established reduced-address/global-drive universality in a different dual-species architecture. No identical control contract or comparative resource superiority is asserted.
- [RG02] T. Rudolph and L. Grover, *A 2 rebit gate universal for quantum computing*, arXiv:quant-ph/0210187 (2002). Establishes the distinction between real-amplitude computational universality and implementing arbitrary unitaries on an unchanged complex encoding. Its encoding is not implemented by this chapter.
- [HRMS20] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via nonnegative supermartingales*, Probability Surveys 17 (2020), 257-317, arXiv:1808.03204. Standard Ville/supermartingale tool, already attributed by dev C-121. The score correction, actual PVM compiler and pulse-to-statistics correspondence are derived here.
- [WMBW26] G. Warttmann, F. Meinert, H. P. Buechler and S. Weber, *Suppressing crosstalk for Rydberg quantum gates*, Quantum 10 (2026), 2045, DOI 10.22331/q-2026-03-24-2045. Current primary context that local addressing errors require explicit physical treatment. Its pulse scheme or error rates are not assumed in the operator-norm contract above.

# Finite Propagation Histories

## Abstract

Finite unitary histories and their relation to word spaces, records and calibrated evolution.

**Theorem 1.1 (Reconstruction from clock zero).**

$$\forall H: \operatorname{ComplexInnerProductSpace}\left(\right), \forall U: \operatorname{UnitarySequence}\left(H\right), \forall T: Nat, \forall x: \operatorname{ClockHistory}\left(H, T\right), \operatorname{propagation}\left(U, T, x\right) = 0 \iff x = \operatorname{trajectory}\left(U, T, \operatorname{component}\left(x, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FinitePropagationHistory.propagation_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dorit Aharonov; Wim van Dam; Julia Kempe; Zeph Landau; Seth Lloyd; Oded Regev (2004). *Adiabatic Quantum Computation is Equivalent to Standard Quantum Computation*. URL: <https://arxiv.org/abs/quant-ph/0405098>.

*Acknowledgement.* Alvaro Arias; Gelu Popescu (1994). *Factorization and Reflexivity on Fock spaces*. URL: <https://arxiv.org/abs/math/9404209>.

*Acknowledgement.* Vittorio Giovannetti; Seth Lloyd; Lorenzo Maccone (2015). *Quantum Time*. DOI: [10.1103/PhysRevD.92.045033](https://doi.org/10.1103/PhysRevD.92.045033). URL: <https://arxiv.org/abs/1504.04215>.

*Commentary.*

Let H be a complex inner product space, let T be a natural number, and let U(k) be a sequence of complex linear isometric equivalences of H. The clock space is the Hilbert direct sum of T+1 copies of H. Define E(0)=I and E(k+1)=U(k)E(k). The trajectory map sends a vector to the components E(k) applied to that vector. The propagation map D has components x(k+1)-U(k)x(k), for k<T. Induction on the clock position reconstructs a trajectory in the kernel from x(0). Conversely each reconstructed trajectory satisfies all the adjacent equations. An arbitrary finite sequence of T unitaries is included by extending it with identities after T; these later values are never used.

**Theorem 1.2 (Normalized trajectories fill the propagation kernel).**

$$\forall H: \operatorname{ComplexInnerProductSpace}\left(\right), \forall U: \operatorname{UnitarySequence}\left(H\right), \forall T: Nat, \operatorname{range}\left(\operatorname{historyEmbedding}\left(U, T\right)\right) = \operatorname{ker}\left(\operatorname{propagation}\left(U, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FinitePropagationHistory.history_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dorit Aharonov; Wim van Dam; Julia Kempe; Zeph Landau; Seth Lloyd; Oded Regev (2004). *Adiabatic Quantum Computation is Equivalent to Standard Quantum Computation*. URL: <https://arxiv.org/abs/quant-ph/0405098>.

*Acknowledgement.* Alvaro Arias; Gelu Popescu (1994). *Factorization and Reflexivity on Fock spaces*. URL: <https://arxiv.org/abs/math/9404209>.

*Acknowledgement.* Vittorio Giovannetti; Seth Lloyd; Lorenzo Maccone (2015). *Quantum Time*. DOI: [10.1103/PhysRevD.92.045033](https://doi.org/10.1103/PhysRevD.92.045033). URL: <https://arxiv.org/abs/1504.04215>.

*Commentary.*

Define J as the trajectory map multiplied by the inverse square root of T+1. Every evolution E(k) preserves inner products, so the trajectory inner product is T+1 times the original inner product. Thus J is a linear isometry. The inverse on the propagation kernel reads clock zero and multiplies by the square root of T+1. The construction includes T=0 and the zero-dimensional space.

In finite dimension D is continuous and its adjoint exists. The identity ContinuousLinearMap.ker_adjoint_comp_self identifies the kernels of D*D and D. The quadratic form of D*D is the squared norm of Dx and is nonnegative. Hence J is an isometric equivalence from H to the zero-energy propagation space. This operator positivity is distinct from positivity of event counts. Aharonov, van Dam, Kempe, Landau, Lloyd and Regev, Adiabatic Quantum Computation is Equivalent to Standard Quantum Computation, section 3.1.1, equations (5)-(6) and Claim 3.3, give the finite history-state setting. Their fixed-input and clock penalties impose additional conditions; the propagation operator here retains every initial vector.

For a unit vector psi, J psi has norm one and its component at clock k is E(k)psi divided by the square root of T+1. This direct-sum representation is the usual clock-basis representation of a finite history state. Clock conditioning is a component statement; it does not assert that arbitrary clock measurements leave a protocol undisturbed. The reference boundary can be any chosen initial interface. Infinite equal-weight clocks do not follow by putting T equal to infinity.

WordHistoryOperators defines the reusable word Hilbert space, append map and finite-support number operator, and proves number_unbounded. On the complete space ell2 of all finite words over a nonempty alphabet, right append maps the basis vector at w to the basis vector at wg. The injection of word indices gives an orthogonal family; OrthogonalFamily.linearIsometry extends it to the complete Hilbert space. Its adjoint reads the coordinate at wg. Consequently Sg* Sg=I and Sg Sg* projects onto words ending in g; the empty-word vector proves this projection is proper. Finite-support vectors are dense by lp.hasSum_single. Multiplication of the w-coordinate by the length of w defines N on that domain. N, Sg and Sg* preserve finite support, and NSg-SgN=Sg there. On a unit basis vector at a word of length n, the norm of N is n; no continuous linear map can agree with N on this domain. Appending an inverse-readout letter is another creation operator, not Sg*: the two-letter extension is distinct from the original word. Arias and Popescu, Factorization and Reflexivity on Fock spaces, introduce orthogonal creation operators; word reversal converts their left creation convention to right creation. These conclusions use the entire word space, not a truncated matrix model.

Under the finite quantum representation and Born rule, fix an output with finite path fiber P, actual complex path amplitudes A(p), and unit records m(p) in a complex Hilbert space. Its probability contribution is the squared norm of the sum of A(p)m(p). Expanding the inner product gives the sum over p,q of A(p) conjugate(A(q)) times the inner product of m(q) with m(p). Identical records give the squared modulus of the amplitude sum. Orthonormal records give the sum of squared moduli. For two normalized records the squared norms of (m(0)+m(1))/2 and (m(0)-m(1))/2 are respectively (1+Re inner(m(0),m(1)))/2 and (1-Re inner(m(0),m(1)))/2. They give the two Hadamard output probabilities, including unit return probability for identical records and one half for orthogonal records. EnvironmentMarginalChannel.environment_marginal_channel supplies the finite matrix partial-trace form of the record Gram channel. A path index alone supplies no physical record. For a typed finite complex circuit, matrix composition supplies the independent output semantics. A path stores one internal basis index at each cut, and its amplitude is the product of the actual matrix entries. Matrix.mul_apply and finite product-index summation identify the output entry with the sum of these path amplitudes. Rectangular dimensions and the zero-step circuit are included. For a finite acyclic tensor circuit, choose a legal topological schedule and retain unused wires as spectator factors; its gate matrices give exactly this typed contraction. Feeding these actual amplitudes and paths to the record Gram identity yields the stated output probability. The independent port and schedule constructions are documented in FiniteCausalPortGraph and FiniteCausalScheduleProtocol.

For finite Kraus matrices K(a,mu) with sum K(a,mu)* K(a,mu)=I, define the record matrix V by V((i,(a,mu)),j)=K(a,mu)(i,j). Its columns are orthonormal. Selecting the actual outcome a and tracing the multiplicity mu gives the branch sum K(a,mu) rho K(a,mu)*. This branch is positive for positive rho; when its trace p is positive, division by p gives a density matrix. FiniteKrausChannel.finite_kraus_quantum_channel supplies the canonical completely positive trace-preserving map. Given blank and record isometries into one finite ambient space, LinearIsometry.extend extends their range identification to a unitary on that space. A sufficiently large ambient space includes both embeddings. The finite-dimensional Kraus and isometric representation setting is Watrous, The Theory of Quantum Information, Theorems 2.22 and 2.26 and Corollary 2.27. The finite tree in FiniteLocalProtocol.recursive_coarse_retained retains all actual outcome prefixes and terminal states. Taking a single actor whose interface is the whole joint system includes every later-participating environment among the active coordinates. Its separate garbage coordinates are inaccessible and are not a model for an environment that returns. The child function depends on the actual outcome, so finite feedback remains internal to the record tree.

An isometry that clones two unit vectors preserves their overlap, while the tensor product of their copies squares it. Thus the overlap equals its square. It is zero or one, and overlap one for unit vectors forces equality. Distinct nonorthogonal pure states therefore cannot be uniformly cloned by an isometry. This is a statement about linear physical records, not an explanation of single-outcome experience.

If the second system unitary is the inverse of the first, the system vector at clock two equals its vector at clock zero. The clock positions remain distinct and orthogonal. The single isometric Kraus matrix sending psi to psi tensor clock-two defines a canonical quantum channel on every input matrix; tracing that clock returns the input exactly. Thus zero system restoration error is consistent with a distinct final history record.

CalibratedUnitaryGroup.calibrated_group supplies the reusable continuous calibration theorem. Continuous calibration is a separate assumption. Let U be a differentiable one-parameter unitary group with real parameter t, U(0)=I, and derivative G at zero. Differentiating the group law gives U'(t)=G U(t), and differentiating U(t)*U(t)=I at zero gives G*=-G. The derivative of exp(-tG)U(t) vanishes, hence U(t)=exp(tG). Given an independently supplied nonzero real hbar, H=i hbar G is self-adjoint and U(t)=exp(-i t H/hbar). Applying the derivative to an initial vector gives the Schrodinger equation. In finite dimension all these derivatives are ordinary operator-norm derivatives. Neither the parameter nor hbar is determined by the discrete event count. Giovannetti, Lloyd and Maccone, Quantum Time, section II.A, equations (1)-(4), discuss conditional-clock dynamics; their generalized continuous-clock eigenvectors do not provide an infinite normalized equal-weight history vector.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/FinitePropagationHistory.history_range`
- Truth anchor: `D5/S3/Quantum/Dynamics/FinitePropagationHistory.propagation_kernel`

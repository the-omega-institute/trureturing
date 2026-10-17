# Positive Pauli Clock Order

## Abstract

The positive two-dimensional clock has equal isolated reduced channels and a nontrivial implemented order overlap.

This model instantiates QUANTUM-REALITY sections 101, 103 and theorem 107.2. The overlap convention is section 85: branch zero implements Q and branch one P. All velocities, frequencies and durations below are real. The source experiment takes positive frequency; the algebraic identities also hold for arbitrary real frequency. Durations have no sign restriction.

$$
(\operatorname{HG}\left(\right) = C^{2}) \land\\{}(X = \begin{pmatrix}0&1\\1&0\end{pmatrix}) \land\\{}(Z = \begin{pmatrix}1&0\\0&-1\end{pmatrix}) \land\\{}(\operatorname{R}\left(v\right) = (\frac{3}{2}-\frac{(v)^{2}}{4})I+\frac{1-v}{2} X+\frac{1+v}{2} Z) \land\\{}(\operatorname{N}\left(v\right) = \operatorname{CFCsqrt}\left(\operatorname{R}\left(v\right)\right)) \land\\{}(\sigma = \frac{1}{2} I)
$$

$$
(A = \frac{3}{2} I+\frac{1}{2} ( X + Z )) \land\\{}(Bcoeff = \frac{1}{4} ( Z - X )) \land\\{}(Ccoeff = \frac{1}{4} I) \land\\{}(\operatorname{V}\left(v, w, t\right) = \operatorname{exp}\left(-i w t \operatorname{N}\left(v\right)\right)) \land\\{}(\operatorname{B}\left(\operatorname{Q}\left(w, t_{+}, t_{-}\right), \operatorname{P}\left(w, t_{+}, t_{-}\right)\right) = \operatorname{kron}\left(\operatorname{E}\left(0, 0\right), \operatorname{Q}\left(w, t_{+}, t_{-}\right)\right)+\operatorname{kron}\left(\operatorname{E}\left(1, 1\right), \operatorname{P}\left(w, t_{+}, t_{-}\right)\right))
$$

$$
(\operatorname{U}\left(v, w, t\right) = \operatorname{B}\left(I, \operatorname{V}\left(v, w, t\right)\right)) \land\\{}(\operatorname{Phi}\left(v, w, t, \rho\right) = \operatorname{trG}\left(\operatorname{U}\left(v, w, t\right) \operatorname{kron}\left(\rho, \sigma\right) (\operatorname{U}\left(v, w, t\right))^{*}\right)) \land\\{}(\operatorname{chi}\left(v, w, t\right) = \operatorname{tr}\left(\sigma \operatorname{V}\left(v, w, t\right)\right)) \land\\{}(\operatorname{P}\left(w, t_{+}, t_{-}\right) = \operatorname{V}\left(-1, w, t_{-}\right) \operatorname{V}\left(1, w, t_{+}\right)) \land\\{}(\operatorname{Q}\left(w, t_{+}, t_{-}\right) = \operatorname{V}\left(1, w, t_{+}\right) \operatorname{V}\left(-1, w, t_{-}\right)) \land\\{}(\operatorname{H}\left(w, t_{+}, t_{-}\right) = (\operatorname{Q}\left(w, t_{+}, t_{-}\right))^{*} \operatorname{P}\left(w, t_{+}, t_{-}\right)) \land\\{}(\operatorname{gamma}\left(w, t_{+}, t_{-}\right) = \operatorname{tr}\left(\sigma \operatorname{H}\left(w, t_{+}, t_{-}\right)\right)) \land\\{}(\operatorname{rhoplus}\left(\right) = \frac{1}{2} \begin{pmatrix}1&1\\1&1\end{pmatrix}) \land\\{}(\operatorname{rhoctrl}\left(w, t_{+}, t_{-}\right) = \operatorname{trG}\left(\operatorname{B}\left(\operatorname{Q}\left(w, t_{+}, t_{-}\right), \operatorname{P}\left(w, t_{+}, t_{-}\right)\right) \operatorname{kron}\left(\operatorname{rhoplus}\left(\right), \sigma\right) (\operatorname{B}\left(\operatorname{Q}\left(w, t_{+}, t_{-}\right), \operatorname{P}\left(w, t_{+}, t_{-}\right)\right))^{*}\right))
$$

**Theorem 1.1 (Standing coefficient witnesses).**

$$(\operatorname{Hermitian}\left(A\right)) \land\\{}(\operatorname{Hermitian}\left(Bcoeff\right)) \land\\{}(\operatorname{Hermitian}\left(Ccoeff\right)) \land\\{}(\frac{1}{2} I \le A) \land\\{}(\forall v \in R, \operatorname{R}\left(v\right) = A+2 v Bcoeff-(v)^{2} Ccoeff) \land\\{}(\forall \xi \in R, (\xi)^{2} Ccoeff = \frac{(\xi)^{2}}{4} I)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_clock_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Hermitian coefficients and the positive constants one half and one quarter are concrete derived data.

**Theorem 1.2 (Positivity on the whole source interval).**

$$\forall v \in R, (|v| < \sqrt{\frac{3}{2}}) \Rightarrow \operatorname{PosDef}\left(\operatorname{R}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_clock_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant estimate is strict on the entire open interval. The model is not restricted to its two pulse directions.

**Theorem 1.3 (Both pulse directions are admissible).**

$$(|1|<\sqrt{\frac{3}{2}}) \land\\{}(|-1|<\sqrt{\frac{3}{2}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.special_directions_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both specified velocities lie strictly inside the source domain.

**Theorem 1.4 (The positive root is invertible).**

$$\forall v \in R, (|v| < \sqrt{\frac{3}{2}}) \Rightarrow \operatorname{PosDef}\left(\operatorname{N}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_clock_speed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The speed is the CFC square root of the response. Response positivity proves root positivity and invertibility.

**Theorem 1.5 (Exact special positive roots).**

$$(\operatorname{N}\left(1\right) = I+\frac{1}{2} Z) \land\\{}(\operatorname{N}\left(-1\right) = I+\frac{1}{2} X) \land\\{}(\operatorname{PosDef}\left(I+\frac{1}{2} Z\right)) \land\\{}(\operatorname{PosDef}\left(I+\frac{1}{2} X\right)) \land\\{}((I+\frac{1}{2} Z)^{2} = \operatorname{R}\left(1\right)) \land\\{}((I+\frac{1}{2} X)^{2} = \operatorname{R}\left(-1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_clock_special_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity and the exact squares identify the candidates uniquely with the positive functional-calculus roots.

**Theorem 1.6 (Canonical maximally mixed state).**

$$(\operatorname{matrix}\left(\operatorname{mixedState}\left(\right)\right) = \sigma) \land\\{}(\operatorname{Surjective}\left(\operatorname{mulVec}\left(\sigma\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.mixed_state_full_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

mixedState inhabits the current Foundation density carrier, with positivity and trace one proved. Its matrix has full range, so the standing support is the identity.

**Theorem 1.7 (Existing propagator and source exponential agree).**

$$\forall v,w,t \in R, \operatorname{V}\left(v, w, t\right) = \operatorname{exp}\left(-i w t \operatorname{N}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.pulse_eq_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

pulse reuses hamiltonianPropagator with Hamiltonian omega times the actual positive root.

**Theorem 1.8 (Unitary structure propagation).**

$$\forall v,w,t \in R, (|v| < \sqrt{\frac{3}{2}}) \Rightarrow \operatorname{Unitary}\left(\operatorname{V}\left(v, w, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.clock_propagators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized generator is skew-adjoint. No additional free structure evolution is inserted.

**Theorem 1.9 (Implemented controlled clock evolution).**

$$\forall v,w,t \in R, (|v| < \sqrt{\frac{3}{2}}) \Rightarrow (\operatorname{Unitary}\left(\operatorname{B}\left(I, \operatorname{V}\left(v, w, t\right)\right)\right)) \land\\{}(\operatorname{B}\left(I, \operatorname{V}\left(v, w, t\right)\right) = \operatorname{kron}\left(\operatorname{E}\left(0, 0\right), I\right)+\operatorname{kron}\left(\operatorname{E}\left(1, 1\right), \operatorname{V}\left(v, w, t\right)\right)) \land\\{}(\forall a,b\in\operatorname{Fin}\left(2\right),\operatorname{entry}\left(\operatorname{B}\left(I, \operatorname{V}\left(v, w, t\right)\right), \operatorname{pair}\left(1, a\right), \operatorname{pair}\left(1, b\right)\right) = \operatorname{entry}\left(\operatorname{V}\left(v, w, t\right), a, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled_clock_evolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint operator is the source's controlled expression. Its excited-clock block acts by the actual structure propagator.

**Theorem 1.10 (Unitary controlled qubit matrices).**

$$\forall Q \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), Complex\right),\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), Complex\right),\; (Q \in \operatorname{unitary}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), Complex\right)\right)) \Rightarrow ((P \in \operatorname{unitary}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), Complex\right)\right)) \Rightarrow (\operatorname{Matrix}.\operatorname{submatrix}\left(\operatorname{Matrix}.\operatorname{blockDiagonal}\left(![Q, P]\right), \operatorname{Prod}.\operatorname{swap}, \operatorname{Prod}.\operatorname{swap}\right) \in \operatorname{unitary}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right), Complex\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two unitary complex qubit matrices Q and P, the controlled matrix is unitary. The matrix is block diagonal with blocks Q and P, with both pair coordinates swapped. Thus the first coordinate selects Q for 0 and P for 1, while the second coordinate carries their action.

**Theorem 1.11 (Mixed controlled-block trace identity).**

$$\forall Q,P,\rho\in\operatorname{Mat}\left(2, C\right),\forall j,k\in\operatorname{Fin}\left(2\right),\operatorname{entry}\left(\operatorname{trG}\left(\operatorname{B}\left(Q, P\right) \operatorname{kron}\left(\rho, \sigma\right) (\operatorname{B}\left(Q, P\right))^{*}\right), j, k\right) = \operatorname{entry}\left(\rho, j, k\right) \operatorname{tr}\left(\sigma (\operatorname{branch}\left(Q, P, k\right))^{*} \operatorname{branch}\left(Q, P, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled_partial_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Q, P and rho are arbitrary complex two-dimensional matrices. branch(Q,P,0) is Q and branch(Q,P,1) is P. The identity directly expands the mixed partial trace; no damping or Gram hypothesis is assumed.

**Theorem 1.12 (All entries of the actual reduced channel).**

$$\forall v,w,t \in R, (|v| < \sqrt{\frac{3}{2}}) \Rightarrow \forall \rho\in\operatorname{Mat}\left(2, C\right),\operatorname{Phi}\left(v, w, t, \rho\right) = \begin{pmatrix}\operatorname{entry}\left(\rho, 0, 0\right)&(\operatorname{chi}\left(v, w, t\right))^{*} \operatorname{entry}\left(\rho, 0, 1\right)\\\operatorname{chi}\left(v, w, t\right) \operatorname{entry}\left(\rho, 1, 0\right)&\operatorname{entry}\left(\rho, 1, 1\right)\end{pmatrix}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.clock_reduced_entries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The raw matrix identity specializes to every canonical density state. The conjugate occurs in the upper off-diagonal entry.

**Theorem 1.13 (Special propagators with their global phase).**

$$\forall w,t \in R, (\operatorname{V}\left(1, w, t\right) = \operatorname{exp}\left(-i w t\right) ( \operatorname{cos}\left(\frac{w t}{2}\right) I - i \operatorname{sin}\left(\frac{w t}{2}\right) Z )) \land\\{}(\operatorname{V}\left(-1, w, t\right) = \operatorname{exp}\left(-i w t\right) ( \operatorname{cos}\left(\frac{w t}{2}\right) I - i \operatorname{sin}\left(\frac{w t}{2}\right) X ))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.clock_pulse_special_directions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinned Mathlib's map_exp applied to the two-coordinate algebra map and exp_diagonal evaluate the actual exponentials. No Hadamard result is copied or reproved.

**Theorem 1.14 (Equal isolated coherence functions).**

$$\forall w,t \in R, (\operatorname{chi}\left(1, w, t\right) = \operatorname{exp}\left(-i w t\right) \operatorname{cos}\left(\frac{w t}{2}\right)) \land\\{}(\operatorname{chi}\left(-1, w, t\right) = \operatorname{exp}\left(-i w t\right) \operatorname{cos}\left(\frac{w t}{2}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.isolated_clock_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maximally mixed structure state gives the same coherence for both directions at every real duration.

**Theorem 1.15 (Equal isolated reduced channels).**

$$\forall w,t \in R, \forall \rho\in\operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\operatorname{Phi}\left(1, w, t, \rho\right) = \operatorname{Phi}\left(-1, w, t, \rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.isolated_clock_channels_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality quantifies over the current canonical density-state carrier and the actual partial-trace maps.

**Theorem 1.16 (Actual pi-pulse operators).**

$$\forall w,t \in R, (w t = \pi) \Rightarrow (\operatorname{V}\left(1, w, t\right) = i Z) \land\\{}(\operatorname{V}\left(-1, w, t\right) = i X)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.pi_clock_pulses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pulse equation yields iZ and iX, including the global phase inherited from the positive roots.

**Theorem 1.17 (Opposite pulse orders differ by sign).**

$$\forall w,t \in R, (w t = \pi) \Rightarrow \operatorname{V}\left(-1, w, t\right) \operatorname{V}\left(1, w, t\right) = -(\operatorname{V}\left(1, w, t\right) \operatorname{V}\left(-1, w, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.pi_clock_orders_anticommute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential identities specialize the existing canonical Pauli anticommutation theorem.

**Theorem 1.18 (Actual coherent order marginal).**

$$\forall w,t_{+},t_{-} \in R, \operatorname{rhoctrl}\left(w, t_{+}, t_{-}\right) = \frac{1}{2} \begin{pmatrix}1&(\operatorname{gamma}\left(w, t_{+}, t_{-}\right))^{*}\\\operatorname{gamma}\left(w, t_{+}, t_{-}\right)&1\end{pmatrix}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.order_control_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same structure register is retained through both pulses. Branch zero carries Q and branch one P; the structure is discarded only after the coherent comparison.

**Theorem 1.19 (General-duration interference coefficient).**

$$\forall w,t_{+},t_{-} \in R, \operatorname{gamma}\left(w, t_{+}, t_{-}\right) = 1-2 (\operatorname{sin}\left(\frac{w t_{+}}{2}\right))^{2} (\operatorname{sin}\left(\frac{w t_{-}}{2}\right))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.order_interference_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With a equal to omega tPlus over two and b equal to omega tMinus over two, the independent operator trace evaluates to one minus twice sin(a) squared sin(b) squared.

**Theorem 1.20 (Relative pi phase in the implemented control).**

$$\forall w,t \in R, (w t = \pi) \Rightarrow (\operatorname{H}\left(w, t, t\right) = -I) \land\\{}(\operatorname{gamma}\left(w, t, t\right) = -1) \land\\{}(\operatorname{rhoctrl}\left(w, t, t\right) = \frac{1}{2} \begin{pmatrix}1&-1\\-1&1\end{pmatrix})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.pi_order_relative_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual relative operator is minus the identity, the trace overlap is minus one, and the control state has negative off-diagonal entries.

For the classical comparison, each run has a fixed label lambda and real scalar rates nPlus(lambda), nMinus(lambda). Both phases read that same label. Define zPlus and zMinus by the scalar exponential at their respective durations, and c(lambda) as the conjugate of zPlus zMinus multiplied by zMinus zPlus.

$$
(\operatorname{zplus}\left(\lambda\right) = \operatorname{exp}\left(-i w t_{+} \operatorname{nplus}\left(\lambda\right)\right)) \land\\{}(\operatorname{zminus}\left(\lambda\right) = \operatorname{exp}\left(-i w t_{-} \operatorname{nminus}\left(\lambda\right)\right)) \land\\{}(\operatorname{c}\left(\lambda\right) = (\operatorname{zplus}\left(\lambda\right) \operatorname{zminus}\left(\lambda\right))^{*} \operatorname{zminus}\left(\lambda\right) \operatorname{zplus}\left(\lambda\right))
$$

**Theorem 1.21 (Fixed-label scalar order).**

$$\forall \Lambda,\forall nplus,nminus:\Lambda \to R,\forall w,t_{+},t_{-} \in R, \forall \lambda\in\Lambda,(\operatorname{zminus}\left(\lambda\right) \operatorname{zplus}\left(\lambda\right) = \operatorname{zplus}\left(\lambda\right) \operatorname{zminus}\left(\lambda\right)) \land\\{}(\operatorname{c}\left(\lambda\right) = 1) \land\\{}(\operatorname{c}\left(\lambda\right)\neq-1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.fixed_scalar_clock_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These scalar phases commute and have unit modulus. The relative coefficient is one, so it cannot be minus one.

**Theorem 1.22 (Arbitrary probability averaging).**

$$\forall \Lambda,\operatorname{MeasurableSpace}\left(\Lambda\right),\forall \mu\in\operatorname{ProbabilityMeasures}\left(\Lambda\right),\forall nplus,nminus:\Lambda \to R,\forall w,t_{+},t_{-} \in R, (\int \operatorname{c}\left(\lambda\right) d\mu = 1) \land\\{}(\int \operatorname{c}\left(\lambda\right) d\mu\neq-1) \land\\{}(\int \operatorname{zminus}\left(\lambda\right) \operatorname{zplus}\left(\lambda\right) d\mu = \int \operatorname{zplus}\left(\lambda\right) \operatorname{zminus}\left(\lambda\right) d\mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.averaged_fixed_scalar_clock_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measure is any probability measure on the label space. Rates need no measurability assumption for the relative coefficient, which is pointwise constant before integration. Pointwise equal ordered amplitudes also have equal Bochner integrals. Their equality alone would not exclude a sign, since both averaged amplitudes can vanish.

**Theorem 1.23 (Positive-frequency source experiment).**

$$\forall w \in R, (w>0) \Rightarrow (\forall v \in R, (|v| < \sqrt{\frac{3}{2}}) \Rightarrow (\operatorname{PosDef}\left(\operatorname{R}\left(v\right)\right)) \land\\{}(\operatorname{PosDef}\left(\operatorname{N}\left(v\right)\right)) \land\\{}((\operatorname{N}\left(v\right))^{2} = \operatorname{R}\left(v\right))) \land\\{}((\operatorname{Hermitian}\left(A\right)) \land\\{}(\operatorname{Hermitian}\left(Bcoeff\right)) \land\\{}(\operatorname{Hermitian}\left(Ccoeff\right)) \land\\{}(\frac{1}{2} I \le A) \land\\{}(\forall v \in R, \operatorname{R}\left(v\right) = A+2 v Bcoeff-(v)^{2} Ccoeff) \land\\{}(\forall \xi \in R, (\xi)^{2} Ccoeff = \frac{(\xi)^{2}}{4} I)) \land\\{}((\operatorname{N}\left(1\right) = I+\frac{1}{2} Z) \land\\{}(\operatorname{N}\left(-1\right) = I+\frac{1}{2} X)) \land\\{}((\operatorname{matrix}\left(\operatorname{mixedState}\left(\right)\right) = \sigma) \land\\{}(\operatorname{Surjective}\left(\operatorname{mulVec}\left(\sigma\right)\right))) \land\\{}(\forall v,t \in R, (|v| < \sqrt{\frac{3}{2}}) \Rightarrow \operatorname{Unitary}\left(\operatorname{B}\left(I, \operatorname{V}\left(v, w, t\right)\right)\right)) \land\\{}(\forall t \in R, (\operatorname{chi}\left(1, w, t\right) = \operatorname{exp}\left(-i w t\right) \operatorname{cos}\left(\frac{w t}{2}\right)) \land\\{}(\operatorname{chi}\left(-1, w, t\right) = \operatorname{exp}\left(-i w t\right) \operatorname{cos}\left(\frac{w t}{2}\right))) \land\\{}(\forall t \in R, \forall \rho\in\operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\operatorname{Phi}\left(1, w, t, \rho\right) = \operatorname{Phi}\left(-1, w, t, \rho\right)) \land\\{}(\forall t_{+},t_{-} \in R, (\operatorname{gamma}\left(w, t_{+}, t_{-}\right) = 1-2 (\operatorname{sin}\left(\frac{w t_{+}}{2}\right))^{2} (\operatorname{sin}\left(\frac{w t_{-}}{2}\right))^{2}) \land\\{}(\operatorname{rhoctrl}\left(w, t_{+}, t_{-}\right) = \frac{1}{2} \begin{pmatrix}1&(\operatorname{gamma}\left(w, t_{+}, t_{-}\right))^{*}\\\operatorname{gamma}\left(w, t_{+}, t_{-}\right)&1\end{pmatrix})) \land\\{}(\forall t \in R, (w t = \pi) \Rightarrow (\operatorname{V}\left(1, w, t\right) = i Z) \land\\{}(\operatorname{V}\left(-1, w, t\right) = i X) \land\\{}(\operatorname{V}\left(-1, w, t\right) \operatorname{V}\left(1, w, t\right) = -(\operatorname{V}\left(1, w, t\right) \operatorname{V}\left(-1, w, t\right))) \land\\{}((\operatorname{H}\left(w, t, t\right) = -I) \land\\{}(\operatorname{gamma}\left(w, t, t\right) = -1) \land\\{}(\operatorname{rhoctrl}\left(w, t, t\right) = \frac{1}{2} \begin{pmatrix}1&-1\\-1&1\end{pmatrix}))) \land\\{}(w \frac{\pi}{w} = \pi) \land\\{}(\forall \Lambda,\operatorname{MeasurableSpace}\left(\Lambda\right),\forall \mu\in\operatorname{ProbabilityMeasures}\left(\Lambda\right),\forall nplus,nminus:\Lambda \to R,\forall t_{+},t_{-} \in R, (\int \operatorname{c}\left(\lambda\right) d\mu = 1) \land\\{}(\int \operatorname{c}\left(\lambda\right) d\mu\neq-1) \land\\{}(\int \operatorname{zminus}\left(\lambda\right) \operatorname{zplus}\left(\lambda\right) d\mu = \int \operatorname{zplus}\left(\lambda\right) \operatorname{zminus}\left(\lambda\right) d\mu))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_pauli_clock_order_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive omega, pi over omega supplies an actual duration satisfying the pulse equation. The combined assertion retains the positive model, canonical state, implemented joint evolution, isolated equality, general-duration overlap and pi witness, together with the fixed scalar probability-average boundary.

The exclusion concerns only fixed commuting scalar clocks. Time-varying classical backgrounds, other apparatus actions, and path-dependent models require separate exclusion. The coherent comparison consumes the actual implemented operators; isolated channel tables alone do not specify controlled implementations. The reference time is the calibrated protocol parameter. The response coefficients are clock-response operators, not a claimed complete quantum spacetime metric.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.averaged_fixed_scalar_clock_order`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.clock_propagators`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.clock_pulse_special_directions`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.clock_reduced_entries`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled_clock_evolution`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled_partial_trace`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.controlled_unitary`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.fixed_scalar_clock_order`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.isolated_clock_channels_equal`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.isolated_clock_coherence`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.mixed_state_full_support`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.order_control_marginal`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.order_interference_formula`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.pi_clock_orders_anticommute`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.pi_clock_pulses`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.pi_order_relative_phase`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_clock_coefficients`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_clock_model`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_clock_special_roots`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_clock_speed`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.positive_pauli_clock_order_separation`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.pulse_eq_exp`
- Truth anchor: `D5/S3/Quantum/Dynamics/PositivePauliClockOrder.special_directions_mem`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/EnvironmentRecords](../EnvironmentRecords.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)

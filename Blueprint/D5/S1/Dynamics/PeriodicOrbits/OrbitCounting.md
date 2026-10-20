# Periodic Orbits, Phases and Divisor Counts

## Abstract

Actual forward cycles explain the arithmetic of finite periodic-point counts.

Let f be a self-map. A point has least period n when n is its minimal positive return time. The type Stratum consists of such points, and Orbits is the image of their actual periodic cycles under cyclic change of starting point. Every theorem here using a period assumes it is positive. Transient points have minimal period zero and contribute to none of these strata. No injectivity of f is assumed.

In the formulas, P(f,n) denotes Stratum, O(f,n) denotes Orbits, m(f,n) denotes cycleLengthMultiplicity, and A(f,n) denotes fixedCount. The symbol card is finite cardinality, val forgets a subtype proof, and rep is the chosen representative. Integer products on the right of a delta identity use the natural-to-integer cast.

$$
\Delta(a,n)=\sum_{(u,v)\in \operatorname{divisorsAntidiagonal}\left(n\right)}\mu(u)a(v)
$$

**Theorem 1.1 (Reconstruct each point from its orbit and phase).**

$$\forall X:\operatorname{Type},  f:X\to X, n\in \mathbb{N}, 0<n\Rightarrow \exists e:\operatorname{O}\left(f, n\right)\times \operatorname{Fin}\left(n\right)\equiv \operatorname{P}\left(f, n\right), \forall o:\operatorname{O}\left(f, n\right), i:\operatorname{Fin}\left(n\right), \operatorname{val}\left(\operatorname{e}\left(o, i\right)\right)=f^{\operatorname{val}\left(i\right)}(\operatorname{val}\left(\operatorname{rep}\left(f, n, o\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.orbit_phase_decomposition` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

Choosing one actual representative of each cycle gives an equivalence from Orbits times Fin n to Stratum. Its value at an orbit and phase i is the ith iterate of that representative. Distinct phases are distinct by minimality of the period; every point on the cycle occurs at one phase. This statement does not require the ambient carrier to be finite.

**Theorem 1.2 (Each orbit contributes exactly one period of points).**

$$\forall X:\operatorname{Type}, [\operatorname{Fintype}\left(X\right)], f:X\to X, n\in \mathbb{N}, 0<n\Rightarrow \operatorname{card}\left(\operatorname{P}\left(f, n\right)\right)=n\cdot \operatorname{card}\left(\operatorname{O}\left(f, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.stratum_card` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

For a finite carrier, taking cardinalities of the phase equivalence gives n times the number of actual cycles. Empty strata are included.

**Theorem 1.3 (Division counts genuine cycles).**

$$\forall X:\operatorname{Type}, [\operatorname{Fintype}\left(X\right)], f:X\to X, n\in \mathbb{N}, 0<n\Rightarrow \operatorname{m}\left(f, n\right)=\operatorname{card}\left(\operatorname{O}\left(f, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.multiplicity_eq_orbit_card` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

The existing cycleLengthMultiplicity divides the stratum size by n. The exact phase decomposition shows that this quotient equals the cardinality of the actual orbit type.

**Theorem 1.4 (Fixed counts sum over least-period divisors).**

$$\forall X:\operatorname{Type}, [\operatorname{Fintype}\left(X\right)], f:X\to X, n\in \mathbb{N}, 0<n\Rightarrow \operatorname{A}\left(f, n\right)=\sum_{d\mid n}d\cdot \operatorname{m}\left(f, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.fixed_count_divisor_sum` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

A point is fixed by the nth iterate exactly when its least period divides n. Partitioning that finite fixed set and counting phases gives the sum of d times cycleLengthMultiplicity over the positive divisors d of n.

**Theorem 1.5 (Mobius inversion recovers complete cycles).**

$$\forall X:\operatorname{Type}, [\operatorname{Fintype}\left(X\right)], f:X\to X, n\in \mathbb{N}, 0<n\Rightarrow \Delta(\operatorname{A}\left(f\right),n)=n\cdot \operatorname{m}\left(f, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.delta_fixed_count` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

The integer transform delta sums mu(u) times the fixed count at v over positive factor pairs u times v equal to n. Mathlib's Mobius inversion identifies it with n times the actual number of n-cycles, explaining both its nonnegativity and its divisibility by n.

For the deterministic transition operator in TraceRankCombinatorics.trace_rank_combinatorial_meaning, the trace at positive time is precisely this actual fixed-point count. Thus the divisor sum supplies the cycle-trace equation used by TraceRankJordanRecovery. That recovery also requires its separate zero-block rank equations; periodic counts alone do not supply them and do not classify attached transient trees.

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.delta_fixed_count`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.fixed_count_divisor_sum`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.multiplicity_eq_orbit_card`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.orbit_phase_decomposition`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/OrbitCounting.stratum_card`
- Dependency: [D5/S1/Descent/FiniteSelfMapConjugacy](../../Descent/FiniteSelfMapConjugacy.md)

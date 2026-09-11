# Half-Line Zero Separation

## Abstract

An off-critical zeta zero separates the target from both half-line source closures.

H is the existing complex L2 space on (0,infinity), chi is the indicator of (0,1), and F_a is the real-parameter fractional-reciprocal source. The canonical predicate Zeta23.IsNontrivialZero(rho) means zeta(rho)=0 and 0<Re(rho)<1. Below beta=Re(rho)>1/2. These are conditional statements; they do not assert the existence of such a zero.

S_N is the original natural shell, including S_0={0}, and d_N is the existing infimum distance from chi to S_N. M is the original cumulative natural closed space, the closure of the union of these shells. C_real is defined separately as the closure of the complex span of every F_a with real a at least one. No equality of M and C_real is assumed.

**Theorem 1.1 (Target evaluation).**

$$\forall \rho\in \mathbb{C},\Re \rho> \frac{1}{2},\rho\neq1,J_{\rho}(\mathrm{chi})=\frac{1}{\rho}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target's tail integral vanishes. Its integral over (0,1) is the elementary complex power integral 1/rho. This evaluation does not require a zeta zero.

**Theorem 1.2 (All real sources vanish).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \forall a\in \mathbb{R},a\ge 1,J_{\rho}(F_{a})=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_realSource` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E9 at theta=1/a gives the near-zero integral. The source equals 1/(a*x) beyond one, so its integral after division by x is 1/a. At the stipulated zero, the two contributions cancel exactly, including a=1.

**Theorem 1.3 (Every finite shell vanishes).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \forall N\in \mathbb{N},\forall f\in S_{N},J_{\rho}(f)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Linearity and equality with the natural source vectors annihilate the span for every N, including zero. No Gram inverse or rank premise occurs.

**Theorem 1.4 (Natural closed space vanishes).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \forall f\in M,J_{\rho}(f)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel of J is closed and contains every shell. It therefore contains their union and its closure, which is the existing space M.

**Definition 1.5 (Full real source closure).**

$$C_{\mathrm{real}}=\overline{\operatorname{span}_{\mathbb{C}}\{F_{a}:a\in \mathbb{R},a\ge 1\}}$$

*Formalization.* `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.fullRealClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C_real is a closed complex submodule of H formed from all real parameters. It is not defined by the natural cumulative family.

**Theorem 1.6 (Full real closure vanishes).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \forall f\in C_{\mathrm{real}},J_{\rho}(f)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_fullRealClosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All real sources lie in the closed kernel, hence so do their complex span and its topological closure.

**Theorem 1.7 (Finite distance bound).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \forall N\in \mathbb{N},\frac{1}{{\Vert \rho\Vert}^{2}(\frac{1}{2\beta-1}+\frac{1}{{\Vert \rho-1\Vert}^{2}})}\le {d_{N}}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_distance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every f in S_N, J(chi-f)=1/rho. The operator norm inequality and the exact norm formula bound each distance, hence the infimum distance. The positive energy ensures division is valid.

**Theorem 1.8 (Natural closure distance bound).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \frac{1}{{\Vert \rho\Vert}^{2}(\frac{1}{2\beta-1}+\frac{1}{{\Vert \rho-1\Vert}^{2}})}\le {\operatorname{infDist}(\mathrm{chi},M)}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_closed_distance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same separation argument applies to M, using its annihilation by J.

**Theorem 1.9 (Full real closure distance bound).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \frac{1}{{\Vert \rho\Vert}^{2}(\frac{1}{2\beta-1}+\frac{1}{{\Vert \rho-1\Vert}^{2}})}\le {\operatorname{infDist}(\mathrm{chi},C_{\mathrm{real}})}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_real_closed_distance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same separation argument applies to the full real source closure. Neither closed-space bound assumes the two spaces coincide.

**Theorem 1.10 (Exact original radius chain).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \frac{1}{{\Vert \rho\Vert}^{2}(\frac{1}{2\beta-1}+\frac{1}{{\Vert \rho-1\Vert}^{2}})}=\frac{(2\beta-1){\Vert \rho-1\Vert}^{2}}{\Vert \rho\Vert^{4}}={\Vert 1-\frac{1}{\rho}\Vert}^{2}(1-{\Vert 1-\frac{1}{\rho}\Vert}^{2})> 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_radius_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original radius is r=norm(1-1/rho). The norm-square identity norm(rho-1)^2=norm(rho)^2-(2*beta-1) gives both equalities. The canonical zero hypotheses imply rho differs from zero and one, while beta>1/2 supplies the remaining positive factor.

**Theorem 1.11 (Complete conditional E11).**

$$\forall \rho\in \mathbb{C},\operatorname{IsNontrivialZero}(\rho),\beta=\Re \rho> \frac{1}{2}, \begin{gathered}(\forall N\in \mathbb{N},\frac{1}{{\Vert \rho\Vert}^{2}(\frac{1}{2\beta-1}+\frac{1}{{\Vert \rho-1\Vert}^{2}})}\le {d_{N}}^{2})\\\land \frac{1}{{\Vert \rho\Vert}^{2}(\frac{1}{2\beta-1}+\frac{1}{{\Vert \rho-1\Vert}^{2}})}\le {\operatorname{infDist}(\mathrm{chi},M)}^{2}\\\land \frac{1}{{\Vert \rho\Vert}^{2}(\frac{1}{2\beta-1}+\frac{1}{{\Vert \rho-1\Vert}^{2}})}\le {\operatorname{infDist}(\mathrm{chi},C_{\mathrm{real}})}^{2}\\\land \frac{1}{{\Vert \rho\Vert}^{2}(\frac{1}{2\beta-1}+\frac{1}{{\Vert \rho-1\Vert}^{2}})}=\frac{(2\beta-1){\Vert \rho-1\Vert}^{2}}{\Vert \rho\Vert^{4}}={\Vert 1-\frac{1}{\rho}\Vert}^{2}(1-{\Vert 1-\frac{1}{\rho}\Vert}^{2})> 0\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_e11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This combines the original finite-distance bound for every natural N, both separately defined closed-space bounds, and the full positive radius chain at Zeta23.IsNontrivialZero. The constructed complex-linear functional and its representative formula provide the separating witness.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.fullRealClosure`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_M`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_fullRealClosure`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_realSource`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_shell`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.halflineFunctional_target`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_closed_distance_bound`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_distance_bound`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_e11`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_radius_chain`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.nyman_halfline_real_closed_distance_bound`
- Dependency: [D5/S3/Observer/Hilbert/NymanBeurlingConeResidual](NymanBeurlingConeResidual.md)
- Dependency: [D5/S3/Observer/Hilbert/NymanHalflineMellinKernel](NymanHalflineMellinKernel.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin](../../Weil/ZetaPntBounds/NymanFractionalMellin.md)

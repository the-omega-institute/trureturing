# Finite uniform laws: Fourier and entropy estimates

## Abstract

Finite Fourier inversion, Gaussian point bounds and entropy estimates.

Throughout, Ω is a nonempty finite type with its uniform law. For X on Ω, p(k)=|{ω∈Ω:X(ω)=k}|/|Ω|. For integer-valued X, φ_X(t)=|Ω|⁻¹ Σω exp(X(ω) i t), with real t and complex exponential. For natural-valued X bounded by n, H(X)=Σ_{k=0}^n -p(k) log₂ p(k), with the summand zero at p(k)=0. These abbreviations denote literal finite counts and sums, not arbitrary mass functions. The estimates are consumed by CircularOrientationEntropyLowerBound.whole_theorem_one_two and supply no separate escape witness.

**Theorem 1.1 (A point-mass bound from characteristic-function decay).**

$$\forall X \in \mathit{Omega} \to \mathbb{Z},\; \forall k \in \mathbb{Z},\; \forall A \in \mathbb{R},\; 0 < A \Rightarrow \left(\left(\forall t \in \mathbb{R},\; \left\lVert \operatorname{phi}\left(t\right) \right\rVert \le \operatorname{exp}\left(-\left(A \cdot \operatorname{sin}\left(\frac{t}{2}\right)^{2}\right)\right)\right) \Rightarrow \operatorname{p}\left(k\right) \le \frac{\operatorname{sqrt}\left(\mathit{pi}\right)}{2 \cdot \operatorname{sqrt}\left(A\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Hypergraphs/FiniteFourier.finite_uniform_mass_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ω is universally quantified with Fintype and Nonempty instances. X:Ω→ℤ, k:ℤ and A:ℝ are arbitrary. The characteristic-function bound is required for every real t. Finite Fourier inversion on [-π,π], sin(|t|/2)≥|t|/π and the Gaussian integral give √π/(2√A). This auxiliary does not assert that a particular orientation law satisfies the characteristic-function hypothesis.

**Theorem 1.2 (Entropy from a uniform upper bound on every atom).**

$$\forall X \in \mathit{Omega} \to \mathbb{N},\; \forall n \in \mathbb{N},\; \left(\forall omega \in \mathit{Omega},\; \operatorname{X}\left(\mathit{omega}\right) \le n\right) \Rightarrow \left(\forall C \in \mathbb{R},\; 0 < C \Rightarrow \left(\left(\forall k \in \mathbb{N},\; \operatorname{p}\left(k\right) \le C\right) \Rightarrow -\operatorname{logb}\left(2, C\right) \le \operatorname{H}\left(X\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Hypergraphs/FiniteFourier.finite_entropy_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ω is again any nonempty finite type. The support bound X(ω)≤n holds for every ω, and p(k)≤C is assumed for every natural k, not just a designated atom. The displayed finite entropy includes every index in Finset.range(n+1). The proof uses normalization and monotonicity of the base-two logarithm on positive masses.

**Theorem 1.3 (Every atom has probability at most one).**

$$\forall X \in \mathit{Omega} \to \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{p}\left(k\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Hypergraphs/FiniteFourier.finite_mass_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty finite Ω, any X:Ω→ℕ and any k:ℕ, the fibre cardinality is at most the total cardinality. This bound is also consumed in the small-n entropy branch.

## References

- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFourier.finite_entropy_lower`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFourier.finite_mass_le_one`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/FiniteFourier.finite_uniform_mass_bound`

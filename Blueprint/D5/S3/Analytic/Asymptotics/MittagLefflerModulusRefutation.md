# The reverse Mittag-Leffler modulus characterization fails

## Abstract

A finite complex witness refutes the reverse Mittag-Leffler characterization.

**Definition 1.1 (The convergent two-parameter series).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Leftrightarrow \left(\forall alpha \in Real,\; 0 < alpha \Rightarrow \left(\forall beta \in Real,\; \forall z \in Complex,\; HasSum\left(((k: Nat) \mapsto \frac{z^{k}}{val\left(\operatorname{Real}.\operatorname{Gamma}\left(alpha \cdot val\left(k, Real\right) + beta\right), Complex\right)}), E\left(alpha, beta, z\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.IsSourceSeries` (`✓ std3`).

*Citation.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

Page 1, equation (1.1): “In this paper we study several inequalities of the two-parameter Mittag-Leffler function Eα,β, which is defined on the complex plane for α > 0 and β ∈ ℝ by the series representation” Eα,β(z) = ∑ from k = 0 to infinity of z^k/Γ(αk+β), z ∈ ℂ. The formula uses HasSum, so convergence is part of the relation. Alpha and beta are real, z is complex, and k is natural. The value val(k,Real) is the natural-to-real coercion, and val(Real.Gamma(alpha*val(k,Real)+beta),Complex) embeds the denominator in the complex plane. Division is totalized at Gamma poles.

**Definition 1.2 (The real reciprocal on the positive axis).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall x \in Real,\; reciprocal\left(E, alpha, beta, x\right) = \frac{1}{\operatorname{Complex}.\operatorname{re}\left(E\left(alpha, beta, val\left(x, Complex\right)\right)\right)}$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.reciprocal` (`✓ std3`).

*Citation.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

Page 18, Conjecture 25 uses “1/Eα,β(x)”. Here E is a real-real-complex-complex family and alpha, beta and x are real. The real part reads the real-valued series on real arguments, after embedding x in Complex.

**Definition 1.3 (Conjecture 25 in full).**

$$claim = \left(\left(\exists E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right)\right) \land \left(\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; \forall beta \in Real,\; 1 < alpha \Rightarrow \left(alpha < 2 \Rightarrow \left(0 \le beta \Rightarrow \left(\left(\left(\forall z \in Complex,\; \operatorname{Complex}.\operatorname{re}\left(E\left(alpha, beta, val\left(\operatorname{Complex}.\operatorname{re}\left(z\right), Complex\right)\right)\right) \le \left\lVert E\left(alpha, beta, z\right) \right\rVert\right) \Leftrightarrow \left(alpha - 1 \le beta \land beta \le alpha\right)\right) \land \left(\left(alpha - 1 \le beta \land beta \le alpha\right) \Leftrightarrow \left(\left(\forall x \in Real,\; 0 < x \Rightarrow 0 < reciprocal\left(E, alpha, beta, x\right)\right) \land \operatorname{D5}.\operatorname{S3}.\operatorname{Analytic}.\operatorname{ExpRatioCM}.\operatorname{Defs}.\operatorname{CompletelyMonotoneOn}\left(reciprocal\left(E, alpha, beta\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.claim` (`✓ std3`).

*Citation.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

Page 18: “Conjecture 25. For every α ∈ (1, 2), one has The inequality (1.4) holds globally ⇐⇒ β ∈ [α − 1, α] ⇐⇒ 1/Eα,β(x) is CM on (0, ∞).” Inequality (1.4) is |Eα,β(z)| ≥ Eα,β(Re z), and globally means every complex z. The parameter beta is nonnegative, as in the paper's inequality problem. The leading existential supplies the entire convergent family. The second conjunct expresses both equivalences for every such family. CompletelyMonotoneOn supplies smoothness and all nonnegative signed derivatives; the separate positivity clause preserves the positive codomain. The displayed val operations are the real-to-complex coercions.

**Theorem 1.4 (The characterization is false).**

$$\neg (\left(\exists E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right)\right) \land \left(\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; \forall beta \in Real,\; 1 < alpha \Rightarrow \left(alpha < 2 \Rightarrow \left(0 \le beta \Rightarrow \left(\left(\left(\forall z \in Complex,\; \operatorname{Complex}.\operatorname{re}\left(E\left(alpha, beta, val\left(\operatorname{Complex}.\operatorname{re}\left(z\right), Complex\right)\right)\right) \le \left\lVert E\left(alpha, beta, z\right) \right\rVert\right) \Leftrightarrow \left(alpha - 1 \le beta \land beta \le alpha\right)\right) \land \left(\left(alpha - 1 \le beta \land beta \le alpha\right) \Leftrightarrow \left(\left(\forall x \in Real,\; 0 < x \Rightarrow 0 < reciprocal\left(E, alpha, beta, x\right)\right) \land \operatorname{D5}.\operatorname{S3}.\operatorname{Analytic}.\operatorname{ExpRatioCM}.\operatorname{Defs}.\operatorname{CompletelyMonotoneOn}\left(reciprocal\left(E, alpha, beta\right)\right)\right)\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

At alpha = 3/2 and beta = 1/2, the interval condition holds. For z = −115+10i, the series instead satisfies norm(E(3/2,1/2,z)) < re(E(3/2,1/2,−115)). The 64-term sum on the real axis is greater than 3/100000, while the absolute real and imaginary parts at z are at most 1/1000000 and 1/100000. At either argument the omitted tail has norm at most 4/10^13. The series exists for every positive alpha and every real beta, including the reciprocal-Gamma pole values. The example refutes the implication from the parameter interval to the global reverse inequality. The all-alpha family, an interior-beta neighbourhood and a corrected universal region remain open here.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.IsSourceSeries`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.reciprocal`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.result`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](../../../S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.md)
- Dependency: [D5/S3/Analytic/ExpRatioCM/Defs](../ExpRatioCM/Defs.md)
- Dependency: [D5/S3/Analytic/KilbasSaigo/Series](../KilbasSaigo/Series.md)

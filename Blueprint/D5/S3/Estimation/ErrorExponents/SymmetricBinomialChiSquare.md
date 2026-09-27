# Symmetric Binomial Chi-Square Defect

## Abstract

The symmetric binomial mixture has an exact even-power chi-square defect, a hyperbolic-cosine envelope, and a root-fidelity bound.

**Definition 1.1 (Symmetric binomial mixture).**

$$\forall B: \mathbb{N}, z: \mathbb{R}, k: \mathbb{N}, {p_{z}}(B, z, k) = \frac{1}{2} \cdot \operatorname{choose}(B, k) \cdot {{\frac{1 + z}{2}}^{k} \cdot {\frac{1 - z}{2}}^{B - k} + {\frac{1 - z}{2}}^{k} \cdot {\frac{1 + z}{2}}^{B - k}}.$$

*Formalization.* `D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.p_z` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law averages the binomial mass with success parameters (1+z)/2 and (1-z)/2. Exchanging the two parameters leaves the mixture unchanged.

**Definition 1.2 (Central binomial reference law).**

$$\forall B: \mathbb{N}, k: \mathbb{N}, {p_{0}}(B, k) = \frac{\operatorname{choose}(B, k)}{{2}^{B}}.$$

*Formalization.* `D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.p_0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference law is the binomial distribution with success probability one half.

**Definition 1.3 (Finite chi-square defect).**

$$\forall B: \mathbb{N}, z: \mathbb{R}, \operatorname{chiSquare}(B, z) = \sum _{k \in \operatorname{range}(B + 1)} \frac{{{p_{z}}(B, z, k)}^{2}}{{p_{0}}(B, k)} - 1.$$

*Formalization.* `D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.chiSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chi-square defect is the second likelihood-ratio moment under the central law, minus one.

**Theorem 1.4 (Exact symmetric-binomial chi-square defect).**

$$\begin{aligned}\forall B: \mathbb{N}, z: \mathbb{R},\\{}\lvert z \rvert \le 1 \Rightarrow [\\{}(\forall k \in \operatorname{range}(B + 1), 0 \le {p_{z}}(B, z, k)) \land \\{}\sum _{k \in \operatorname{range}(B + 1)} {p_{z}}(B, z, k) = 1 \land \\{}(\forall k: \mathbb{N}, k \le B \Rightarrow \frac{{p_{z}}(B, z, k)}{{p_{0}}(B, k)} = \frac{{1 + z}^{k} \cdot {1 - z}^{B - k} + {1 - z}^{k} \cdot {1 + z}^{B - k}}{2}) \land \\{}\operatorname{chiSquare}(B, z) = \frac{{{1 + {z}^{2}}}^{B} + {{1 - {z}^{2}}}^{B}}{2} - 1 \land \\{}\operatorname{chiSquare}(B, z) = \sum _{j \in \operatorname{Icc}(1, \frac{B}{2})} \operatorname{choose}(B, 2 \cdot j) \cdot {z}^{4 \cdot j} \land \\{}\operatorname{chiSquare}(B, z) \le \operatorname{cosh}(B \cdot {z}^{2}) - 1 \land \\{}(\forall \delta: \mathbb{R}, (0 < \delta \land \delta \le \frac{1}{4} \land B \cdot \delta \le 1 \land {z}^{2} = 2 \cdot \delta - {\delta}^{2}) \Rightarrow \operatorname{chiSquare}(B, z) \le 3 \cdot {B \cdot \delta}^{2}) \land \\{}(\lvert z \rvert < 1 \Rightarrow ((\forall k \in \operatorname{range}(B + 1), 0 < {p_{z}}(B, z, k)) \land 0 < \operatorname{bhattacharyya}((k: \operatorname{Fin}(B + 1)) \mapsto {p_{0}}(B, k), (k: \operatorname{Fin}(B + 1)) \mapsto {p_{z}}(B, z, k)))) \land \\{}1 - {\operatorname{bhattacharyya}((k: \operatorname{Fin}(B + 1)) \mapsto {p_{0}}(B, k), (k: \operatorname{Fin}(B + 1)) \mapsto {p_{z}}(B, z, k))}^{2} \le \operatorname{chiSquare}(B, z)].\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.symmetric_binomial_chi_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For absolute bias at most one, the symmetric mixture is nonnegative and normalized. Its likelihood ratio has the closed symmetric sign-product form. Its chi-square defect is both the average of two binomial powers minus one and the finite sum of its positive even terms.

The even terms are bounded by the corresponding hyperbolic-cosine series. For the quadratic parameterization z squared equals 2 delta minus delta squared, the small-argument series comparison gives a quadratic defect bound.

In the strict interior, every mixture mass and the Bhattacharyya affinity are positive. The squared affinity loss is no larger than the chi-square defect, by comparing the squared root likelihood-ratio gap with the squared likelihood-ratio gap.

## References

- Truth anchor: `D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.chiSquare`
- Truth anchor: `D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.p_0`
- Truth anchor: `D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.p_z`
- Truth anchor: `D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.symmetric_binomial_chi_square`
- Dependency: [D5/S3/TotalVariation/Hellinger](../../TotalVariation/Hellinger.md)

# HermitianEigenvaluePerturbation

## Abstract

Public declarations of HermitianEigenvaluePerturbation, with complete parameters and the Lean operations.

**Theorem 1.1 (abs_eigenvalue_sub_eigenvalue_le_norm).**

$$\forall (n : \mathbb{N}) , \forall (d : \mathbb{N}) , \forall (T : \operatorname{EuclideanSpace} \mathbb{C} (Fin d) \to_{L} [\mathbb{C}] \operatorname{EuclideanSpace} \mathbb{C} (Fin d)) , \forall (S : \operatorname{EuclideanSpace} \mathbb{C} (Fin d) \to_{L} [\mathbb{C}] \operatorname{EuclideanSpace} \mathbb{C} (Fin d)) , \forall (hT : (\operatorname{val}\left(T\right)) . \operatorname{IsSymmetric}) , \forall (hS : (\operatorname{val}\left(S\right)) . \operatorname{IsSymmetric}) , \forall (hn : \operatorname{Module}. \operatorname{finrank} \mathbb{C} (\operatorname{EuclideanSpace} \mathbb{C} (Fin d)) = n) , \forall (k : Fin n) , \left|hT. \operatorname{eigenvalues} hn k - hS. \operatorname{eigenvalues} hn k\right| \leq \left\lVert T - S \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le_norm` (`✓ std3`). ∎

*Citation.* Jon Crall and LeanPool contributors (2026). *LeanPool DavisKahan Hermitian eigenvalue perturbation proofs*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.2 (norm_toEuclideanLin_le_of_entry_le).**

$$\forall (n : \mathbb{N}) , \forall (A : \operatorname{Matrix} (Fin n) (Fin n) \mathbb{C}) , \forall (\varepsilon : \mathbb{R}) , (\forall (i j : Fin n) , \left\lVert A i j \right\rVert \leq \varepsilon) \to (\forall (x : \operatorname{EuclideanSpace} \mathbb{C} (Fin n)) , \left\lVert (\operatorname{Matrix}. \operatorname{toEuclideanLin} A) x \right\rVert \leq \operatorname{val}\left(n\right) \cdot \varepsilon \cdot \left\lVert x \right\rVert)$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.norm_toEuclideanLin_le_of_entry_le` (`✓ std3`). ∎

*Citation.* Jon Crall and LeanPool contributors (2026). *LeanPool DavisKahan Hermitian eigenvalue perturbation proofs*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.3 (abs_eigenvalues0_sub_le_norm).**

$$\forall (n : \mathbb{N}) , \forall (A : \operatorname{Matrix} (Fin n) (Fin n) \mathbb{C}) , \forall (B : \operatorname{Matrix} (Fin n) (Fin n) \mathbb{C}) , \forall (hA : A. \operatorname{IsHermitian}) , \forall (hB : B. \operatorname{IsHermitian}) , \forall (k : Fin (\operatorname{Fintype}. \operatorname{card} (Fin n))) , \left|hA. \operatorname{eigenvalues}_{0} k - hB. \operatorname{eigenvalues}_{0} k\right| \leq \left\lVert \operatorname{Matrix}. \operatorname{toEuclideanCLM} (A - B) \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_norm` (`✓ std3`). ∎

*Citation.* Jon Crall and LeanPool contributors (2026). *LeanPool DavisKahan Hermitian eigenvalue perturbation proofs*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.4 (abs_eigenvalues0_sub_le_of_entry_le).**

$$\forall (n : \mathbb{N}) , \forall (A : \operatorname{Matrix} (Fin n) (Fin n) \mathbb{C}) , \forall (\operatorname{Ahat} : \operatorname{Matrix} (Fin n) (Fin n) \mathbb{C}) , \forall (hA : A. \operatorname{IsHermitian}) , \forall (\operatorname{hAhat} : \operatorname{Ahat}. \operatorname{IsHermitian}) , \forall (\varepsilon : \mathbb{R}) , (\forall (i j : Fin n) , \left\lVert \operatorname{Ahat} i j - A i j \right\rVert \leq \varepsilon) \to (\forall (k : Fin (\operatorname{Fintype}. \operatorname{card} (Fin n))) , \left|\operatorname{hAhat}. \operatorname{eigenvalues}_{0} k - hA. \operatorname{eigenvalues}_{0} k\right| \leq \operatorname{val}\left(n\right) \cdot \varepsilon)$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_of_entry_le` (`✓ std3`). ∎

*Citation.* Jon Crall and LeanPool contributors (2026). *LeanPool DavisKahan Hermitian eigenvalue perturbation proofs*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8>.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

## References

- Truth anchor: `D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le_norm`
- Truth anchor: `D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_norm`
- Truth anchor: `D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_of_entry_le`
- Truth anchor: `D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.norm_toEuclideanLin_le_of_entry_le`

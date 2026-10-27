# Pell circulant permanent and determinant

## Abstract

The permanent divided by the signed determinant of the Pell circulant tends to one.

**Definition 1.1 (The Pell circulant).**

$$\forall n \in \mathbb{N},\; \operatorname{C}\left(n\right) = \operatorname{Matrix}.\operatorname{circulant}\left((\operatorname{fun} (k : \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{D5}.\operatorname{S1}.\operatorname{Recurrence}.\operatorname{PellCompanionGcd}.\operatorname{P}\left(n - 1 - \operatorname{val}\left(k\right)\right)\right) : \mathbb{R}))\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.C` (`✓ std3`).

*Citation.* Stefano Spezia (2026). *OEIS A392131 and A392132: Pell circulant determinant and permanent*. URL: <https://oeis.org/A392131/internal>.

*Commentary.*

OEIS A392131, COMMENT (unpaginated): “a(n) is the determinant of the n X n Toeplitz matrix whose first column is formed by the vector(A000129(n-1), A000129(n-2), ..., A000129(0)) and whose first row is obtained by rotating once the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.” The Pell sequence is D5.S1.Recurrence.PellCompanionGcd.P. Mathlib Matrix.circulant evaluates its vector at i-j, where subtraction is in Fin n. Subtraction in the argument of P is natural-number subtraction, truncated at zero. Nat.cast has target ℝ. Thus the first row is (P(n-1), P(0), ..., P(n-2)); at n=4 it is (5,0,1,2).

**Definition 1.2 (The signed determinant).**

$$\forall n \in \mathbb{N},\; \operatorname{A392131}\left(n\right) = \operatorname{Matrix}.\operatorname{det}\left(\operatorname{C}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.A392131` (`✓ std3`).

*Citation.* Stefano Spezia (2026). *OEIS A392131 and A392132: Pell circulant determinant and permanent*. URL: <https://oeis.org/A392131/internal>.

*Commentary.*

OEIS A392131, NAME (unpaginated): “a(n) is the determinant of the n X n circulant matrix whose rows are formed by successively rotating the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.” The COMMENT and four-by-four EXAMPLE specify the initial right rotation used in C. The determinant is signed; the empty determinant is one.

**Definition 1.3 (The permanent).**

$$\forall n \in \mathbb{N},\; \operatorname{A392132}\left(n\right) = \operatorname{Matrix}.\operatorname{permanent}\left(\operatorname{C}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.A392132` (`✓ std3`).

*Citation.* Stefano Spezia (2026). *OEIS A392131 and A392132: Pell circulant determinant and permanent*. URL: <https://oeis.org/A392131/internal>.

*Commentary.*

OEIS A392132, NAME (unpaginated): “a(n) is the permanent of the n X n circulant matrix whose rows are formed by successively rotating the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.” This uses the same C as A392131, and the empty permanent is one.

**Definition 1.4 (The ratio limit).**

$$claim = \left(\forall epsilon \in \mathbb{R},\; (0 < epsilon) \Rightarrow (\exists N \in \mathbb{N},\; (2 \le N) \land (\forall n \in \mathbb{N},\; (N \le n) \Rightarrow (\lvert \frac{\operatorname{A392132}\left(n\right)}{\operatorname{A392131}\left(n\right)} - 1 \rvert < epsilon)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.claim` (`✓ std3`).

*Citation.* Stefano Spezia (2026). *OEIS A392131 and A392132: Pell circulant determinant and permanent*. URL: <https://oeis.org/A392131/internal>.

*Commentary.*

OEIS A392131, FORMULA (unpaginated): “Conjecture: lim_{n->oo} A392132(n)/a(n) = 1.” OEIS A392132, FORMULA (unpaginated): “Conjecture: lim_{n->oo} a(n)/A392131(n) = 1.” Here a(n) denotes the determinant in A392131 and the permanent in A392132. The formula states the epsilon-N meaning of that limit over the tail n≥2, with the signed determinant in the denominator.

**Theorem 1.5 (The ratio tends to one).**

$$\forall epsilon \in \mathbb{R},\; (0 < epsilon) \Rightarrow (\exists N \in \mathbb{N},\; (2 \le N) \land (\forall n \in \mathbb{N},\; (N \le n) \Rightarrow (\lvert \frac{\operatorname{A392132}\left(n\right)}{\operatorname{A392131}\left(n\right)} - 1 \rvert < epsilon)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stefano Spezia (2026). *OEIS A392131 and A392132: Pell circulant determinant and permanent*. URL: <https://oeis.org/A392131/internal>.

*Commentary.*

Normalize C by P(n-1). Its diagonal is one, and an off-diagonal entry with positive modular displacement d is at most (6/5)/(12/5)^d. A cycle is reconstructed from a moved root and its displacement list. The positive displacements sum to a positive multiple of n. Counting all root and composition pairs bounds the total cycle weight by (6n/11)(11/12)^n/(1-(11/12)^n), which tends to zero. The permanent lies between one and the exponential of this weight, while the absolute determinant error is at most the permanent error. Both normalized functions tend to one; their common scalar factor cancels in the ratio.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.A392131`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.A392132`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.C`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.claim`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.result`
- Dependency: [D5/S1/Recurrence/PellCompanionGcd](../../../S1/Recurrence/PellCompanionGcd.md)
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration](../Geometry/CrownOrderPolytopeEnumeration.md)

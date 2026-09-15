# The OEIS A229140 Least-Coordinate Distinctness Conjecture

## Abstract

The values 628 and 673 refute the distinctness conjecture for OEIS A229140.

**Definition 1.1 (The least first coordinate).**

$$\forall m \in \mathrm{Nat},\; \forall x \in \mathrm{Nat},\; (\operatorname{IsLeastCoord}\left(m, x\right)) \Leftrightarrow ((\exists y \in \mathrm{Nat},\; x^{2} + y^{2} = m) \land (\forall u \in \mathrm{Nat},\; (u < x) \Rightarrow (\forall v \in \mathrm{Nat},\; u^{2} + v^{2} \ne m)))$$

*Formalization.* `D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.IsLeastCoord` (`✓ std3`).

*Citation.* Ralf Stephan (2013). *OEIS A229140, Smallest k such that k^2 + l^2 = n-th number expressible as sum of two squares*. URL: <https://oeis.org/A229140>.

*Commentary.*

For natural m and x, IsLeastCoord(m,x) holds exactly when x occurs as the first coordinate of a representation of m by two natural squares and no smaller natural first coordinate occurs in such a representation.

**Definition 1.2 (Distinctness between consecutive zeros).**

$$(claim) \Leftrightarrow (\forall L \in \mathrm{Nat},\; \forall R \in \mathrm{Nat},\; (\operatorname{IsLeastCoord}\left(L, 0\right)) \Rightarrow \left((\operatorname{IsLeastCoord}\left(R, 0\right)) \Rightarrow \left((L < R) \Rightarrow \left((\forall m \in \mathrm{Nat},\; (L < m) \Rightarrow \left((m < R) \Rightarrow (\neg \operatorname{IsLeastCoord}\left(m, 0\right))\right)) \Rightarrow (\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (L < m) \Rightarrow \left((m < R) \Rightarrow \left((L < n) \Rightarrow \left((n < R) \Rightarrow \left((m \ne n) \Rightarrow \left((\operatorname{IsLeastCoord}\left(m, k\right)) \Rightarrow \left((\operatorname{IsLeastCoord}\left(n, k\right)) \Rightarrow (False)\right)\right)\right)\right)\right)\right))\right)\right)\right))$$

*Formalization.* `D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.claim` (`✓ std3`).

*Citation.* Ralf Stephan (2013). *OEIS A229140, Smallest k such that k^2 + l^2 = n-th number expressible as sum of two squares*. URL: <https://oeis.org/A229140>.

*Commentary.*

For every pair L<R whose least first coordinates are zero, with no value strictly between them having least first coordinate zero, any two distinct intermediate representable values cannot have the same least first coordinate.

**Theorem 1.3 (The conjecture fails between 625 and 676).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a229140-stephan-least-coordinate-distinctness-refutation` (refuted) by `D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a229140-stephan-least-coordinate-distinctness-refutation","declaration_gid":"D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ralf Stephan (2013). *OEIS A229140, Smallest k such that k^2 + l^2 = n-th number expressible as sum of two squares*. URL: <https://oeis.org/A229140>.

*Commentary.*

The proof checks the zero witnesses 625=0^2+25^2 and 676=0^2+26^2, the representations 628=12^2+22^2 and 673=12^2+23^2, the exclusion of every first coordinate from 0 through 11 for each intermediate value, and the absence of a natural square strictly between 625 and 676. Thus 628 and 673 share the least first coordinate 12.

## References

- Truth anchor: `D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.IsLeastCoord`
- Truth anchor: `D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.claim`
- Truth anchor: `D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.result`

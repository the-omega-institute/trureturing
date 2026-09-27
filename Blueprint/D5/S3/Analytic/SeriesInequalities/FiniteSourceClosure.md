# Finite Source Closure

## Abstract

The actual recursive image is closed in the critical weighted norm, and the norm closure of finite-source outputs has vanishing antidiagonal tails.

**Theorem 1.1 (Closure of the actual finite-source image).**

$$\forall K \in Type, A \in \mathbb{R}, rho \in \mathbb{R},\; \left(\operatorname{RCLike}\left(K\right) \land \left(0 < A \land \left(0 < rho \land \left(rho < 1 \land A \cdot rho = \left(1 - rho\right)^{2}\right)\right)\right)\right) \Rightarrow \left(\left(\forall a \in \mathbb{N}\to K,\; \left(\forall n \in \mathbb{N},\; \operatorname{norm}\left(\operatorname{a}\left(n\right)\right) \le A\right) \Rightarrow \left(\exists U \in \operatorname{WeightedArray}\left(K\right),\; \operatorname{norm}\left(U\right) \le A \land \left(\forall n \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{U}\left(n, k\right) = \operatorname{smul}\left(rho^{n + k}, \operatorname{extension}\left(a, n, k\right)\right)\right)\right)\right) \land \left(\operatorname{IsClosed}\left(\operatorname{actualImage}\left(A, rho\right)\right) \land \left(\forall U \in \operatorname{WeightedArray}\left(K\right),\; U \in \operatorname{closure}\left(\operatorname{finiteSourceImage}\left(A, rho\right)\right) \Rightarrow \left(U \in \operatorname{actualImage}\left(A, rho\right) \land U \in vanishingTails\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/FiniteSourceClosure.critical_recursive_image_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a real-like field, so that K can be the real or complex numbers. The extension has boundary E(a)(n,0)=a(n) and recurrence E(a)(n,k+1)=E(a)(n+1,k)-sum over j=0,...,k of E(a)(n,j)a(k-j). All source coordinates have norm at most A.

WeightedArray(K) is the space of bounded K-valued functions on pairs of natural numbers, with the supremum norm. An unweighted array T is represented by U(n,k)=rho^(n+k) times T(n,k). Because rho is positive, division by that weight recovers every entry of T. The norm of U is exactly the supremum of rho^(n+k) norm(T(n,k)). In the displayed formula, smul denotes real scalar multiplication.

The set actualImage(A,rho) consists of these weighted outputs of all admissible boundaries. The set finiteSourceImage(A,rho) uses boundaries that vanish beyond some natural index M. Their recursive outputs retain every column; finite input support does not mean finite output support.

For a weighted array U, tail(U,L) is the supremum of norm(U(n,k)) over n+k at least L. The set vanishingTails consists of the arrays for which these suprema tend to zero. All closures and closedness assertions use the supremum norm on WeightedArray(K).

At the critical relation A rho=(1-rho)^2, each finite convolution has mass rho+A sum over i=0,...,k of rho^(i+1) at most one. Strong column induction gives norm(E(a)(n,k)) rho^k at most A for every bounded boundary. Since rho^n is at most one, this constructs the weighted output with norm at most A.

Recover a source from a weighted array by a(n)=rho^(-n) U(n,0). Each recovered source coordinate is continuous in U. Strong induction through the subtraction, multiplication and finite sums in the recurrence proves continuity of each output coordinate in the product topology of the boundary. The actual image is thus exactly the simultaneous closed conditions that the recovered source obeys the amplitude bound and reproduces every coordinate. This proves image closedness without norm continuity of the full source-to-output map.

The tail suprema satisfy tail(U,L) at most norm(U-V)+tail(V,L). A norm approximation within epsilon/2 and a tail bound of epsilon/2 prove that vanishingTails is closed. Finite-source critical tail decay places every finite-source output in this closed set. Closedness of the actual image then gives the stated inclusion for the norm closure. No reverse inclusion or compactness of the actual image is asserted.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/FiniteSourceClosure.critical_recursive_image_closure`
- Dependency: [D5/S3/Analytic/SeriesInequalities/FiniteSourceCriticalTail](FiniteSourceCriticalTail.md)

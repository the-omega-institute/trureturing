# A basis for binary two-by-two trace coordinates

## Abstract

Traces of binary words in two-by-two matrices have a basis of sorted traces and invariant monomials times the commutator-square scalar.

**Theorem 1.1 (The dimension of the coordinate span).**

$$\forall (n: \mathbb{N}), (\operatorname{Module.finrank}\left(\mathbb{C}, \operatorname{Subtype}\left(\lambda (x: ((\operatorname{Fin}\left(2\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) \to (\mathbb{C})) \mapsto (x \in \operatorname{Submodule.span}\left(\mathbb{C}, \operatorname{Set.range}\left(\lambda (i: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\lambda (p: (\operatorname{Fin}\left(2\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) \mapsto (\operatorname{D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation.traceWord}\left(2, 2, n, p, i\right)))\right)\right))\right)\right) = ((n) + (1)) + (\operatorname{Fintype.card}\left(\operatorname{Subtype}\left(\lambda (e: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left((n) + (1)\right))) \mapsto ((((((\operatorname{Fin.val}\left(e\left(0\right)\right)) + (\operatorname{Fin.val}\left(e\left(1\right)\right))) + ((2) \cdot (\operatorname{Fin.val}\left(e\left(2\right)\right)))) + ((2) \cdot (\operatorname{Fin.val}\left(e\left(3\right)\right)))) + ((2) \cdot (\operatorname{Fin.val}\left(e\left(4\right)\right)))) + (4) = n)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords.coordinate_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Claudia De Lazzari; Harshit J. Motwani; Tim Seynnaeve (2022). *The Linear Span of Uniform Matrix Product States*. DOI: [10.3842/SIGMA.2022.099](https://doi.org/10.3842/SIGMA.2022.099). URL: <https://arxiv.org/abs/2204.10363v3>.

*Commentary.*

Let X and Y be complex 2 by 2 matrices. Put s = tr X, t = tr Y, u = det X, v = det Y and w = tr(XY). Give these five invariants weights 1, 1, 2, 2 and 2, respectively, and let Rₖ be the complex span of the invariant monomials of weighted degree k, with zero space for negative k. The coordinate functions of the trace parametrization in sigma22-099.tex, lines 219–220, are traces of binary matrix words. The family used here consists of tr(XᵃYⁿ⁻ᵃ) for 0 ≤ a ≤ n and the functions δsᵉ⁽⁰⁾tᵉ⁽¹⁾uᵉ⁽²⁾vᵉ⁽³⁾wᵉ⁽⁴⁾ of total weighted degree n, where δ = w² − stw + s²v + t²u − 4uv has weight four.

Cayley–Hamilton gives X² = sX − uI and Y² = tY − vI. Its polarized identity gives YX = sY + tX + (w − st)I − XY, and the sandwich identity gives YXY = wY + vX − svI. Induction on the word length therefore writes every word W of length n as aI + bX + cY + dXY, with coefficients in Rₙ, Rₙ₋₁, Rₙ₋₁ and Rₙ₋₂, respectively. The induction starts with I and uses the explicit left-multiplication formulas for X and Y, preserving these degrees.

Set C = XY − YX. Cyclicity of trace gives tr C = tr(XC) = tr(YC) = 0, whereas direct expansion gives tr(XYC) = δ. Applying these identities to the four-term reduction shows tr(WC) belongs to δRₙ₋₂. An adjacent interchange changes tr(AXYB) by tr(BAC). Consequently the difference between two permuted length-n word traces belongs to δRₙ₋₄. Sorting every binary word gives the inclusion of the coordinate span in the sum of the span of tr(XᵃYⁿ⁻ᵃ) and δRₙ₋₄.

To obtain the reverse inclusion, start with the constant-coefficient word combination C. The operations Q ↦ XQ + QX, Q ↦ YQ + QY, Q ↦ XQX, Q ↦ YQY and Q ↦ XYQ + QYX send fC to sfC, tfC, ufC, vfC and wfC. They increase every word length by one, one, two, two and two, respectively. Induction on the sum of the exponents constructs, for each invariant monomial f of weight k, a constant-coefficient combination Q of words of length k + 2 with Q = fC. The matrix identity C² = δI then gives tr(QC) = 2δf. This trace is a combination of length-(k + 4) word traces. Since two is nonzero over the complex numbers, δf belongs to their span. Each tr(XᵃYⁿ⁻ᵃ) is itself a length-n word trace.

The five invariants are algebraically independent. Indeed, any complex quintuple (s,t,u,v,w) with s² ≠ 4u is attained: choose distinct roots λ, μ of z² − sz + u, put X = diag(λ,μ), and set a = (w − μt)/(λ − μ), b = (λt − w)/(λ − μ) and Y = [[a,1],[ab − v,b]]. These matrices have the required invariants. If two polynomials have equal values on every matrix pair, multiply their difference by s² − 4u. The product vanishes on every complex quintuple: on the discriminant-zero set its first factor vanishes, and elsewhere the quintuple is attained. Polynomial extensionality over the infinite field ℂ makes that product the zero polynomial. Since s² − 4u is nonzero and the polynomial ring is a domain, the difference is zero.

Now consider a linear relation among the proposed family. Evaluate it at X = xI and Y = I. Here δ = 0 and tr(XᵃYⁿ⁻ᵃ) = 2xᵃ, so the relation becomes a polynomial in x with distinct exponents a. Its coefficients vanish, eliminating all coefficients of the sorted traces. The remaining relation is δ times a polynomial in the five invariants. Injectivity of polynomial evaluation at matrix pairs makes this product zero as a polynomial. The polynomial δ is nonzero, as its value at (0,0,0,0,1) is one. Cancellation therefore makes the second factor zero, and its distinct monomials have zero coefficients. This proves independence of the entire family.

The two inclusions show that this independent family spans the coordinate space. Every exponent in a weight-(n − 4) monomial is at most n, so it can be represented in Fin (n + 1). Its index set is the disjoint union of Fin (n + 1) and exactly the subtype displayed in the formula. The dimension of the span of a finite independent family is its cardinality; the cardinality of that disjoint union is n + 1 plus the stated exponent count. This argument includes n = 0.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoTraceWords.coordinate_dimension`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation](UniformMPSExpectedDimensionRefutation.md)

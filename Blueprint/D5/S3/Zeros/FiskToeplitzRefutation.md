# A counterexample to Fisk's Question 10

## Abstract

A positive upper bivariate polynomial has a non-Hurwitz coefficient-Toeplitz minor.

**Definition 1.1 (Upper bivariate polynomials).**

$$\forall (f:\operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\operatorname{Real}\right)\right)), \operatorname{Upper}\left(f\right) = (\forall (x:\operatorname{Complex}), \forall (y:\operatorname{Complex}), x \in \operatorname{UpperHalfPlane}.\operatorname{upperHalfPlaneSet} \Rightarrow \left(y \in \operatorname{UpperHalfPlane}.\operatorname{upperHalfPlaneSet} \Rightarrow f.\operatorname{eval}_{2}(\operatorname{Polynomial}.\operatorname{eval}_{2}\operatorname{RingHom}(\operatorname{algebraMap}\left(\operatorname{Real}, \operatorname{Complex}\right),x),y) \ne 0\right))$$

*Formalization.* `D5/S3/Zeros/FiskToeplitzRefutation.Upper` (`✓ std3`).

*Citation.* Steve Fisk (2008). *Questions about determinants and polynomials*. URL: <https://arxiv.org/abs/0808.1850v1>.

*Commentary.*

PDF p. 1: “All polynomials f(x₁,…,x_d) with real coefficients such that f(σ₁,…,σ_d)≠0 for all σ₁,…,σ_d in the open upper half plane.” Here d=2. The carrier is Polynomial (Polynomial ℝ), with x in the coefficient ring and y outermost. Polynomial.eval₂ embeds the real coefficients into ℂ and evaluates at x and y.

**Definition 1.2 (Positive coefficients on the support).**

$$\forall (f:\operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\operatorname{Real}\right)\right)), \operatorname{PositiveUpper}\left(f\right) = (\operatorname{Upper}\left(f\right) \land \forall (i:\operatorname{Nat}), \forall (j:\operatorname{Nat}), ((f).\operatorname{coeff}(j)).\operatorname{coeff}(i) \ne 0 \Rightarrow 0 < ((f).\operatorname{coeff}(j)).\operatorname{coeff}(i))$$

*Formalization.* `D5/S3/Zeros/FiskToeplitzRefutation.PositiveUpper` (`✓ std3`).

*Citation.* Steve Fisk (2008). *Questions about determinants and polynomials*. URL: <https://arxiv.org/abs/0808.1850v1>.

*Commentary.*

PDF p. 1: “P⁺_d = all polynomials in U_d with all positive coefficients.” Every nonzero coefficient (f.coeff j).coeff i is strictly positive; absent monomials have coefficient zero. The condition Upper excludes the zero input.

**Definition 1.3 (Closed left half-plane roots).**

$$\forall (p:\operatorname{Polynomial}\left(\operatorname{Real}\right)), \operatorname{HurwitzStable}\left(p\right) = (\forall (z:\operatorname{Complex}), z \in (p.\operatorname{map}(\operatorname{algebraMap}\left(\operatorname{Real}, \operatorname{Complex}\right))).\operatorname{roots} \Rightarrow z.\operatorname{re} \le 0)$$

*Formalization.* `D5/S3/Zeros/FiskToeplitzRefutation.HurwitzStable` (`✓ std3`).

*Citation.* Steve Fisk (2008). *Questions about determinants and polynomials*. URL: <https://arxiv.org/abs/0808.1850v1>.

*Commentary.*

PDF p. 1: “H₁ = all polynomials with all roots in the closed left half plane.” The real coefficients are mapped to ℂ before taking Polynomial.roots. The zero polynomial has the empty root multiset, so structural zero minors are included. The counterexample minor is nonzero.

**Definition 1.4 (The coefficient matrix (5)).**

$$\forall (f:\operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\operatorname{Real}\right)\right)), \operatorname{toeplitz}\left(f\right) = (\lambda (r:\operatorname{Nat})(c:\operatorname{Nat})\mapsto \operatorname{if} r \le c \operatorname{then} (f).\operatorname{coeff}(c-r) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Zeros/FiskToeplitzRefutation.toeplitz` (`✓ std3`).

*Citation.* Steve Fisk (2008). *Questions about determinants and polynomials*. URL: <https://arxiv.org/abs/0808.1850v1>.

*Commentary.*

Question 10, PDF p. 4: “Suppose f∈P⁺₂, and write f = ∑ f_i(x)y^i. Form the infinite matrix”. Matrix (5) has f₀,f₁,f₂,… in its first row, with each next row shifted one column to the right and zeros below the diagonal. Rows and columns are indexed by ℕ from zero. Polynomial.coeff is zero beyond the degree.

**Definition 1.5 (Ordered finite minors).**

$$\forall (f:\operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\operatorname{Real}\right)\right)), \forall (n:\operatorname{Nat}), \forall (R:\operatorname{Fin}\left(n\right) \to \operatorname{Nat}), \forall (C:\operatorname{Fin}\left(n\right) \to \operatorname{Nat}), \operatorname{minor}\left(f, n, R, C\right) = \operatorname{Matrix}.\operatorname{det}((\lambda (i:\operatorname{Fin}\left(n\right))(j:\operatorname{Fin}\left(n\right))\mapsto \operatorname{toeplitz}\left(f, R(i), C(j)\right)))$$

*Formalization.* `D5/S3/Zeros/FiskToeplitzRefutation.minor` (`✓ std3`).

*Citation.* Steve Fisk (2008). *Questions about determinants and polynomials*. URL: <https://arxiv.org/abs/0808.1850v1>.

*Commentary.*

Question 10, PDF p. 4: “Show that the resulting matrix is totally stable. That is, every minor is a stable polynomial.” The polynomial is the determinant of the selected submatrix. StrictMono row and column maps in claim preserve the source's order and determinant sign. The size-zero determinant is one.

**Definition 1.6 (Question 10).**

$$\operatorname{claim} = (\forall (f:\operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\operatorname{Real}\right)\right)), \operatorname{PositiveUpper}\left(f\right) \Rightarrow \forall (n:\operatorname{Nat}), \forall (R:\operatorname{Fin}\left(n\right) \to \operatorname{Nat}), \forall (C:\operatorname{Fin}\left(n\right) \to \operatorname{Nat}), \operatorname{StrictMono}\left(R\right) \Rightarrow \left(\operatorname{StrictMono}\left(C\right) \Rightarrow \operatorname{HurwitzStable}\left(\operatorname{minor}\left(f, n, R, C\right)\right)\right))$$

*Formalization.* `D5/S3/Zeros/FiskToeplitzRefutation.claim` (`✓ std3`).

*Citation.* Steve Fisk (2008). *Questions about determinants and polynomials*. URL: <https://arxiv.org/abs/0808.1850v1>.

*Commentary.*

Question 10, PDF p. 4: “Suppose f∈P⁺₂, and write f = ∑ f_i(x)y^i. Form the infinite matrix”. Matrix (5) is toeplitz. “Show that the resulting matrix is totally stable. That is, every minor is a stable polynomial.” The quantifiers range over every real bivariate polynomial, every natural size and every two strictly increasing maps Fin n → ℕ. The roots must have nonpositive real part.

**Theorem 1.7 (Question 10 is false).**

$$\neg (\forall (f:\operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\operatorname{Real}\right)\right)), \operatorname{PositiveUpper}\left(f\right) \Rightarrow \forall (n:\operatorname{Nat}), \forall (R:\operatorname{Fin}\left(n\right) \to \operatorname{Nat}), \forall (C:\operatorname{Fin}\left(n\right) \to \operatorname{Nat}), \operatorname{StrictMono}\left(R\right) \Rightarrow \left(\operatorname{StrictMono}\left(C\right) \Rightarrow \operatorname{HurwitzStable}\left(\operatorname{minor}\left(f, n, R, C\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/FiskToeplitzRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steve Fisk (2008). *Questions about determinants and polynomials*. URL: <https://arxiv.org/abs/0808.1850v1>.

*Commentary.*

Take f=(4x+y+1)(x+y+4). Each affine factor has positive imaginary part when x and y do, and all six nonzero coefficients are positive. Rows 0,…,4 and columns 1,…,5 give a tridiagonal minor with determinant 5(x+1)(21x²+33x+21)(13x²−x+13). The complex number (1+15i√3)/26 is a root with real part 1/26. Thus this nonzero minor fails HurwitzStable. The five-by-five determinant factors as b(b²−a)(b²−3a), where a=4x²+17x+4 and b=5x+5.

## References

- Truth anchor: `D5/S3/Zeros/FiskToeplitzRefutation.HurwitzStable`
- Truth anchor: `D5/S3/Zeros/FiskToeplitzRefutation.PositiveUpper`
- Truth anchor: `D5/S3/Zeros/FiskToeplitzRefutation.Upper`
- Truth anchor: `D5/S3/Zeros/FiskToeplitzRefutation.claim`
- Truth anchor: `D5/S3/Zeros/FiskToeplitzRefutation.minor`
- Truth anchor: `D5/S3/Zeros/FiskToeplitzRefutation.result`
- Truth anchor: `D5/S3/Zeros/FiskToeplitzRefutation.toeplitz`

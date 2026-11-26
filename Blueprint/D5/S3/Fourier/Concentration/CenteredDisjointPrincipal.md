# Centered principal coefficient and signed remainder

## Abstract

The constant part of the centered even factors identifies a principal coefficient and a controlled error.

**Theorem 1.1 (Amplitude and squared-norm errors).**

$$\begin{aligned}&|C-P| \le A(H-h)\\&||C|^{2}-|P|^{2}| \le A^{2}(H^{2}-h^{2})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CenteredDisjointPrincipal.centered_principal_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite T and complex phases a(j), exponential parameter c and natural degree d≥|T|, set n=d−|T|, u=c−(sum of a(j) over T)/2, and v=(sum of |a(j)|² over T)/24. Let C be the degree-d coefficient of exp(cx) times the product over T of exp(−a(j)x)−1. Write A for the product of |a(j)| over T, H for the degree-n coefficient of exp(|u|x+v x²), and h=|u|^n/n!. The principal coefficient P is the product of −a(j) over T times u^n/n!.

Extract the linear factors from the centered product. The even factors all have constant coefficient one, so the coefficientwise quadratic majorant remains valid after subtracting one from both products. Multiplication by the centered exponential and extraction of degree n give the difference H−h and the amplitude error. For the square-norm difference, the reverse triangle inequality bounds the difference of norms and the full majorant bounds their sum. Multiplying produces the difference of squares H²−h².

**Theorem 1.2 (Signed coefficient approximation).**

$$\begin{aligned}&|\operatorname{Re}\left([x^{d}y^{d}]Q\right)-\sum_{T \subseteq s,|T| \le d}(-1)^{|T|}|\operatorname{P}\left(T\right)|^{2}| \le\\&\quad\sum_{T \subseteq s,|T| \le d}\operatorname{A}\left(T\right)^{2}(\operatorname{H}\left(T\right)^{2}-\operatorname{h}\left(T\right)^{2})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CenteredDisjointPrincipal.mixed_centered_principal_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite ambient set s, choose c to be the sum of its phases and let Q be the disjoint product of exp(a(j)x)+exp(conj(a(j))y)−1. For each subset T with |T|≤d, define the corresponding P(T), A(T), H(T) and h(T) by the local theorem.

The exact mixed coefficient is the alternating sum of squared overlap norms. Subtract the alternating sum of squared principal norms and apply the triangle inequality termwise. This gives the sum of the local squared error bounds. The actual high-degree arithmetic estimate for zeta ordinates still requires control of the subset centers and the signed principal sum.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CenteredDisjointPrincipal.centered_principal_remainder`
- Truth anchor: `D5/S3/Fourier/Concentration/CenteredDisjointPrincipal.mixed_centered_principal_error`
- Dependency: [D5/S3/Fourier/Concentration/CenteredDisjointCharacterBound](CenteredDisjointCharacterBound.md)

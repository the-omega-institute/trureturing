# Compression from the original regular actions

## Abstract

The original nonassociative Hilbert-space product defines an exact compression in its regular-action norm.

Let H be any finite-dimensional complex Hilbert space with a conjugate-linear additive involution. The data consist of the original continuous complex-bilinear product mu, its strict two-sided unit e with Hilbert norm one, the reversal identity for the involution, and the Hilbert-adjoint identity adjoint(L_x)=L_(star x). Assume the bilinear norm is at most M, M is at least one, and the original Hilbert associator norm is at most delta times the three input norms, with delta nonnegative.

Define p(x) as the original Hilbert operator norm of L_x. The auxiliary Banach space is the range of x mapped to L_x, with the inherited operator norm. Evaluation at e proves injectivity and identifies H linearly and continuously with this range. Actual left and right multiplication are transported through this identification. For P and Q, set T=L_P R_Q+R_Q L_P-identity and let C(P,Q) be the transport to H of one half of the sum of identity and T times the Taylor inverse-square-root series evaluated at T squared minus identity. No associative multiplication or C*-algebra instance is added to H, and the Hilbert structure on H is retained.

**Theorem 1.1 (Exact idempotence from the actual product defects).**

$$\forall P,Q\in H, \forall \tau \in \mathbb{R}, P^{*}=P, Q^{*}=Q, 0\le \tau, \tau+M \delta \le \frac{1}{1024}, \operatorname{p}\left(\operatorname{mu}\left(P, P\right)-P\right)\le \tau, \operatorname{p}\left(\operatorname{mu}\left(Q, Q\right)-Q\right)\le \tau \implies \operatorname{C}\left(P, Q\right)^{2}=\operatorname{C}\left(P, Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For self-adjoint P and Q with p(mu(P,P)-P) and p(mu(Q,Q)-Q) at most tau, assume tau is nonnegative and tau+M delta is at most 1/1024. The norm of the square of T=L_P R_Q+R_Q L_P-identity minus identity is at most 512(tau+M delta) in the auxiliary operator algebra. Thus the inverse-square-root Taylor series converges. One half of the sum of identity and T times that series is exactly idempotent, and conjugation by the regular-range equivalence gives an exactly idempotent continuous linear map on the original H.

The approximate-projection bounds, left/right square defects and commutator defect are derived from mu. The mixed corner is defined as the range of this corrected map. The construction follows Kitaev, Almost-idempotent quantum channels and approximate C*-algebras, arXiv:2405.02434v2, sections 3 and 7. It is a prerequisite for the full-corner construction of Lemma 9.4; it does not establish corner saturation, an exact matrix action, compatible columns, or the block extension.

**Theorem 1.2 (The regular norm respects star reversal).**

$$\forall x, y\in H, \operatorname{p}\left(\operatorname{mu}\left(y^{*}, x^{*}\right)\right)= \operatorname{p}\left(\operatorname{mu}\left(x, y\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.p_star_mul_rev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality is obtained from the original involution reversal law and adjoint invariance of the operator norm. It is used by the transported right-action estimates.

**Theorem 1.3 (The two actual regular actions have controlled defects).**

$$\forall P, Q\in H, \forall \tau \in \mathbb{R}, 0\le \tau, \operatorname{p}\left(\operatorname{mu}\left(P, P\right)-P\right)\le \tau, \operatorname{p}\left(\operatorname{mu}\left(Q, Q\right)-Q\right)\le \tau \implies (\operatorname{norm}\left(\operatorname{left}\left(P\right)*\operatorname{left}\left(P\right)-\operatorname{left}\left(P\right)\right)\le M \delta \operatorname{p}\left(P\right)^{2}+(1+\delta) \tau \land \operatorname{norm}\left(\operatorname{right}\left(Q\right)*\operatorname{right}\left(Q\right)-\operatorname{right}\left(Q\right)\right)\le M \delta \operatorname{p}\left(Q\right)^{2}+(1+\delta) \tau \land \operatorname{norm}\left(\operatorname{left}\left(P\right)*\operatorname{right}\left(Q\right)-\operatorname{right}\left(Q\right)*\operatorname{left}\left(P\right)\right)\le M \delta \operatorname{p}\left(P\right) \operatorname{p}\left(Q\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.two_piece_defects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative tau and actual p-defects of P and Q bounded by tau, the left and right transported actions have square defects bounded by M delta p(P)^2 plus (1+delta) tau and M delta p(Q)^2 plus (1+delta) tau. Their commutator is bounded by M delta p(P)p(Q). All three estimates are derived from the same original product.

**Theorem 1.4 (The actual compression is close to its midpoint).**

$$\forall P, Q\in H, \forall \tau \in \mathbb{R}, P^{*}=P, Q^{*}=Q, 0\le \tau, \tau+M \delta\le \frac{1}{1024}, \operatorname{p}\left(\operatorname{mu}\left(P, P\right)-P\right)\le \tau, \operatorname{p}\left(\operatorname{mu}\left(Q, Q\right)-Q\right)\le \tau \implies \operatorname{norm}\left(\operatorname{regularCompression}\left(P, Q\right)-\frac{1}{2} \cdot (1+\operatorname{cornerInvolution}\left(P, Q\right))\right)\le \frac{19}{2} \cdot \operatorname{norm}\left(\operatorname{inverseSqrt}\left(\operatorname{cornerInvolution}\left(P, Q\right)^{2}-1\right)-1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.regularCompression_closeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated self-adjointness, p-defect, nonnegativity and smallness conditions, the norm of the actual corner involution is at most 19. The generic Taylor-tail estimate therefore gives the displayed quantitative midpoint bound for the same original-product compression.

**Theorem 1.5 (Closeness to both actual bracketings).**

$$\operatorname{p}\left(\operatorname{C}\left(P, Q, x\right)-\operatorname{mu}\left(P, \operatorname{mu}\left(x, Q\right)\right)\right)\le4866 \cdot \tau+M\delta \cdot \operatorname{p}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_closeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r=tau+M delta. For self-adjoint P and Q, nonnegative tau, r at most 1/1024, and actual p-projection defects at most tau, both p(C(P,Q)x-mu(P,mu(x,Q))) and p(C(P,Q)x-mu(mu(P,x),Q)) are at most 4866 r p(x), for every x. The Taylor tail is at most the square defect, hence at most 512 r. The midpoint displacement is at most 4864 r and the actual commutator contributes at most 2 r for either bracketing.

**Theorem 1.6 (The original Hilbert operator bounds).**

$$\operatorname{norm}\left(\operatorname{C}\left(P, Q\right)-\operatorname{L}\left(P\right) \cdot \operatorname{R}\left(Q\right)\right)\le4866 \cdot \tau+M\delta \cdot M$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_closeness_hilbert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same self-adjointness, nonnegative tau, r at most 1/1024 and actual p-projection-defect hypotheses, both Hilbert operator norms of C(P,Q)-L_P R_Q and C(P,Q)-R_Q L_P are at most 4866 M r. The additional M comes from norm(x) at most p(x) at most M norm(x). The regular and original Hilbert operator norms are not identified.

**Theorem 1.7 (Star exchanges the actual corner labels).**

$$\operatorname{star}\left(\operatorname{C}\left(P, Q, x\right)\right)=\operatorname{C}\left(Q, P, \operatorname{star}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, star(C(P,Q)x)=C(Q,P)(star(x)) for every x. The actual star reversal interchanges left and right multiplication. Its p-isometry gives a bounded real-linear involution on the regular range, and the convergent Taylor correction preserves this intertwining. This is star covariance, with no assertion that a mixed compression is positive or an orthogonal projection.

**Theorem 1.8 (The actual complementary two-piece decomposition).**

$$\operatorname{p}\left(\operatorname{C}\left(P, Q, x\right)+\operatorname{C}\left(P, e-Q, x\right)-\operatorname{C}\left(P, e, x\right)\right)\le14598 \cdot \tau+M\delta \cdot \operatorname{p}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_two_piece` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, p(C(P,Q)x+C(P,e-Q)x-C(P,e)x) is at most 14598 r p(x), for every x. The actual unit is star fixed, e-Q has exactly the same projection defect as Q, and the uncorrected bracketings add exactly. Applying the three quantitative compression bounds gives the decomposition error. This does not identify the two corrected ranges as an exact direct sum.

**Theorem 1.9 (The actual compatible-corner product has approximate outer support).**

$$\operatorname{p}\left(\operatorname{C}\left(P, R, \operatorname{mu}\left(x, y\right)\right)-\operatorname{mu}\left(x, y\right)\right)\le260000 \cdot (\tau+M\delta) \cdot \operatorname{p}\left(x\right) \cdot \operatorname{p}\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.corner_product_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same original finite-dimensional complex Hilbert product, let P, Q and R be self-adjoint, let tau be nonnegative, set r=tau+M delta, assume r at most 1/1024, and bound all three actual p-projection defects by tau. For every x in range C(P,Q) and y in range C(Q,R), the displayed estimate holds with the universal numerical constant 260000. No orthogonality of the labels, exact corner closure, associativity of H, scalar pairing, or saturation is assumed.

Exact idempotence makes x fixed by C(P,Q). The bracketing estimate and the original associator bound imply p(mu(P,x)-x) at most 24354 r p(x). Star reversal gives the corresponding right support bound for y and R. The product estimate p(mu(a,b)) at most 2 p(a)p(b), valid at this scale, then controls the five differences through mu(P,mu(mu(x,y),R)), mu(P,mu(x,mu(y,R))), mu(P,mu(x,y)), and mu(mu(P,x),y). Their coefficients sum to 253282, bounded by 260000. M enters only through r in this regular-norm estimate. The result is approximate product support; exact closure, minimal-corner scalar pairing, positivity, dimension transfer and column saturation require further arguments.

**Theorem 1.10 (The actual compressed square detects nonzero mixed-corner vectors).**

$$\frac{\operatorname{norm}\left(x\right)^{2}}{2}\le\operatorname{Re}\left(\operatorname{inner}\left(e, \operatorname{C}\left(Q, Q, \operatorname{mu}\left(x^{*}, x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.corner_square_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Retain the same original Hilbert product and all the self-adjointness, projection-defect, nonnegative-tau and r at most 1/1024 hypotheses for P and Q. If additionally 520000 r M^2 is at most one, then every x in range C(P,Q) satisfies the displayed lower bound, and C(Q,Q)mu(star(x),x)=0 if and only if x=0. The norm here is the original Hilbert norm, and e is the original strict unit of Hilbert norm one.

Star reversal places star(x) in the reversed actual corner. Applying the compatible-corner support estimate bounds the p-distance of the compressed square from the original square by 260000 r p(x)^2. The original adjoint law and strict right unit give exactly inner(e,mu(star(x),x))=inner(x,x). Cauchy-Schwarz bounds the expectation error by the same regular-norm error. The comparison p(x) at most M norm(x) gives the stated half-norm lower bound at the additional scale, and hence detects zero exactly. The M^2 factor is explicit; no M-independent Hilbert positivity radius is asserted. This result does not define the scalar coefficient b(Y,X)t_Q, prove that the actual diagonal corner is one-dimensional, or establish column saturation or a block extension.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_closeness`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_closeness_hilbert`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_idempotent`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_star`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_two_piece`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.corner_product_support`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.corner_square_nondegenerate`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.p_star_mul_rev`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.regularCompression_closeness`
- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.two_piece_defects`
- Dependency: [D5/S3/Quantum/Algebra/Approximate/Compression](Compression.md)

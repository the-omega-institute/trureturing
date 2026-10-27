# RegularReadInverse

## Abstract

A local inverse in all eight original source coordinates

The original read pair is originalPM(W)=(p(W),f_M(W)), with the second read taken after the actual eighth M action. The independent source coordinates of an original world are sourceChart(W)=(r/b,b). Its sourceCoordinates vector consists of r,b,r(1-r)/b,d and the four ordinary coefficients of its one whole gain polynomial. The norm on this Fin 8 function space is exactly the sup norm of those eight entries.

At any source point in the displayed strip, the actual read derivative is invertible and chartRead is analytic. The inverse function theorem produces an open partial homeomorphism e whose forward function is chartRead and whose source contains the source point. Its inverse is analytic at the center image. Composing that inverse with chartSource gives H(q)=chartSource(e inverse(q)).

Choose a positive-radius ball A about the actual read image with compact closure inside the inverse target and inside the analytic neighborhoods of both the inverse and H. The product norm makes A a convex open rectangle in the two read coordinates. Analyticity makes the derivative of H continuous on its compact closure. A finite bound for that derivative and the convex mean value inequality give a positive finite Lipschitz constant L for H on A.

The set localWorlds(e,A) includes every original parent world whose r,b lie in the same closed source strip, whose independent source coordinates lie in the source of e, and whose actual read pair lies in A. The reconstructed center chartWorld(x) belongs to this set. Original parent uniqueness identifies each such world with chartWorld(sourceChart(W)). Thus H returns its complete original source vector. Every pair of these worlds, including pairs at different acquired bases, satisfies the source sup norm estimate with the same L.

This is a local inverse result at arbitrary source points of the strip. It does not identify a selected algebraic lift with a determinantal critical world. It also does not establish remote-branch control, exhaustion of an entire original preimage, separation by 89, or a uniform bound for all common future words on that entire preimage.

**Theorem 1.1 (The actual local source inverse).**

Lean statement: `D5/S3/Observer/CubicGain/RegularReadInverse.actual_local_source_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RegularReadInverse.actual_local_source_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x=(t,b) with 9005/10000 <= tb <= 9006/10000 and 12758/100000 <= b <= 12759/100000, there exist an open partial homeomorphism e, a real epsilon>0 and a positive nonnegative real L. The forward map of e is chartRead and x belongs to its source. The ball A of radius epsilon about chartRead(x) is open and convex, its closure is compact and contained in the target of e, and both e inverse and H=chartSource composed with e inverse are real analytic on a neighborhood of that closure. The norm of the derivative of H is at most L throughout the closure, and H is L-Lipschitz on A. The world chartWorld(x) belongs to localWorlds(e,A). For every W in localWorlds(e,A), H(originalPM(W))=sourceCoordinates(W). Every two W,W' in this same set obey norm(sourceCoordinates(W)-sourceCoordinates(W')) <= L norm(originalPM(W)-originalPM(W')).

## References

- Truth anchor: `D5/S3/Observer/CubicGain/RegularReadInverse.actual_local_source_inverse`
- Dependency: [D5/S3/Observer/CubicGain/RegularReadJacobian](RegularReadJacobian.md)

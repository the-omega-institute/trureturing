# Count the nonzero quadratic section

## Abstract

Quantized quadratic values bound the original middle-lattice section after its zero directions are removed.

**Theorem 1.1 (The shortest direction may be a null line).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiQuadraticMiddleCount.quadratic_nonzero_middle_box_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiQuadraticMiddleCount.quadratic_nonzero_middle_box_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c and q be positive integers and let X,Y,H be positive reals with H squared equal to XY. Choose an actual reduced basis B of the original integer lattice c divides w*z2-t*z1. Let Q be an integer-valued homogeneous function of degree two, zero at zero, whose values on that lattice are divisible by q. Suppose |Q(z)| is at most M times [(Y/X)z1 squared+(X/Y)z2 squared], where M is nonnegative. Any finite set s in the original rectangle |z1|<=X, |z2|<=Y, contained in this lattice and avoiding Q=0, satisfies card(s)<=1+4H sqrt(M/q)+24XY/c.

Write sigma for the weighted length of B.R. Every point has reduced coordinates |i|<=2H/sigma and |j|<=2H sigma/c. Count the noncentral rows by erasing zero from the j interval before multiplying the interval counts. A nonempty section supplies sigma<=2H, so these rows contribute at most 24XY/c. On the central line, an actual counted point forces Q(B.R) to be nonzero. Divisibility gives q<=|Q(B.R)|<=M sigma squared, while homogeneity transfers the original box bound to |i|<=2H sqrt(M/q). This counts the central line by 1+4H sqrt(M/q). If B.R is a null direction, the entire central line is absent.

The theorem includes split quadratic forms with rational zero lines, the zero function and empty sections. It assumes the explicit arithmetic value quantization and weighted bound, and proves the count rather than assuming a counting supplier. The argument combines the existing literal-lattice reduction with the new separation of the shortest null direction. It does not assume a positive definite quadratic form.

Research use: the proposed physical-kernel average supplies c=p squared, q=p to the power 6-j and M of order (XY) squared divided by p to the power 3+j. Both j=3 and j=4 then have the same boundary scale (XY) to the power 3/2 divided by p to the power 9/2. Those arithmetic supplies, the two-root cover, and the global original six-word count are separate obligations. This module alone does not improve the delivered alpha<26/7 theorem or settle the nonsplit branch. The motivating ordinary lattice argument was proposed through the oracle broker; the kernel-checked implementation is by Codex.

Source-bound four-slot registration remains incomplete under issue #31176, https://github.com/the-omega-institute/trureturing/issues/31176. The Reg mirror retains a full-telescope typed positive-law attempt; it is not a Contract.Registration or declared_validated evidence.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiQuadraticMiddleCount.quadratic_nonzero_middle_box_count`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage](PascadiOriginalWeightAverage.md)

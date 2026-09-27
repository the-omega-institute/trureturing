# Conjugate Hankel Signature

## Abstract

Weighted Hankel signature equals the signed count of real-node weights.

**Theorem 1.1 (The real-node signature formula).**

$$sigPos(H)-sigNeg(H)=sumRealNodeSigns(s,w)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ConjugateHankelSignature.weighted_hankel_signature` (`✓ std3`). ∎

*Citation.* Saugata Basu; Richard Pollack; Marie-Françoise Roy (2003). *Algorithms in Real Algebraic Geometry*. DOI: [10.1007/978-3-662-05355-3](https://doi.org/10.1007/978-3-662-05355-3). URL: <https://www.math.purdue.edu/~sbasu/bpr-posted1.pdf>.

*Commentary.*

Let s be any finite set of complex numbers closed under conjugation, and let d be any natural number at least the cardinality of s. Assign each node z a complex weight w(z), with w(conjugate z) equal to conjugate w(z). For i,j in Fin d, define H(i,j) as the real part of the sum over z in s of w(z) times z to the power i+j. This real Hankel matrix is symmetric.

The positive index minus the negative index of the actual quadratic form associated to H equals the sum over real nodes r in s of the sign of the real part of w(r). Here the sign is one for a positive real part, minus one for a negative real part, and zero when that real part vanishes. The equality is an integer equality; the two natural inertia indices are individually cast to integers before subtraction. Conjugation compatibility makes every real-node weight real.

Real coefficient vectors evaluate on s to conjugation-compatible value vectors. Lagrange interpolation on the distinct nodes produces a polynomial of degree less than the cardinality of s for every such vector. Conjugating the polynomial preserves its degree and values, so interpolation uniqueness makes its coefficients real. Padding with zero coefficients gives surjective evaluation for every admissible d. A linear right inverse separates the value space from the evaluation kernel, on which the form is zero.

A compatible value vector is determined by one real value at each real node and one complex value at each node in the upper half-plane. The lower half-plane values are their conjugates. The form becomes the sum of real scalar squares weighted by w(r), together with the real parts of 2w(z) times a complex square. For a nonzero complex coefficient, a complex square root followed by real and imaginary coordinates transforms the corresponding two-dimensional real form into one positive square and one negative square. A zero coefficient instead gives a zero block.

The diagonal model adds zero coordinates for the evaluation kernel. Its positive and negative indices count the positive and negative diagonal weights. Each nonreal pair contributes equally to those indices and cancels from their difference; precisely the signed real-node weights remain. Zero weights, singular matrices, the empty node set, admissible dimension zero, and all extra polynomial coordinates are included. No polynomial-root enumeration, squarefreeness, or positivity assumption is needed.

## References

- Truth anchor: `D5/S3/QuadraticForms/ConjugateHankelSignature.weighted_hankel_signature`
- Dependency: [D5/S3/Constants/NewtonHankelRealRootCriterion](../Constants/NewtonHankelRealRootCriterion.md)

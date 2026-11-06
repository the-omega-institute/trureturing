# An exceptional-19 non-Boolean physical intersection family

For every natural `r`, put `d = 18*r + 12`, `B = 2^d`, `g = B - 1`, and
`t = g*(2*B - 3)`.  The literal physical labels whose `Nat.testBit` is set in
`Q = (B^2+B+1)/19` and in `2Q` each have integer source sum zero.  Their
physical intersection has

`511 * intersectionSum = -(B-1) * (80*B^2 - 1111*B + 1724)`

and is strictly negative.  The theorem keeps every `Fin (3*d)` occurrence,
including `r = 0`; it uses the original `actualSource` and literal bit filters.

The intersection statement is the non-Boolean consequence: two physical zero
families can have a strictly nonzero (negative) physical intersection.  The
usual all-`d` intersection-closure criterion is only an application after the
displayed arithmetic and the source-width hypotheses; it is not claimed here.

Lean anchor: `D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean.exceptional19_zero_pair_intersection`.

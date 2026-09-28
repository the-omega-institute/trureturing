# Polynomial reflection and generating-series numerators

## Theorem: Reflection gives a palindromic numerator

Let n be a nonnegative integer and let p be a real polynomial of degree
at most n. Suppose p(0) = 1 and p(-1-x) = (-1)^n p(x) for every real x.
Then there is a polynomial R of degree exactly n such that

    (sum over k >= 0 of p(k) z^k) (1-z)^(n+1) = R(z),
    coefficient(R, j) = coefficient(R, n-j) for 0 <= j <= n.

Proof. Expand p in the basis b_i(x) = binomial(x+i, i), for
0 <= i <= n. The series for b_i(k) is (1-z)^(-i-1), so multiplying
the series for p(k) by (1-z)^(n+1) produces a polynomial R of degree
at most n. Under x -> -1-x, the basis polynomial b_i evaluates at k
to (-1)^i binomial(k, i). Its generating series is
(-1)^i z^i (1-z)^(-i-1). Hence the numerator of the reflected
polynomial is (-1)^n z^n R(1/z). The assumed reflection identity makes
this numerator also (-1)^n R(z), so R(z) = z^n R(1/z). The constant
coefficient of R is p(0) = 1, and reciprocity makes its coefficient at
z^n equal to one. Thus its degree is exactly n.

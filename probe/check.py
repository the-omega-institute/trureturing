"""Independent exact-arithmetic probe for Brietzke (2024), Section 5."""
import json
from math import comb


def d(n, k):
    if k < 0 or k > n:
        return 0
    numerator = (k + 1) * comb(2 * (n + 1), n - k)
    quotient, remainder = divmod(numerator, n + 1)
    assert remainder == 0, ("inexact division", n, k, remainder)
    return quotient


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def main():
    printed = [[1], [2, 1], [5, 4, 1], [14, 14, 6, 1],
               [42, 48, 27, 8, 1], [132, 165, 110, 44, 10, 1]]
    computed = [[d(n, k) for k in range(n + 1)] for n in range(6)]
    assert computed == printed
    for n in range(300):
        assert sum(d(n, 5*j+1) - d(n, 5*j+2) for j in range(n+1)) == fib(2*n), (21, n)
        assert sum(d(n, 5*j) - d(n, 5*j+3) for j in range(n+1)) == fib(2*n+1), (22, n)
        assert sum(d(n, 4*j) - d(n, 4*j+2) for j in range(n+1)) == 2**n, (15, n)
        for k in range(n + 3):
            assert d(n+1, k) == d(n, k-1) + 2*d(n, k) + d(n, k+1), ("recurrence", n, k)
    assert d(1, 3) == 0
    print(json.dumps({"rows": computed, "anchors_21_22": "pass: 0 <= n < 300",
                      "conj15_range": "pass: 0 <= n < 300", "recurrence": "pass: 0 <= n < 300, 0 <= k < n+3",
                      "division": "exact on every evaluated in-range input", "d_1_3": d(1, 3)}, indent=2))


if __name__ == "__main__":
    main()

"""Check the indexing and specialization of the cited Chebyshev identity.

All arithmetic is exact. These finite checks supplement the published general
identity; they are not a proof for unbounded n.
"""
import json
from check import d


def main():
    # S_m(x) = U_m(x/2), with polynomial coefficients stored low degree first.
    polynomials = [[1], [0, 1]]
    for m in range(1, 121):
        nxt = [0] + polynomials[m]
        for j, a in enumerate(polynomials[m-1]):
            nxt[j] -= a
        polynomials.append(nxt)
    for n in range(61):
        total = [0] * (2*n + 2)
        for k in range(n + 1):
            for j, a in enumerate(polynomials[2*k+1]):
                total[j] += d(n, k) * a
        assert total == [0] * (2*n+1) + [1], n

    # Evaluate in Z[s]/(s^2-2), using pairs a+b*s.
    values = [(1, 0), (0, 1)]
    for m in range(1, 9):
        a, b = values[m]
        c, e = values[m-1]
        values.append((2*b-c, a-e))
    assert values[8:10] == values[0:2]
    assert [values[k] for k in [1, 3, 5, 7]] == [(0, 1), (0, 0), (0, -1), (0, 0)]
    print(json.dumps({"polynomial_identity": "pass for 0 <= n <= 60",
                      "specialization_ring": "Z[s]/(s^2-2)",
                      "S_0_through_S_9": values,
                      "odd_weights_divided_by_s": [1, 0, -1, 0],
                      "recurrence_state_repeats_after_8": True}, indent=2))


if __name__ == "__main__":
    main()

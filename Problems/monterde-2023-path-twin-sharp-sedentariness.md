---
slug: monterde-2023-path-twin-sharp-sedentariness
bibkey: monterde2023sedentariness
doi: 10.1016/j.disc.2025.114959
url: https://arxiv.org/abs/2401.00362v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.result
---

# The twin end vertex of P'_9 is not sharply 1/9-sedentary

## Problem

H. Monterde (arXiv:2401.00362, math.CO and quant-ph; Discrete Math. 349(4)
(2026) 114959) studies the quantum walk `U(t) = e^{itA}` of a graph with
adjacency matrix `A`. A vertex `u` is sharply `C`-sedentary if
`inf_{t>0} |U(t)_{u,u}| = C` with `0 < C ≤ 1`. The graph `P_n'` is the path
`1, …, n` with an added vertex `n + 1` joined to vertex `2`, so that `1` and
`n + 1` are non-adjacent twins. Example 18 proves `|U(t)_{1,1}| ≥ 1/n` for odd
`n` and states:

> We conjecture that $u$ is sharply $(\frac{1}{n})$-sedentary in $P_n'$ for
> all odd $n\geq 5$.

Issue #11607 fixes the reading: `U(t) = e^{itA} = hamiltonianPropagator A (−t)`,
`u = 1`, and the claim is `inf_{t>0} |U(t)_{1,1}| = 1/n` for every odd
`n ≥ 5`. The result refutes it at `n = 9`.

## Motivation

A sedentary vertex keeps a bounded-below part of the walk's amplitude for all
time. The paper's bound `1/n` comes from the weight of vertex `1` on the zero
eigenspace, and the paper proves that it is the infimum for `n = 5`. The frozen
declaration `D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.result` shows
that the infimum is larger for `n = 9`.

## Gap

Issue #11607 preregisters the reading, the witness and the literature check.
arXiv v1 is the only version and keeps the conjecture. The arXiv sources of
the later quantum-walk papers that mention sedentariness (2404.16654,
2502.08103, 2504.11585, 2505.07982, 2510.05306, 2601.13318, 2601.18964,
2603.20977, 2604.20700, 2609.10713) were searched; arXiv:2601.18964 repeats the
case `n = 5` and arXiv:2510.05306 uses `P_n'` only through sedentariness, and
none states or refutes the conjecture.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. For real `θ` with `cos 9θ = 0`, the vector
   `x(θ) = (1/2, cos θ, cos 2θ, …, cos 8θ, 1/2)` satisfies
   `A x(θ) = 2cos θ · x(θ)`, and `e_1 − e_10` lies in the kernel of `A`.
2. With `θ_k = (2k + 1)π/18` (`k = 0, …, 8`),
   `e_1 = (e_1 − e_10)/2 + (1/9) Σ_k x(θ_k)`, because Mathlib's closed form
   `sin(a/2) Σ_{k<9} cos(ak + b) = sin(9a/2) cos(4a + b)` with `a = mπ/9`,
   `b = mπ/18` gives `Σ_k cos(m θ_k) = 0` for `m = 1, …, 8`.
3. The frozen `exp_mulVec_of_eigenvector` gives
   `U(t)_{1,1} = 1/2 + (1/18) Σ_k e^{2it cos θ_k}`; pairing `θ_k` with
   `π − θ_k` gives the real value
   `5/9 + (1/9)(cos αt + cos √3 t + cos βt + cos γt)` with
   `α = 2cos(π/18)`, `β = 2cos(5π/18)`, `γ = 2cos(7π/18)`.
4. `α = β + γ` because `cos(5π/18) + cos(7π/18) = 2cos(π/3)cos(π/18)`, and
   `cos a + cos b + cos(a + b) ≥ −3/2` because
   `(1 + cos a + cos b)² + (sin a − sin b)² = 3 + 2(cos a + cos b + cos(a + b))`.
5. Hence `|U(t)_{1,1}| ≥ 5/9 − (1/9)(3/2 + 1) = 5/18` for all `t`, so the
   infimum is at least `5/18 > 1/9`.

## Falsifier

The answer would change if the claim were only the lower bound
`|U(t)_{1,1}| ≥ 1/n`, which the paper proves. It does not depend on the sign
convention of `U(t)`: for real symmetric `A`, `e^{−itA}` is the entrywise
conjugate of `e^{itA}`.

## Evidence

Exact SymPy arithmetic (issue #11607) gives
`det(zI − A(P_9')) = z²(z² − 3)(z⁶ − 6z⁴ + 9z² − 3)` and the resolvent entry
`((zI − A)^{−1})_{1,1} = 5/(9z) + z/(9(z² − 3)) + z(z² − 1)(z² − 3)/(3(z⁶ − 6z⁴ + 9z² − 3))`.
NumPy on 400 000 times in `[0, 4000]` gives `min |U(t)_{1,1}| = 0.27785` for
`n = 9`; as a positive control, the same code gives `0.200001` for `n = 5`,
where the paper proves that the infimum is `1/5`.

The rank statements in the Triage section are reproduced by the following
exact program (Python with SymPy). Each `2cos(mπ/N)` is written as
`ζ^m + ζ^(−m)` with `ζ = e^{iπ/N}` and reduced modulo the cyclotomic polynomial
`Φ_{2N}`; integer relations are found by integer row reduction of the
coefficient vectors.

```python
# Exact Q-linear relations among the positive support eigenvalues 2cos((2k+1)π/(2n)) of P_n'.
# Each 2cos(mπ/N) = ζ^m + ζ^(-m) with ζ = e^{iπ/N} is reduced modulo the cyclotomic polynomial
# Φ_{2N}; the coefficient vectors are integer, and integer relations are found by exact
# integer row reduction of [Vᵀ | I].
from sympy import cyclotomic_poly, symbols, Poly, totient
x = symbols('x')

def vec(m, N):
    phi = Poly(cyclotomic_poly(2 * N, x), x)
    d = phi.degree()
    p = Poly(x ** (m % (2 * N)) + x ** ((-m) % (2 * N)), x).rem(phi)
    c = p.all_coeffs()[::-1]
    return [int(c[i]) if i < len(c) else 0 for i in range(d)]

def integer_relations(rows):
    # rows: list of integer vectors v_k; returns a Z-basis of {c : Σ c_k v_k = 0}
    m = len(rows)
    A = [list(r) + [1 if j == i else 0 for j in range(m)] for i, r in enumerate(rows)]
    d = len(rows[0])
    r = 0
    for col in range(d):
        while True:
            piv = [i for i in range(r, m) if A[i][col] != 0]
            if not piv:
                break
            i0 = min(piv, key=lambda i: abs(A[i][col]))
            A[r], A[i0] = A[i0], A[r]
            done = True
            for i in range(r + 1, m):
                if A[i][col]:
                    q = A[i][col] // A[r][col]
                    A[i] = [a - q * b for a, b in zip(A[i], A[r])]
                    if A[i][col]:
                        done = False
            if done:
                r += 1
                break
    return [row[d:] for row in A[r:]]

def analyse(n):
    N = 2 * n
    ms = [2 * k + 1 for k in range(n) if 2 * k + 1 < n]          # positive eigenvalues
    rel = integer_relations([vec(m, N) for m in ms])
    odd = any(sum(c) % 2 for c in rel)
    return len(ms), len(ms) - len(rel), odd, rel

for n in range(5, 41, 2):
    m, rank, odd, rel = analyse(n)
    print(n, 'positive eigenvalues', m, 'rank', rank,
          'independent' if rank == m else ('relation with odd coefficient sum' if odd else 'relations, all even sums'))
# n = 9: eigenvalues 2cos(π/18), 2cos(3π/18) = √3, 2cos(5π/18), 2cos(7π/18)
m, rank, odd, rel = analyse(9)
print('n=9 relations (coefficients of 2cos(π/18), √3, 2cos(5π/18), 2cos(7π/18)):', rel)
```

For odd `5 ≤ n ≤ 39` it prints the number of positive support eigenvalues,
their rank over `ℚ`, and whether an integer relation with odd coefficient sum
exists; for `n = 9` it prints the single relation `(−1, 0, 1, 1)` among
`2cos(π/18)`, `√3`, `2cos(5π/18)`, `2cos(7π/18)`, that is `α = β + γ`. As a
positive control, `n = 5` (the paper's sharp case) is reported independent.

The canonical source is
`D5/S3/Quantum/Dynamics/PathTwinSharpSedentariness.lean`. Its public
declarations are `pathTwin`, `SharplySedentary`, `claim` and `result`. The
frozen module state has statement identity `sha256:9b7669a62d8d4da32d0aa2f2710152b77d14c34940e82b630de86320fa9be5da`. The result
declaration has statement identity `sha256:b5a176bb8b77439efcfa4840cfdb32847d308d60dcb9879d4fb4e554c7d48427`. The Freeze event is
`sha256:4d6ad7491f604242c82c1abaf171f6bde09f608552cfc38e5cd9298ac740143a`. Its project-level frozen prerequisites are the modules
providing `hamiltonianPropagator` and `exp_mulVec_of_eigenvector`. The proof
uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`;
no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2023 math.CO and quant-ph paper, preregistered in
issue #11607 before any Lean. `theorem`; resolution `refuted`. The public
theorem has `proof_shape: bind-only`: the eigenvector action comes from the
frozen `exp_mulVec_of_eigenvector`, and the remaining steps are trigonometric
normalization with Mathlib's finite cosine sum `Real.sin_mul_sum_cos`, all
local steps of `result`. Its admission
basis is `open-problem-resolution`. Utility
`kind=certified-instance; basis=refutes` with typed `claim` and `result`.

### What the settlement shows

**Proved (Lean):** for `n = 9`, `|U(t)_{1,1}| ≥ 5/18` for every real `t`, so
vertex `1` of `P_9'` is not sharply `1/9`-sedentary.

**Mechanism (proved inside `result` for `n = 9`):** the real part of the
return amplitude of `P_9'` is `1/2 + (1/18) Σ_k cos(t λ_k)` over the eigenvalues
`λ_k = 2cos((2k + 1)π/18)`, and the relation
`2cos(π/18) = 2cos(5π/18) + 2cos(7π/18)` couples three of the four positive
phases, which cannot all have cosine near `−1`. **Not formalized (argument):**
the same decomposition gives `1/2 + (1/(2n)) Σ_k e^{it λ_k}` with
`λ_k = 2cos((2k + 1)π/(2n))` for every odd `n`, and the paper's sharpness
argument uses that the positive `λ_k` are linearly independent over `ℚ`.

**Computed (exact linear algebra over `ℚ`, the program in the Evidence
section; not formalized), with the paper's Lemma 9 (S = {0}, a = 1/2 + 1/(2n)):** an integer
relation among the positive support eigenvalues with odd coefficient sum rules
out the value `1/n`, and linear independence gives it. For odd `5 ≤ n ≤ 39`, the
positive support eigenvalues are linearly independent over `ℚ` exactly for the
primes `5, 7, 11, 13, 17, 19, 23, 29, 31, 37`, so the conjecture holds there;
for `9, 15, 21, 25, 27, 33, 35, 39` there is a relation with odd coefficient
sum, so the conjecture fails there as well.

**Computed (the program in the Evidence section), not formalized:** `α`, `β`,
`γ`, `√3` have rank 3 over `ℚ` with the single relation `α = β + γ`, and `β`,
`γ`, `√3` are independent. **Argument, not formalized:** by Kronecker's
theorem the phases `(βt, γt, √3 t)` are dense modulo `2π`, so the infimum at
`n = 9` equals `5/18` exactly: vertex `1` of `P_9'` is sharply
`5/18`-sedentary.

**Open:** whether, for every odd `n ≥ 5`, vertex `1` of `P_n'` is sharply
`1/n`-sedentary if and only if `n` is prime.

**Source consequences:** no other result of arXiv:2401.00362 depends on the
conjecture; the paper's lower bound `1/n` (Example 18) and the case `n = 5`
stand.

## ASSUMED-UNVERIFIED

The Discrete Mathematics text was not read, so it is unverified whether the
conjecture was edited there. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
answer. The Lean kernel does not authenticate the external source or its
version history.

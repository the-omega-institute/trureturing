---
slug: lidar-2025-qpu-restricted-anticoncentration-refutation
bibkey: lidar2025dadqc
doi: 10.48550/arXiv.2512.07127
url: https://arxiv.org/abs/2512.07127v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.result
---

# Lidar's QPU-restricted IQP anticoncentration conjecture

## Problem

D. A. Lidar, “Digital-Analog-Digital Quantum Supremacy”, arXiv:2512.07127v1,
p. 4, Conjecture 2, asks for positive constants $a,b$, depending only on $d$,
such that every output string $s$ satisfies
$\Pr_{G,\theta}[P_{U_{\mathrm{IQP}}^{(\theta)}}(s)\ge a2^{-n}]\ge b$.
The hardware graph is fixed, simple and $D$-regular, $3\le d\le D$ is fixed,
$G$ is uniform on its $d$-factors, the angles are independently uniform on
$[0,2\pi)$, and the one-qubit fields are arbitrary but fixed. The Library note
quotes Definition 1 and Conjecture 2 verbatim and identifies Eqs. (17)–(20).

## Motivation

The source's Theorem 2 assumes Conjecture 2. A valid hardware family and one
fixed field choice violating the uniform positive lower bound refute its
universal scope. The motivation GID proves `claim`, which is the negation of
that lower bound on the subsequence $n=6m$, $m\ge3$.

## Gap

Tier 1 external named open problem, preregistered in issue #13764.
The preregistration records the source quotations, quantifiers, literature
queries and refutation criterion. Its literature conclusion is
`not-found-in-searched-scope`; it is not an exhaustive literature certificate.
The supporting module supplies hardware factors and product-angle integration;
the settling module connects these to the literal circuit probability.

## Route

Set $d=4$, $D=5$, and every fixed field $v_i=\pi/7$. Each of the $m$ blocks is
$K_6$ with one edge removed, and the missing-edge endpoints are joined cyclically
between adjacent blocks. The hardware adjacency is literal; `hardware_degree_five`
checks its degree and `factor_nonempty` proves that the four-factor ensemble exists.
The complement of a four-factor is a perfect matching. `factor_block_twins`
finds in every block a nonadjacent pair with the same four neighbours.

`circuit_amplitude_literal` expands the tensor circuit, and
`factor_entangler_eq_CZ` identifies its diagonal entangler with the graph phase
up to a global phase. Partial trace and integration over the complementary
angles give the twin conditional mean. The square-root moment contracts by
$47/48$ per block. Product-angle periodicity absorbs the fixed fields and the
output-bit shifts. Markov's inequality gives, for every output $s$ and $a>0$,

$$
\Pr_{G,\theta}[P(s)\ge a2^{-6m}]
\le a^{-1/2}(47/48)^m.
$$

The right side tends to zero, so no positive uniform $b$ exists.

## Falsifier

The source conclusion would require one pair $a,b>0$ to work for every
$m\ge3$ and every output string. `result : claim` proves that no such pair
exists for this literal circuit and joint graph-angle measure. No alternate
definition of output probability is used.

## Evidence

The mathematical declarations are
`D5/S3/Quantum/Measurements/IQP/HardwareCircuitFactors` and
`D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.result`.
The Scribe settling node carries `OpenProblemResolutionClaim` with `Refuted`.
The mathematical truth and axiom closure are the Lean declarations; the graph
enumeration below is independently rerunnable finite computation.

## Triage

The settling module has `admission_basis: open-problem-resolution (#13764)`;
the supporting module has `admission_basis: escape-witness`, witnessed by
`OpLidarProductShift.pi_periodic_shift`. Auxiliary bind-only declarations are
used on the live path to the settlement. No digestion atom or cover is involved.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this delivery:** forced twins in every four-factor of the displayed
  hardware family yield the product reduced-state calculation and its conditional
  mean. `factor_block_twins`, `normalized_twin_conditional_mean`,
  `factor_literal_fractional_moment`, `literal_tail_bound` and `result` connect
  that structure to the literal circuit and the uniform output-tail bound.
- **Proved in the supporting module:** `conditional_fractional_moment` applies to
  any nonnegative integrable random variable $Z$ on independent uniform angle
  pairs and an arbitrary probability space $Y$, when its conditional mean is
  $\prod_{i=1}^{m}(1+\cos\alpha_i\cos\beta_i)$. It gives
  $\mathbb E\sqrt Z\le(47/48)^m$; `fractional_markov` gives the corresponding
  upper tail. These are the actual general hypotheses furnished by this proof.
  **Open:** a literal-circuit bridge for every hardware family with a positive
  density of forced twins. A positive-density count alone is not the delivered
  conditional-mean and joint-measure hypothesis.
- **Computed:** at exactly $m=3$, $n=18$, enumeration gives
  $|F_4(H_3)|=1755=12^3+3^3$ and $1728=12^3$ connected factors, so
  $\Pr[G\text{ connected}]=64/65=4^3/(4^3+1)$. The script, command, exit and
  hash appear below. **Open in Lean:** the uniform formulas
  $|F_4(H_m)|=12^m+3^m$ and
  $\Pr[G\text{ connected}]=4^m/(4^m+1)$ for all $m\ge3$.
  The paper argument counts perfect matchings: no connector yields twelve local
  choices per block and connected complements; all connectors yields three
  local choices per block and disconnected complements. Local parity forces
  these two connector cases. This combinatorial argument is not a delivered
  kernel proof of the uniform counts.
- **Open:** sufficient structural hypotheses restoring anticoncentration,
  including expansion or exclusion of forced twins. **Open:** the specific
  Zephyr hardware mentioned in the source. This settlement proves neither a
  Zephyr counterexample nor a restoring theorem.
- **Open and unaffected:** Conjecture 1, the source's average-case hardness
  assertion. No average-case hardness proof or refutation is delivered.
- **Proved:** Conjecture 2 fails with its stated universal hardware scope.
  **Open formal bridge / source consequence:** Theorem 2 remains a conditional
  implication under its stated conjectures; the refuted general anticoncentration
  hypothesis cannot supply an unconditional supremacy conclusion. No Lean proof
  of the source's complexity-theoretic implication or of a replacement ensemble
  is delivered.

### Finite graph enumeration

Save the following exact script as `enumerate-lidar-m3.py` and run
`python3 enumerate-lidar-m3.py`. Exit code: 0.
SHA256: `75d1b2e73d588043fe7d12cfe120c60b51be2f9cfedd995a7422a93e3e31f516`.
Output: `m=3; vertices=18; hardware_edges=45; F4=1755; connected=1728; probability=64/65`.

```python
from fractions import Fraction
m = 3
n = 6 * m
edges = set()
for i in range(m):
    for a in range(6):
        for b in range(a + 1, 6):
            if (a, b) != (4, 5):
                edges.add((6 * i + a, 6 * i + b))
    edges.add(tuple(sorted((6 * i + 5, 6 * ((i + 1) % m) + 4))))
adj = [set() for _ in range(n)]
for u, v in edges:
    adj[u].add(v)
    adj[v].add(u)
assert len(edges) == 15 * m and all(len(a) == 5 for a in adj)
def matchings(unmatched, chosen):
    if not unmatched:
        yield frozenset(chosen)
        return
    u = min(unmatched)
    for v in sorted(adj[u] & unmatched):
        yield from matchings(unmatched - {u, v}, chosen + [(min(u, v), max(u, v))])
def connected(es):
    a = [set() for _ in range(n)]
    for u, v in es:
        a[u].add(v)
        a[v].add(u)
    seen = {0}
    todo = [0]
    while todo:
        for v in a[todo.pop()] - seen:
            seen.add(v)
            todo.append(v)
    assert all(len(x) == 4 for x in a)
    return len(seen) == n
factors = [edges - set(M) for M in matchings(set(range(n)), [])]
assert len({frozenset(G) for G in factors}) == len(factors)
c = sum(connected(G) for G in factors)
assert len(factors) == 12 ** m + 3 ** m
assert c == 12 ** m
assert Fraction(c, len(factors)) == Fraction(4 ** m, 4 ** m + 1)
print(f'm={m}; vertices={n}; hardware_edges={len(edges)}; F4={len(factors)}; connected={c}; probability={Fraction(c, len(factors))}')
```

## ASSUMED-UNVERIFIED

The literature reading in #13764 is scoped and source-attested. The uniform
graph-count formulas, arbitrary positive-density hardware bridge, restoring
conditions, Zephyr behaviour, average-case hardness and the source's general
complexity-theoretic implication are not kernel-certified by this delivery.

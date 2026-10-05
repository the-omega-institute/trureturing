# Flat-prefix RT specialization: existing result and formalization checklist

This note is a formalization checklist, not a new mathematical theorem. The
positive flat-prefix construction, its kernel and the optimal diamond error
are already proved on paper in `ARITHMETIC_HOLOGRAPHIC_RT.md`, Theorem 34.1.
The generic channel construction and optimality used below are already present
in `FiniteSectorPhysicalConstruction.lean` and
`FiniteSectorChannelOptimality.lean`. PR #13249 supplies explicit coordinates
for an existing recurrence. Merely combining these suppliers in a new wrapper
would not constitute an independent mathematical contribution.

## Existing flat-prefix specialization

Let `n : N`. The case `n=0` is the trivial single-sector bridge: `v=(1)`,
`T=0`, and `delta=0`; below assume `n >= 1`. Let `1 <= m_0 < ... < m_n` be
integers, and let `1 <= d_i` be integers. Put `r_i = m_i d_i`,
`ell_i = log m_i`, and let `M = m_n`. Define,
for `j : Fin M`,

```
sigma i j = if j.val < m_i then (m_i : R)^(-1) else 0.
```

Take sectors `S = Fin (n+1)` and the model in
`D5/S3/Quantum/Entanglement/FiniteSectorChannelModel.lean` with target rank
`d i`, spectral size `M`, and spectrum `sigma`. Then:

1. `sigma` is nonnegative, sums to one, and is antitone in `j`, so it is a
   valid `Model S M` (the only arithmetic input is `0 < m_i` and the prefix
   cardinality `card {j : Fin M | j.val < m_i} = m_i`).
2. The model's residual Gram kernel is exactly
   `kernel sigma i k = sqrt (min(m_i,m_k)/max(m_i,m_k)) =
   exp(-|ell_i-ell_k|/2)`. Under the displayed ordering this is the
   exponential kernel on the ordered loss list.
3. `physical_encoding` in
   `D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.lean` gives
   source and target encoding channels and local CPTP splitters. On sector
   `i`, the source is the flat Schmidt state of rank `r_i`; the splitter has
   Stinespring map
   `|i,a,b> -> |i,a> |b>` and therefore leaves the target flat state of rank
   `d_i` while its environment is the flat maximally entangled state
   `|Phi_{m_i}> = m_i^(-1/2) sum_{b<m_i} |b,b>`.
4. For the nested prefix embeddings `b < m_i` into a common `M`-dimensional
   environment,
   `inner(Phi_{m_i},Phi_{m_k}) = sqrt(min(m_i,m_k)/max(m_i,m_k))`. Hence the
   induced logical action of the two-sided local channels is the Schur channel
   `X_ik -> K_ik X_ik`, with `K` the same kernel as in (2).
5. Let `v_i = equilibriumWeight n ell i` and `Z = sum_i v_i`. Since `ell` is
   monotone, the existing theorem `ExponentialSectorKernel.result` supplies
   `K v = 1`, `v > 0` under the strict ordering, `Z = 1 + sum_i tanh((ell_{i+1}-ell_i)/4)`, and
   `p*=v/Z` in the simplex with `min_{p in Delta} p^T K p = 1/Z`. The
   endpoint/interior formula from #13249, applied to `n-1` when `n >= 1`,
   identifies (the interior formula ranges over `1 <= i < n`)

   ```
   v_0 = 1/(1+sqrt(m_0/m_1)),
   v_n = 1/(1+sqrt(m_{n-1}/m_n)),
   v_i = 1/(1+sqrt(m_{i-1}/m_i))
         + 1/(1+sqrt(m_i/m_{i+1})) - 1.
   ```

6. Applying `FiniteSectorChannelOptimality.result` to this `Model` gives the
   exact physical two-sided CPTP/Stinespring channel and diamond error

   ```
   delta = 2 * (1 - 1/Z)
         = 2*T/(1+T),
   T = sum_i tanh((ell_{i+1}-ell_i)/4),
   ```

   including passive-reference inputs. Thus the recursive weight is the
   optimizer for the *actual* finite channel once integer ranks and the
   ordered flat-prefix spectrum are supplied.

### Remaining proof-engineering obligations for a formal specialization

* `source_transport`: the generic model's local source carrier has dimension
  `sum_i d_i*M`, with zero Schmidt coefficients outside `j<m_i`. The actual
  flat-rank carrier has dimension `sum_i d_i*m_i`. To state the result on that
  smaller carrier, construct the support embedding and prove restriction and
  CPTP extension preserve the encoded channel actions and errors. Equal Schmidt
  rank alone is not a complete typed transport proof.
* `PrefixModel`: prove `sigma_nonneg`, `sigma_sum`, and `sigma_antitone`; these
  are finite sums over a prefix of `Fin M` and do not require new analysis.
* `prefix_kernel`: split the sum at `min m_i m_k`; each nonzero summand is
  `1/sqrt(m_i m_k)`, giving `min/sqrt(m_i m_k)`.
* `physical_prefix_stinespring`: specialize the existing `physical_encoding`
  splitter action. The action is already exposed as a sum over residual labels
  in `physical_encoding`; prefix support reduces this to the nested environment
  overlap above.
* `ordered_kernel_eq`: rewrite `sqrt(min/max)` as
  `exp(-|log m_i-log m_k|/2)` using positivity of integer casts and
  `Real.exp_log`.
* `equilibrium_bridge`: invoke `ExponentialSectorKernel.result` with
  `Monotone ell`; use #13249's endpoint/interior theorem only for the closed
  coordinate formula.

No new channel optimality argument is needed: the generic theorem already
proves the all-local-CPTP lower bound and the matching splitting channel.

## Exact failure of the unsorted recurrence, not of the physical channel

Ordering is a choice of sector labels and can always be achieved by relabeling.
It is needed when applying this particular recurrence to the absolute-distance
kernel. It is not a physical obstruction to a channel with unsorted ranks.

For an exact example take the positive integer ranks

```
m = [1, 4, 16, 1],
loss = [0, log 4, log 16, 0],
edge = [1/2, 1/2, 4].
```

The unrestricted #13249 recurrence then gives

```
v = [2/3, 1/3, -2/15, 1/5],
K = [[1,   1/2, 1/4, 1  ],
     [1/2, 1,   1/2, 1/2],
     [1/4, 1/2, 1,   1/4],
     [1,   1/2, 1/4, 1  ]],
K v = [1, 7/10, 1/4, 1].
```

All these equalities are exact rational calculations. Thus the vector from
this unsorted recurrence has a negative coordinate and does not solve
`K v = 1`; normalizing it does not produce a simplex point. Nevertheless,
`K` is the Gram matrix of the genuine nested maximally entangled states
`Phi_1, Phi_4, Phi_16, Phi_1`, so the two-sided splitter channel exists in
precisely this original label order. Sorting and merging equal-rank groups
restores the ordered optimizer without changing the physical task.

For completeness, prescribed flat residual ranks must be positive integers,
but absolute integrality of `exp(loss_i)` is not necessary for realizing the
same kernel: adding a common constant to every loss leaves `K` unchanged.
A common shift that turns every `exp(loss_i)` into an integer suffices for the
flat-prefix realization. For finitely many losses such a common scaling exists
exactly when all ratios `exp(loss_i-loss_0)` are rational. This is a restriction
on this flat, maximally entangled rank realization, not a denial of a general
Schur CPTP realization of the exponential Gram kernel.

## Status

No new Lean declaration, kernel compilation, or independent new theorem is
claimed. The positive result is already in Theorem 34.1; the unsorted example
only warns against deleting an existing hypothesis. CI on this Markdown file
checks repository workflow eligibility, not these mathematical claims.

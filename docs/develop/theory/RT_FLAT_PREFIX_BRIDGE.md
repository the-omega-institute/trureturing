# RT bridge theorem after `equilibrium_weight_endpoint_interior`

This is a standalone bridge note; it does not alter any existing source file.
It records a Lean-ready theorem that instantiates the existing finite-sector
channel construction with flat-prefix residual spectra, and separates the
hypotheses needed for a physical realization from the unrestricted recursive
formula.

## Theorem (flat-prefix physical bridge)

Let `n : N`, let `1 <= m_0 < ... < m_n` be integers, and let `1 <= d_i` be
integers. Put `r_i = m_i d_i`, `ell_i = log m_i`, and let `M = m_n`. Define,
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
   `K v = 1`, `v >= 0`, `Z = 1 + sum_i tanh((ell_{i+1}-ell_i)/4)`, and
   `p*=v/Z` in the simplex with `min_{p in Delta} p^T K p = 1/Z`. The
   endpoint/interior formula from #13249 identifies

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

### Proof obligations for a Lean PR

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

## Precise obstruction to the naive unrestricted bridge

The #13249 recurrence is quantified over *arbitrary* real `loss : N -> R`.
Without ordering, its vector need not be the inverse-kernel equilibrium vector
and need not be a probability. For example, with

```
loss = [0, 10, 20, 0]
q0 = exp(-5), q1 = exp(-5), q2 = exp(10)
```

(the `q_i` are the three `edge` values), #13249's coordinate formula gives

```
v = [ 1/(1+q0),
      1/(1+q0)+1/(1+q1)-1,
      1/(1+q1)+1/(1+q2)-1,
      1/(1+q2) ]
  ~= [0.993307, 0.986614, -0.006647, 0.0000454].
```

Thus `v_2 < 0`, and direct multiplication by the kernel
`K_ij = exp(-|loss_i-loss_j|/2)` gives `(K v)_2 ~= 4.54e-5`, not `1`.
Consequently no simplex optimizer or CPTP environment interpretation exists
for this unsorted input. The monotonicity hypothesis in
`ExponentialSectorKernel.result` is therefore essential, rather than a
formal convenience. A second independent obstruction is integrality: if
`exp(loss_i)` is not a positive integer ratio, no finite Schmidt ranks
`r_i=m_i d_i` realize the spectrum even when the recurrence vector is
positive.

The bridge theorem must therefore state (or derive by sorting/collapsing
sectors) both conditions: ordered losses and integer flat-prefix ratios.

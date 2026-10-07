# Actual Binet inverse and finite resolution

The [producer](binet_inverse_tail.py) and [directed data](binet-inverse-tail.json)
provide a complete quarter-moment allowance for the actual Binet Dirichlet
inverse. The mathematical parameter application and finite-input error
bound are in [FIB §388](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#388-实际-binet-逆核的四分之一矩与分辨率尾证书).
The existing stable Mertens/FIB inverse and RH growth equivalence in §384
are reused. No old theta, arithmetic or inverse grid producer is executed.

For $q=(3-\sqrt5)/2$, $\beta_d=\log(1-(-q)^d)$ and
$\gamma=\beta^{-1}$ in Dirichlet convolution, the retained scalar budget gives

$$
\beta_1-\sum_{d>1}|\beta_d|d^{1/4}>7/500,
\qquad
\sum_{d\ge1}|\gamma_d|d^{1/4}<500/7.
$$

The numerical source retains 64 Binet terms and pays every omitted term
with $q^{65}(65-64q)/(1-q)^3$. Its inverse-quarter-moment upper allowance
is approximately $71.4112152978443$. This is a complete norm allowance,
not a measured value of the infinite moment.

The classical source is Glöckner and Lucht,
[*Weighted inversion of general Dirichlet series*, arXiv:1112.0749v2](https://arxiv.org/pdf/1112.0749v2),
Proposition 1, pp. 4–5, and Theorem 2(a), p. 4. The multiplicative weight
$d^{1/4}$ gives a Banach algebra and permits a small-tail Neumann inverse.
In log coordinates it is an exponential weight, so the paper's distinct
Theorem 1 admissible-weight spectral characterization is unused.
The complete inverse-moment estimate is an application of those existing
results, without a new generic inversion theorem or originality claim.

Write $A_D=\sum_{d\le D}|\gamma_d|d^{1/4}$. The data retain actual inverse
coefficients through $F_{18}=2584$. For each listed cutoff, the remaining
moment allowance subtracts the certified **lower** endpoint of $A_D$
from the complete upper allowance. Dividing by $(D+1)^{\alpha+1/4}$
gives the operator-tail allowance on sequences with
$\sup_{N\ge1}|f(N)|/N^\alpha<\infty$. The source, prefix and complete
budget use the same actual coefficients.

| Kernel cutoff $D$ | Remaining quarter-moment allowance, approximate | $\alpha=1/2$ tail allowance, approximate |
|---:|---:|---:|
| $F_3=2$ | $66.528109$ | $29.185305$ |
| $F_6=8$ | $62.691633$ | $12.065011$ |
| $F_9=34$ | $59.184207$ | $4.112963$ |
| $F_{12}=144$ | $55.626056$ | $1.331228$ |
| $F_{15}=610$ | $52.752897$ | $0.429256$ |
| $F_{18}=2584$ | $50.181704$ | $0.138421$ |

The exact dyadic endpoints carry the bounds. At $D=2584$, the last
tail allowance is strictly below $0.138421$. The unadjusted public
moment cap would give approximately $0.1970274$ at the same cutoff.
Neither value is an estimate of the actual centered cancellation.

For the actual FIB error $H$, the existing identity gives
$\mathfrak M(N)=\sum_{d\le N}\gamma_dH(\lfloor N/d\rfloor)$.
The kernel tail reads only indices at most $\lfloor N/(D+1)\rfloor$.
Thus §388's local finite maximum supplies an error certificate at each
fixed $N$ without assuming an unknown global square-root bound for $H$.
The retained terms still require their own actual high-index inputs.
A global critical-space statement is conditional on membership of the
input in that space; it does not establish that membership for actual $H$.
The positive response $k=\gamma*\log$ remains a different operator.

## Reproduction and scope

The retained result uses Python 3.13.12, python-flint 0.9.0 and 192 bits:

```sh
uv run --offline --no-project --python 3.13 --with python-flint==0.9.0 python docs/reports/fib-robin-boundary/binet_inverse_tail.py --output /tmp/binet-inverse-tail.json
```

The declared offline runtime must be installed or cached. The entry
point accepts the Binet head length, inverse-prefix cutoff, precision and
output path. It computes stable small logarithms with `log1p`; the full
exponential tail is independent of the finite inverse table. Source hash,
parameter formula, scalar enclosures, inverse coefficients and Fibonacci
resolution records are retained. A finite inverse check and prime/prime-square
coefficient comparisons test the prefix implementation. They do not replace
the cited full inverse or certify arbitrary inputs.

All infinite conclusions rely on the original Binet formula, classical
weighted inversion and stated directed numerical supplier. This computation
provides no actual $H$ square-root growth estimate, signed Robin tail bound,
common cofinal signs, RH proof or new Lean certification.

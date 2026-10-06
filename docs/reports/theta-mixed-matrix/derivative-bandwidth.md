# Direct actual-theta bandwidth at one fixed gap

The [weighted Fourier construction](../../../Library/Weil/fukushima2011dirichlet.md)
permits direct checking of its symbol and leakage conditions below the
coarse sufficient closed-form threshold (WF6). This program supplies
actual original-theta derivative norms and verifies those two conditions
at $\varepsilon=1/4$, $N=64$.

## Derivative and full-tail enclosures

Reuse the original-series derivative identities (WC1)–(WC3) in the
[theta supplier note](../../../Library/Analytic/romik2021orthogonal.md).
For $x\ge0$, retain theta indices $n\le6$ and derivative orders
$0\le j\le3$. The explicit $C_j$ tail after six, using
$r_*=(3/2)^{10}e^{-5\pi}<1$, multiplied by
$e^{(9/2+2j)x-\pi e^{2x}}$, bounds each omitted derivative.
No derivative of an asymptotic remainder is used.

Each cell requires a strictly positive lower bound for $\Phi$ before
forming ratios. With $r_j=\Phi^{(j)}/\Phi$,
$t=\tanh(x/2)$, $k=\operatorname{sech}(x/2)^2$ and $\ell=\log s$,
the existing derivative identities give

$$
\ell'=(r_1-t/2)/2,\qquad
\ell''=(r_2-r_1^2-k/4)/2,\qquad
\ell'''=(r_3-3r_1r_2+2r_1^3+kt/4)/2.
$$

Use $s'=s\ell'$, $s''=s((\ell')^2+\ell'')$ and
$s'''=s((\ell')^3+3\ell'\ell''+\ell''')$. Computing the $r_j$
before their products avoids interval powers of the small denominator.

The 1536 exact dyadic boxes cover $[0,3]$. Twice the sum of box widths
times squared absolute derivative upper endpoints bounds the entire
interior integral by evenness. For $c=3/8$, the (WC2) bound gives

$$
\|s^{(j)}\|_{L^2(|x|>3)}^2
\le K_j^2\frac{e^{-2c e^6}}{2c e^6}.
$$

This follows by substituting $u=e^{2x}$ on both tails and bounding
$1/u$ by $e^{-6}$. The program may enlarge the scalar maximum in $K_j$
to $\max_{u>0}u^{1+2j}e^{-(\pi/2-c)u}$, which also bounds $u\ge1$.

The [saved exact dyadics](derivative-bandwidth-result.json) give these
rounded upper bounds:

| Derivative order | Full $L^2$ squared norm upper bound |
|---|---:|
| 0 | $0.2514288769553961$ |
| 1 | $1.527668781502706$ |
| 2 | $41.10771340011968$ |
| 3 | $27781.80832537150$ |

These are upper bounds, rather than two-sided quadrature accuracies.
The deliberately coarse order-three bound is not used in the $N=64$
leakage test.

## Direct symbol and leakage conditions

At $\xi=32$, retain the first 1024 positive terms of (WF3),

$$
m(\xi)=2\sum_{k\ge0}\frac{\xi^2}{a_k(a_k^2+\xi^2)},
\qquad a_k=2k+\tfrac12.
$$

The partial lower endpoint is a lower bound for the full symbol. The
omitted sum is at most $\xi^2/(2a_{1023}^2)$ by the decreasing
inverse-cubic integral. Rounded outward,

$$
6.9998794435578549\le m(32)\le7.0000016928809330.
$$

The program reads the [approved deficit](deficit-result.json) from its
canonical sibling file and records that data file's SHA-256. Its reused
upper bound is $\mu_{1/4}\le5.2350558731050110$, so
$m(32)\ge\mu_{1/4}$.
Combining the derivative upper bound with (WF5) gives

$$
m(32)\eta_{64}^2
\le m(32)\frac8{3\pi}64^{-3}\|s''\|_2^2
<0.0009317521481018941<\frac1{16}.
$$

Thus both direct sufficient conditions hold at $N=64$. Applied to the
same actual even minimal form, (WF5)–(WF6) yield

$$
\widetilde D(v)\ge\frac5{16}\|v\|_2^2
\quad\text{if }v\text{ is in the even minimal form domain and }
\widehat v=0\text{ on }|\xi|<64.
$$

The complete prime operator, both translated directions and all Gamma
crossing edges remain present. This is a high-frequency restriction
bound; it does not rule out spectral vectors mixing low and high
frequencies.

This direct check does not assert $64\ge N_0(1/4)$ in the displayed
closed-form (WF6) formula. Substituting the saved upper bounds into that
formula gives a first term greater than $520871$. The direct conditions
provide an alternative sufficient check. Independent commutator accuracy
and finite-family mesh requirements are still necessary; a small lower
bandwidth alone does not give a practical finite family or matrix sign.
There is no cofinal $\varepsilon\downarrow0$, RH, Robin, originality or
new Lean-certification claim.

## Reproduce

The recorded runtime is Python 3.13.12, python-flint 0.9.0 and 128-bit
ball arithmetic. From the repository root run

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/derivative_bandwidth.py
```

The command writes `derivative-bandwidth-result.json` beside the program.
It rejects a nonpositive denominator, nonfinite enclosure, unproved tail
ratio, or failure of either declared direct condition. The program is
project-authored and applies the existing original-series derivative
supplier using FLINT arithmetic; dependency licensing is supplied by
python-flint/FLINT.

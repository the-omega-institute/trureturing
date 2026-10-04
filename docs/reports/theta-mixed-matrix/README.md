# Actual mixed theta scalar assembly

This program evaluates the documented
[complete theta matrix assembly](../../../Library/Weil/jarohsweth2020local.md)
on one specified real even trial function. It retains the original
probability measure, Gamma jump corners, all retained prime powers and
full-probability variance. Its purpose is to exercise that implementation
interface; this single function is not the complete approximation family
required by the fixed-window spectral test.

## Exact inputs and model

Put $\ell=\log2$, $\delta=1/2$ and

$$
b(x)=2w_{1/2}(x)=\frac{\mathbf1_{\{1/2<|x|<1\}}}{\ell|x|}.
$$

The target is
$T=D(b)-(3/8)(G-\mu^2)$, with $G=\int b^2d\nu$,
$\mu=\int b\,d\nu$, $d\nu=2\Phi(x)\cosh(x/2)dx$ and total mass one.
The original theta series and the exact weight
$\psi(t)=e^{-t/2}/(1-e^{-2t})$ are used.

The retained Gamma square is $[-2,2]^2$. Complete positive-shift prime
terms are retained through $N=8$: $2,3,4,5,7,8$, with
$w_{p^k}=\log p/\sqrt{p^k}$. Each positive-shift integral includes both
original graph directions in the normalized energy.

Gamma cells have boundaries $-2,-1,-1/2,1/2,1,2$. The two nonzero
same-cell triangles, eight jump-corner triangles and three separated
rectangles cover every nonzero retained contribution. Each transformed
unit square uses $64^2$ directed interval boxes, totaling 53,248 boxes.
The jump differences are kept in their one-sided branches. No nested
analytic integral is used.

The six-term theta callback includes the uniform complex remainder from
(TH) in the model note and rejects boxes violating its strip or ratio
conditions. The real removable kernel uses the positive entire series
for $\sinh(t)/t$ through order 20 with a geometric remainder. Field
multiplication encloses real squares even when their intervals cross
zero. Shifted prime breakpoint ordering and both active and zero branch
membership are explicitly certified; ambiguity raises an error.

## Directed target accounting

Choose the exact rounded dyadic $r$ saved in the result. The retained
quantity is

$$
F_r=D_{2,8}(b)-\tfrac38(G-2\mu r+r^2),
\qquad
T-F_r=R_\Gamma+R_p+\tfrac38(\mu-r)^2\ge0.
$$

The reported upper bound for the full $T$ adds both explicit omitted-tail
bounds and the mean loss. In particular, the upper endpoint of $F_r$
alone is not an upper bound for $T$. Since $\log9>2$ is certified, the
omitted prime supports are disjoint and the coefficient-one potential
bound applies. Every omitted prime power is included in that bound.

The result contains exact dyadic lower/upper endpoints, the actual runtime
versions, every retained prime term and Gamma panel, and the number of
certified branch reads. Rounded human-readable intervals are:

| Quantity | Enclosing interval or upper bound |
|---|---|
| $G$ | $[0.1173319675831936,0.1173319675831938]$ |
| $\mu$ | $[0.0448861392452370,0.0448861392452372]$ |
| $D_{p,\le8}(b)$ | $[0.0206720399437825,0.0206720399437827]$ |
| $D_{\Gamma,[-2,2]}(b)$ | $[0.0295399,0.0485488]$ |
| $F_r$ | $[0.0069680,0.0259769]$ |
| $R_\Gamma$ | $<3.7720\cdot10^{-38}$ |
| $R_p$ | $<2.2821\cdot10^{-6}$ |
| $(3/8)(\mu-r)^2$ | $<7.5872\cdot10^{-14}$ |
| Full $T$ | $[0.0069680,0.0259792]$ |

This directed computation gives a positive lower bound on this scalar
trial target. It does not supply signs for the prescribed full family,
a complete low-spectral-window exclusion, a cofinal window certificate,
Lean certification, RH or the full Robin inequality.

## Reproduce

The recorded runtime is Python 3.13.12, python-flint 0.9.0, FLINT 3.6.0,
with 128-bit ball arithmetic. The inspected source-method documentation
is separately pinned in the
[Johansson integration note](../../../Library/Analytic/johansson2018ballintegration.md);
its FLINT 3.3.1 documentation pin is not a claim about the installed wheel.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/scalar_pilot.py
```

The command writes `scalar-result.json` next to the program. Nonfinite
enclosures, uncertified branches or breakpoint ordering, failed tail
conditions and the declared box limit reject the computation. The
implementation uses existing FLINT directed arithmetic and integration;
no third-party implementation code is copied here. The program is
project-authored; dependency licensing is supplied by python-flint/FLINT.

The separate [directed weighted Fourier deficit](deficit.md) reuses these
theta callbacks to enclose the full symmetric-row scalar deficit at
$\varepsilon=1/4$. It supplies a coefficient for the Fourier construction,
without computing the finite trial matrix or repeating this scalar trial.

The [direct derivative and bandwidth supplier](derivative-bandwidth.md)
encloses the original-theta derivatives and checks the two direct
high-frequency conditions at $\varepsilon=1/4$, $N=64$. It retains the
even minimal form and leaves independent finite-family accuracy and
matrix-sign requirements unresolved.

The [joint high-frequency floor](joint-high-floor.md) combines the same
symbol and derivative supplier with the full symmetric prime row. It
puts the complete even high-frequency restriction above $c=3/8$ and
retains a positive variance gap. The low block and its coupling remain
unestimated.

The [sharp-band center interface](sharp-center.md) retains the complete
operator and bounds a prescribed finite approximation to its full Schur
center. Original-theta exponential moments and existing Bernstein-ellipse
approximation give a center of rank at most 96 with remainder below
1/16 at the same threshold. The retained matrix sign, high correctors
and their complete operator residuals remain uncomputed.

The [complete low-band forward-action supplier](forward-action.md) pays
every omitted Gamma index and both omitted prime directions at this same
band. Its uniform action error is below $1/1000$, with the multiplication
and full mean terms kept exact. High trials require separate weighted
derivative estimates; this low-band allowance cannot certify their
residuals or the retained matrix sign.

The [common matrix screen](common-matrix-screen.md) saves uncertified
numerical diagnostics and exact dyadic choices for four high trials.
The [whole-line trial supplier](high-trials.md) defines those choices
on the actual operator, imposes an exact symbolic ground lift and pays
their own weighted derivative and omitted-action bounds. The retained
integrals, complete residual Gram and lower matrix sign remain unpaid.

The [ground normalization and residual-tail supplier](ground-residual.md)
uses the same saved theta norms to bound the exact ground projection
away from zero. It transports the low and high action allowances to
one common residual map on the exact ground complement, with difference
below $0.000662$. This is an action-tail difference, not a residual norm
or a certificate of its retained Gram.

The [original-kernel strip and coherent-root supplier](strip-root.md)
applies an explicit relative original-series bound before transporting
the square root. It supplies exponential Fourier-action tails on the
same fixed whole-line high family: the full Gamma action beyond
$|\xi|=512$ is below $5.80\cdot10^{-18}$ in its five-generator coefficient
norm. Finite-frequency integrals, exact projection and common residual
Gram remain unpaid. This supplies paper-model inputs with directed
coefficient bounds, without a matrix sign or new Lean certification.

The [stable projected-ground application](stable-ground.md) combines the
existing exact Schur kernel with the one-sided degree-94 tail to bound
$\|E^*Pv_0\|$ away from zero without a new ground-moment integral. A
restricted $E^*SE$ lower bound above $0.004660867160108$ would suffice
for the second Schur elimination. The
[actual low actions and exact direction](low-common-action.md) supply
the inputs to the [restricted comparison](restricted-schur.md).

The [continuous sinc projection supplier](continuous-projection.md)
preserves the actual cutoff64 in a physical convolution. At the saved
spacing it pays infinite-lattice projection quadrature and the finite
physical input tail, while explicitly separating sample and kernel
errors. Its DFT identity applies at lattice outputs; off-lattice prime
shifts require an additional evaluation interface. The actual common
Gram and restricted sign remain unpaid.

The [local high samples](local-high.md) enclose the four actual
$Z=QH_{1024,64}EB$ columns using exact low inputs, continuous sinc
projection and paid local replacement errors. The retained $H,PH$
intervals feed the [localized whole-line Gram](local-z-gram.md) without
another forward solve. This gives $\|Z\|<1.0090$ and the same
five-generator real norm below $1.00904$, while retaining the independent
strip and derivative bounds.

The [full-Gamma periodization allowance](full-gamma-periodic.md)
preserves paired-jump cancellation for the unbounded full symbol on
those same fixed high vectors. It pays analytic local replacement
errors; numerical actions, the complete residual Gram and restricted
Schur sign remain separate obligations.

The [off-grid action interface](off-grid-action.md) pays the shifted
high inputs and full-Gamma contour transport on the same family.
The [actual four-column high action](high-full-action.md) consumes the
saved source samples to enclose $Z^*CZ$ and $(CZ)^*(CZ)$ over the full
real line, including the complete omitted-prime $L^2$ allowance. It
gives $\|CZ\|<1.051588$. The
[actual95 low actions](low-common-action.md) use the same basis and
saved high columns to evaluate the low/mixed blocks and exact projected
ground moments. The [common restricted comparison](restricted-schur.md)
forms their joint residual Gram, pays complete omitted primes and
transports ground-direction intervals into a94-dimensional LDL check.
Under the paper supplier premises, its restricted lower matrix exceeds
the required second-Schur allowance by more than $1/10$. This is a
fixed-$c=3/8$ paper-model comparison, not Lean certification, cofinal
positivity, RH or the full Robin inequality.

The [quantified two-Schur parameter transport](threshold-transport.md)
uses these same saved data to check a conditional ground-orthogonal
gap greater than $0.0005648$ at $c=0.39$, without another action solve.
This bounded parameter range remains short of cofinal $c\uparrow1/2$
positivity and supplies no Lean, RH or full Robin certification.

The [sharper exterior envelope](sharper-exterior.md) reuses the same
interior, actions and restricted comparison. Under the same paper
premises, it improves the high coercivity input and yields a
ground-orthogonal margin greater than $0.00169425$ at $c=0.41$.
This is still a bounded parameter range, without cofinal or RH closure.

The [actual coupling norm and joint three-block comparison](actual-coupling.md)
uses the saved Grams to sharpen the low-tail allowance and the actual
$ZA$ norm. Under the same paper premises its ground-orthogonal margin
is greater than $0.00112575$ at $c=0.42$, without new action columns.
The remaining cofinal, RH, full Robin and Lean obligations are retained.

The [weighted window metric](weighted-window-metric.md) reuses Suzuki's
derivative pairing and transports the original theta variance to its
exact rank-one-corrected metric. It states the outstanding cofinal
relative estimate, including the loss in a scalar unweighted transfer.
It does not supply that estimate or a further numerical margin.

The [target-dependent correction](target-correction.md) chooses new exact
correction maps from those saved actions and reuses the ground moments
to control both complementary ground tails. Under the same paper premises
it gives a whole-form ground-orthogonal gap greater than $0.00186736$
at $c=0.45$. At $c=0.46$ the finite restriction passes, while the
requested joint gap $1/1000$ fails its sufficient comparison. Neither
result closes the cofinal, RH, full Robin or Lean obligations.

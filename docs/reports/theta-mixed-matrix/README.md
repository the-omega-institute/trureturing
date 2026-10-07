# Actual mixed theta scalar assembly

This program evaluates the documented
[complete theta matrix assembly](../../../Library/Weil/jarohsweth2020local.md)
on one specified real even trial function. It retains the original
probability measure, Gamma jump corners, all retained prime powers and
full-probability variance. Its purpose is to exercise that implementation
interface; this single function is not the complete approximation family
required by the fixed-window spectral test.

## Complex inner products for matrix reports

The complex matrix interfaces use the upstream first-slot-linear
convention

$$
\langle f,g\rangle_2=\int_{\mathbb R}f(x)\overline{g(x)}\,dx,
\qquad |u\rangle\langle v|x=\langle x,v\rangle_2u.
$$

For common columns $x_j$ and $x(z)=\sum_jz_jx_j$, a Hermitian
norm Gram written as $z^*Gz$ has
$G_{ij}=\langle x_j,x_i\rangle_2$, so $z^*Gz=\|x(z)\|_2^2$.
Projection coefficients are linear in the projected vector. The saved
real columns and real matrices have the same entries under either
inner-product convention; complex extensions must use the declared one.

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
requested joint gap $1/1000$ fails its sufficient comparison. Reusing
the same positive blocks with the existing three-block norm lift gives
a smaller whole-form gap greater than $1/2000$ and the conditional
original bound $D\ge0.4605\operatorname{Var}_\nu$, without new actions
or another numerical target. These fixed-band results retain the
cofinal, RH, full Robin and Lean obligations.

The [fixed-test and centered-window interface](centered-window.md)
distinguishes the relative scalar conversion from a sufficient absolute
fixed-test limit, and maps the published pole constraint to the original
theta mean. It retains the unproved signed arithmetic estimate.
A new four-bump example shows why pole cancellation alone does not turn
a generic pointwise exponential error envelope into that estimate.
The example kernel is not the actual arithmetic kernel.

The [signed arithmetic head and fixed-row tail](signed-discrepancy-window.md)
retain the prime-minus-continuum realization. Published cumulative-error
and weighted smoothing suppliers give explicit coupling inputs in the
original centered metric. Three new Fibonacci-plus-half cutoffs retain
all prime powers and certify smaller band allowances than the same
measure's total-variation envelope. The out-of-band allowance, low-block
sign and common cofinal parameter sequence are separate obligations.
The [complete fixed-band row allowance](signed-low-row.md) pays the
Fourier and full arithmetic tails at the actual $N=64$ low unit ball,
using new smoothing and frequency parameters and the saved theta
derivatives. It improves the same weighted total-variation allowance;
the low sign and common cofinal parameter sequence remain unpaid.

The [local signed-frequency allowance](local-signed-frequency.md)
instead applies the retained Schur criterion to the actual Fourier
kernel. It reuses theta $H^1$ caps and the complete arithmetic tail,
retains all signed cross terms, and covers the original $N=64$ low
unit ball by 512 closed frequency cells. Its complete upper allowance
is below $5.45645802$, compared to the same operator's prior $T=128$
allowance above $14.70575975$. No old producer is replayed; the
low sign, common cofinal comparison, RH and full Robin remain open.


The [spatially weighted high inverse](../../../Library/Weil/fukushima2011dirichlet.md#spatially-weighted-high-inverse-at-every-subcritical-parameter)
retains the spatial term already supplied by (WF5) at each
$0<\varepsilon\le1/2$ and its prescribed finite bandwidth. The
[complete residual consumer](sharp-center.md#retain-this-spatial-weight-in-the-complete-inverse-residual)
uses it to reduce the same full-residual scalar allowance by a
nonnegative common source Gram, while preserving the exact ground column.
This is a conditional application of existing high-form and inverse-residual
suppliers. Weighted residual entries have not been evaluated; the
[target correction's cofinal boundary](target-correction.md#directed-results-and-the-cofinal-boundary)
still requires actual low and complementary-low signs on the same
parameter sequence. Saved fixed-band matrices do not supply those signs.


The [projection and exact-ground corrections](sharp-center.md#keep-the-projection-and-ground-corrections-on-the-same-residual)
retain the actual high-space constraint in that same residual allowance.
They reuse classical positive block and rank-one inverses and supply a
projection credit without an infinite-dimensional inverse computation.
Its entries remain unevaluated; no low sign or cofinal certificate is supplied.


The [weighted omitted-action supplier](forward-action.md#weighted-omitted-actions-before-the-sharp-high-projection)
feeds a [common dual-source allowance](sharp-center.md#pay-weighted-action-errors-with-one-common-dual-source)
by reconstructing the unprojected action on the exact ground complement.
It reuses the complete Gamma and prime envelopes and the same constrained
inverse tools, keeping the chosen low trial and ground correction joint.
It pays only action truncation errors; retained action and source Grams
remain unevaluated, and no matrix or cofinal sign is supplied.


The [saved-joint-field weighted input](joint-weighted-input.md) uses all
128 already enclosed high-floor cells at the original $N=64,c=3/8$.
Its new coefficient-only calculation encloses the output weight and
common ground-complement action error at the unchanged cutoffs; no old
source acquisition is replayed. Its approximately $0.20175$ weighted/scalar
budget ratio compares truncation allowances, not inverse-cost or matrix
signs. New weighted Gram integration and common cofinal signs remain open.

The [finite-core common residual correction](weighted-residual-core.md)
integrates a step-weight gain from the already saved full-Gamma action
rows and whole-line residual Gram. It pays continuum, sample, prime and
exact-frame uncertainty on the same coefficient map. The enclosed gain
reduces the existing scalar residual allowance on a specified frame
direction; it does not certify positivity of the entire gain matrix or
recompute the global comparison. No old action grid is regenerated.

The [sinc reconstruction of that same core](sinc-weighted-residual-core.md)
reuses the existing continuous projection on saved unprojected rows,
then calls the same cardinal integration and exact-frame code. Its
source/kernel errors remain joint; the smaller error allowance does not
establish all-direction gain, a new global sign or cofinal positivity.

The [vanishing exterior reserve](vanishing-exterior-reserve.md) applies
classical Fourier analytic uniqueness to the original theta weight and
a fixed nonzero sharp-high residual. Deleting the positive reserve makes
the simple multiplier allowance infinite; this fixed-source obstruction
does not decide the actual constrained inverse or a moving cofinal family.
The existing unprojected common dual-source construction is reused, with
its growing source budgets and the actual low signs still unpaid.
The same note's [divided endpoint check](vanishing-exterior-reserve.md#the-divided-endpoint-expression-cannot-have-a-strict-weighted-high-floor)
uses the theta derivative envelopes in a topology controlling that
expression. Its conditional paper argument excludes a strictly positive
$s^2$-weighted endpoint floor at any fixed finite band; it asserts no
sharp-high density in the original minimal form norm, negative energy,
moving-cofinal obstruction or RH conclusion.

The [critical-zero source-range check](critical-prime-source-range.md)
uses the full prime-power action to exclude a blanket exact factorization
of every discarded low source as $Q(sf+a v_0)$, $f\in L^2$, after any
finite low removal. This conditional paper obstruction concerns that
stronger source requirement; positive-reserve approximate estimates and
the actual cofinal form signs remain unresolved.

The [regulated complete-prime source budget](regulated-prime-source-budget.md)
reuses the full half-weighted Mangoldt count to control a common
unprojected source. It selects one cofinal parameter/band schedule for
prescribed growing finite sources, retaining the exact ground.
Band-dependent source norms, actual low/complementary-low signs and
the full RH/Robin conclusion remain unresolved.


The [centered complete-prime discrepancy budget](centered-prime-discrepancy-budget.md)
cancels the continuous main term on the same exactly ground-centered
even $H^2$ source, retaining the endpoint and every prime power. It pays
the extra source derivative norm and improves the fixed-source regulator
allowance in asymptotic order. Common changing-family Grams, actual
inverse convergence and low/cofinal signs remain unresolved.


The same [regulated budget's row and column estimate](regulated-prime-source-budget.md#the-regulator-also-pays-an-l2-source-norm)
pays the complete prime action with the actual common $L^2$ source Gram.
Its prime allowance vanishes uniformly on normalized sources along the
original positive-reserve schedule; archimedean costs and actual signs
remain payable. The [full-low derivative check](centered-prime-discrepancy-budget.md#a-high-lift-cannot-hide-the-full-low-spheres-derivative-cost)
shows why arbitrary regular high lifts cannot make the earlier derivative
certificate uniformly cheap. Neither estimate decides RH or full Robin.

The [actual critical-translation boundary](../../../Library/Dynamics/clason2021regularization.md#the-real-translation-boundary-retains-fixed-sharp-low-mass)
retains a two-tail escaped family inside the original small-window
critical closure, with positive mass in every fixed sharp-low band.
Its [common-source metric error bound](../../../Library/Dynamics/clason2021regularization.md#a-compact-fit-has-a-fixed-error-on-the-whole-sharp-low-sphere)
tests uniform approximation by the bounded-window compact fit on the
whole centered low sphere. This conditional paper interface preserves
individual-input convergence and noncompact alternatives; it supplies
no inverse divergence, actual cofinal signs, half-bound or RH/Robin
conclusion, and has no new Lean certification or originality claim.

Under the inherited whole-critical-domain, mixed-nullity and
metric-coercivity premises, the [actual endpoint synthesis](../../../Library/Dynamics/clason2021regularization.md#a-bounded-synthesis-from-the-actual-endpoint-translations)
leaves a Hilbert–Schmidt residual on every fixed even sharp-low band,
and its [corrected common-source fit](../../../Library/Dynamics/clason2021regularization.md#a-corrected-fit-converges-uniformly-at-each-fixed-band)
converges uniformly on that band's whole centered unit sphere.
The principal synthesis retains the infinite translation tail; it is
noncompact. This conditional paper construction supplies no effective
regularization or growing-band rate, finite all-input acquisition,
actual cofinal signs, half-bound or RH/Robin conclusion, and has no
new Lean certification or originality claim.


The [actual endpoint-jet and original-form residual interface](../../../Library/Dynamics/clason2021regularization.md#actual-endpoint-jets-in-the-original-form)
extends that conditional construction with spatial/parameter jet bounds,
original-form-norm tail and midpoint allowances, and the
[existing common-source certificate on the sampled residual columns](../../../Library/Dynamics/clason2021regularization.md#pay-the-finite-remainder-with-the-existing-common-source-certificate).
The principal synthesis remains infinite; only its compact residual is
truncated. An actual simultaneous residual Gram and the growing-band
coefficient cost still require certification. This is conditional paper
analysis with unevaluated constants, without an effective regularization
rate, new numerical or Lean result, actual cofinal signs, half-bound,
Robin or RH conclusion.


The [actual complex endpoint parameter](../../../Library/Dynamics/clason2021regularization.md#the-actual-normalized-endpoint-columns-have-a-complex-parameter-strip)
extends the original normalized theta columns using a zero-free bilinear
normalization, rather than a holomorphic ordinary norm. Its
[high-order residual interface](../../../Library/Dynamics/clason2021regularization.md#apply-existing-analytic-approximation-to-the-actual-compact-residual)
reuses Cauchy/Taylor and Legendre/Bessel tools on separately analytic
kernel pieces, with sufficient parameter and residual-column-count
bounds. It preserves the original critical/minimal-form premises, one
coefficient map and simultaneous complex Gram, and the infinite
principal synthesis. Constants and actual residual Grams remain
uncertified; this conditional paper analysis supplies no numerical
runtime, effective regularization rate, new Lean result, actual cofinal
signs, all-input half-bound, Robin or RH conclusion.


The [two actual midpoint residual columns](theta-profile-residual-gram.md)
acquire a first full-space simultaneous complex-coefficient Gram for
the left J4 profiles at centers 0 and 1/2, with widths 1/2 and zero
primal/dual witnesses. Fresh original negative-edge actions, common
cross entries, whole-cell derivative transport and both tails give
a positive upper Gram with norm below 0.001698. The interior enclosure
error dominates this coarse baseline. The complete growing family,
common coefficient cost and cofinal signs remain unresolved. The old quadratic rows and grid producers are unused;
there is no new Lean, original half-bound, Robin or RH result.

The [shared critical and dual correction](theta-shared-witness-correction.md)
uses one legitimate critical vector and one individual real-Xi dual for
these same two columns. Direct full-cell transport, row-specific endpoint
inflation and complete tails give a positive joint upper Gram below
0.000981, against a same-method offset-centered zero control below
0.001523. The ratio of the directed upper allowances is below 0.65;
this does not order the true residual norms. The direct producer reuses
the profile and fresh witness midpoint actions, with no additional
metric-action callbacks. Existing J5 conversion gives a subblock cost
below 3.133 times the coefficient-map norm. Full-family convergence,
common-sequence signs, the original half-bound, Robin, RH and Lean
certification remain unresolved.


The [explicit actual-endpoint constants](../../../Library/Dynamics/clason2021regularization.md#explicit-original-series-constants-for-the-actual-endpoint-strip)
reuse the relative theta remainder and original derivative polynomials.
The [two-rate normalization bound](../../../Library/Dynamics/clason2021regularization.md#retain-both-actual-endpoint-decay-rates)
and [directed caps](../../../Library/Dynamics/clason2021regularization.md#directed-caps-for-the-same-endpoint-choice)
give a sufficient endpoint threshold 58 and normalized error cap below 920,
with $R_0=59$. The [producer](theta_endpoint_constants.py) and
[result](theta-endpoint-constants-result.json) preserve the actual model
and supply conservative WF2 coefficient caps. They acquire scalar constants,
not actual column/functional enclosures or a simultaneous Gram. Critical
membership applies to actual normalized columns; the ideal profiles
belong to the original form domain. Source/archimedean costs, common
cofinal signs, the all-input half-bound, Robin, RH and Lean certification
remain unresolved.

From the repository root, with Python 3.10+ and python-flint 0.9.0:

```sh
python docs/reports/theta-mixed-matrix/theta_endpoint_constants.py --output docs/reports/theta-mixed-matrix/theta-endpoint-constants-result.json
```

The cached declared runtime may also be invoked with
`uv run --offline --no-project --python 3.13 --with python-flint==0.9.0`
before that command. This producer is verified on the local macOS host,
including a different working directory, paths with spaces and a shell
without startup files; the portable fixture reproduces the result bytes.
No numerical acquisition or platform execution is inferred from CI.

## Conservative WF2 coefficients and absolute endpoint allowances

The same scalar producer applies the existing
[WC2 bounds](../../../Library/Analytic/romik2021orthogonal.md)
to the original [WF2 comparison](../../../Library/Weil/fukushima2011dirichlet.md#transformed-form-and-a-global-derivative-comparison).
It supplies conservative enlarged coefficients under those original-model
premises; it does not measure the exact operator norm or introduce a new
form comparison theorem. No previous derivative or translation grid runs.

Let $b=3/8$, $r=e^{-2b}$ and use the existing full-positive-line caps
$K_0,K_1$. WC2 gives

$$
\|s\|_\infty^2\le K_0^2r,\qquad
\|s'\|_\infty^2\le K_1^2r.
$$

The complete prime operator has $b_n(x)=w_ns(x)s(x+\log n)$,
with every prime-power weight $w_n=\Lambda(n)/\sqrt n\le n$.
Using $e^{2|x|}+e^{2|x+\log n|}\ge2n$ and retaining both shifted
directions in the existing operator-norm sum gives

$$
B_{\rm cap}=2K_0^2\left(\frac r{(1-r)^2}-r\right)
\ge\|B_{\rm complete\ prime}\|.
$$

The integer-edge majorant includes every prime power. This is WF1's
complete prime operator, not the negative-edge metric operator called
$B$ in the critical-source correction.

For $K=128$ put

$$
\overline M_2=\sum_{k=0}^K\frac2{(2k+1/2)^3}
               +\frac1{2(2K+1/2)^2}.
$$

The decreasing-tail integral bounds $M_2\le\overline M_2$.
Thus the unchanged WF2 inequality can use the enlarged coefficients

$$
\overline c_0=\frac32+B_{\rm cap}+2\overline M_2K_1^2r,
\qquad
\overline c_1=2\overline M_2K_0^2r.
$$

The directed result gives the strict caps

$$
\overline M_2<16.166,\quad B_{\rm cap}<13.532,\quad
\overline c_0<154091,\quad\overline c_1<84.394.
$$

Substitution in the already derived endpoint formulas, with the same
$R_*=58$, $R_0=59$ and $d=1/16$, supplies the absolute allowances

$$
M_\theta<117.074,\qquad C_d<70582.145.
$$

Here the producer evaluates $M_-$, $C_+$ and $C_-$ with the two
coefficients separately, and uses $\sqrt{\overline c_0+\overline c_1}$
as a conservative bound for $c_F$. The bounds apply to the existing
analytic residual columns and $d(T)\le C_de^{-T}$ for $T>R_0$, $T\ge1$;
they are not actual sampled column norms or residual errors. The retained
endpoint scalar records and supplier hashes are unchanged.

Actual column and coefficient-functional enclosures, one simultaneous
primal/dual complex Gram, the infinite noncompact principal contribution,
source/archimedean costs and signs on one original common cofinal sequence
still require work. These scalar instantiations supply no runtime,
optimality, Lean, all-input half-bound, Robin or RH certificate.

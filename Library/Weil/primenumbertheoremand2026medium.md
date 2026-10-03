---
bibkey: primenumbertheoremand2026medium
authors: PrimeNumberTheoremAnd contributors
year: 2026
title: PrimeNumberTheoremAnd -- Medium prime number theorem
doi: null
url: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01
claim: The Chebyshev psi function has an error of order x times exp(-c (log x)^(1/10)) for some positive c, using compactly supported Mellin smoothing and contour estimates.
strata_touched:
  - D5/S3/Weil/PrimeNumberTheorem/MellinCalculus
  - D5/S3/Weil/PrimeNumberTheorem/Smooth1
  - D5/S3/Weil/PrimeNumberTheorem/PntSmoothing
  - D5/S3/Weil/PrimeNumberTheorem/PntTail
  - D5/S3/Weil/PrimeNumberTheorem/PntLongVertical
  - D5/S3/Weil/PrimeNumberTheorem/PntShortContour
  - D5/S3/Weil/PrimeNumberTheorem/PntContourBound
  - D5/S3/Weil/PrimeNumberTheorem/MediumPNT
license: Apache-2.0
triage: anchor
---

# Medium prime number theorem

## Locator

https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01

The immutable source tree contains `PrimeNumberTheoremAnd/MellinCalculus.lean` and `PrimeNumberTheoremAnd/MediumPNT.lean`, the consumed sources for the medium prime number theorem.

Source: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01

The immutable source uses Lean 4.32.2 and Mathlib
905b95818eb32af7874a58b427f50c1711a5e96c. Its consumed mathematical source is
PrimeNumberTheoremAnd/MellinCalculus.lean and
PrimeNumberTheoremAnd/MediumPNT.lean. The upstream tree contains the root
LICENSE and no NOTICE file. Copyright the PrimeNumberTheoremAnd contributors.

The port has compactly supported Mellin convolution, smoothing kernels,
Chebyshev vertical integrals, contour pieces, and twelve analytic declarations.
It reuses the repository's ZetaPntBase and ZetaPntBounds sources. This source distribution is modified from the cited source.
The theorem's logarithmic exponent is one tenth; it does not assert the optimal
classical error exponent or an explicit value of its positive decay constant.

Retirement requires equivalent declarations in the Mathlib revision actually
adopted by this repository, with direct applications preserving the original
quantified contracts and standard axiom closure. At that point consumers use
those declarations directly and the redundant local port is removed. An
unadopted upstream revision or acceptance elsewhere does not meet this condition.

## Mathematical contracts

The consumed definitions and bounds below are from the immutable
PrimeNumberTheoremAnd source cited above. The corresponding local port is in
`D5/S3/Weil/PrimeNumberTheorem/`; the exact statement types and proofs remain
in those Lean modules. These are classical analytic inputs, not new theorems
of the golden cubic block theory. Each displayed contract retains its own
quantified hypotheses and parameters.

## Mathematical conventions and definitions

Write $\zeta$ for the ordinary Riemann zeta function, $\zeta'$ for its complex
derivative, and

$$
\psi(X)=\sum_{1\leq n\leq\lfloor X\rfloor}\Lambda(n),
$$

where $\Lambda$ is the von Mangoldt function; the sum is empty if its upper
limit is less than one. Let $i^2=-1$. For a function $f$ on the positive real
axis, its complex Mellin transform is

$$
\mathcal M f(s)=\int_0^\infty x^{s-1}f(x)\,dx.
$$

The real kernel is coerced into the complex numbers when the transform is
applied to it. Support means the set where a function is nonzero. All set
integrals in the contracts use Lebesgue measure; finite integrals
$\int_a^b$ are oriented interval integrals. In Lean notation `Icc`, `Ioo`,
`Ioc`, `Iic`, `Ici`, and `uIcc` mean closed, open, left-open right-closed,
closed lower half-line, closed upper half-line, and unordered closed intervals,
respectively. `ContDiff ℝ 1 ν` means that $\nu$ is once continuously
differentiable. `HolomorphicOn f K` means complex differentiability on $K$,
namely `DifferentiableOn ℂ f K`. The complex rectangle $[a,b]\times_{\mathbb C}
[c,d]$ consists of complex numbers with real part in the first interval and
imaginary part in the second.

For a complex-valued integrand $h$, the normalized vertical integral used here
is

$$
V'(h,\sigma)=\frac{1}{2\pi i}\,i\int_{\mathbb R}h(\sigma+it)\,dt.
$$

This is `VerticalIntegral' h σ`. The contour normalization and its orientation
are part of every definition below; no unsigned path-length replacement is
intended. The functions and predicates are defined for all displayed real
parameters. Conditions such as $\epsilon>0$, $X>3$, or unit mass are imposed
only in the individual theorem that requires them. In particular, support does
not silently imply nonnegativity, smoothness, or unit mass.

The exact definition fragments and theorem type fragments use the following
notation. They specify mathematical contracts and are not standalone proof
files.

```lean
open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev ContDiff
local notation "𝓜" => mellin
local notation "Λ" => vonMangoldt
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ
variable {𝕂 : Type*} [RCLike 𝕂]
```

**MellinConvolution.** Multiplicative convolution of $f,g:\mathbb R\to\mathbb K$, where $\mathbb K$ is an `RCLike` scalar type, integrates $f(y)g(x/y)$ against $dy/y$ over $y>0$.

```lean
noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y
```

**DeltaSpike.** The dilation kernel associated with a real kernel $\nu$ is $\Delta_{\nu,\epsilon}(x)=\nu(x^{1/\epsilon})/\epsilon$. Its total real-power definition is the one displayed below; its analytic uses impose the required positive-parameter conditions.

```lean
noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε
```

**Smooth1.** The smoothed indicator $S_{\nu,\epsilon}$ is the multiplicative convolution of the indicator of $(0,1]$ with $\Delta_{\nu,\epsilon}$.

```lean
noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)
```

**SmoothedChebyshevIntegrand.** For a real smoothing kernel $\nu$, write $h_{\nu,\epsilon,X}(s)$ for minus the logarithmic derivative of zeta times $\mathcal M(S_{\nu,\epsilon})(s)X^s$. Complex powers and the coercion of the real smoothed indicator are exactly as displayed.

```lean
noncomputable abbrev SmoothedChebyshevIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s
```

**SmoothedChebyshev.** The smoothed Chebyshev reading is $V^{\prime}\!\left(h_{\nu,\epsilon,X},1+(\log X)^{-1}\right)$, using the normalized vertical integral defined above.

```lean
noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)
```

**I₁.** $I_1$ is the lower infinite vertical tail on the line of real part $1+(\log X)^{-1}$, with imaginary parameter $t\leq-T$.

```lean
noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))
```

**I₂.** $I_2$ is the horizontal piece at imaginary part $-T$, oriented from real part $\sigma_1$ to $1+(\log X)^{-1}$.

```lean
noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))
```

**I₃₇.** $I_{37}$ is the complete finite vertical piece on the line of real part $\sigma_1$, oriented from imaginary part $-T$ to $T$.

```lean
noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))
```

**I₈.** $I_8$ is the horizontal piece at imaginary part $T$, oriented from real part $\sigma_1$ to $1+(\log X)^{-1}$.

```lean
noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))
```

**I₉.** $I_9$ is the upper infinite vertical tail on the line of real part $1+(\log X)^{-1}$, with imaginary parameter $t\geq T$.

```lean
noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))
```

**I₃.** $I_3$ is the lower finite vertical piece on the line of real part $\sigma_1$, oriented from imaginary part $-T$ to $-3$.

```lean
noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))
```

**I₇.** $I_7$ is the upper finite vertical piece on the line of real part $\sigma_1$, oriented from imaginary part $3$ to $T$.

```lean
noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))
```

**I₄.** $I_4$ is the short horizontal piece at imaginary part $-3$, oriented from real part $\sigma_2$ to $\sigma_1$.

```lean
noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))
```

**I₆.** $I_6$ is the short horizontal piece at imaginary part $3$, oriented from real part $\sigma_2$ to $\sigma_1$.

```lean
noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))
```

**I₅.** $I_5$ is the central finite vertical piece on the line of real part $\sigma_2$, oriented from imaginary part $-3$ to $3$.

```lean
noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))
```

**LogDerivZetaHasBound.** The predicate $\mathsf{ZetaBound}(A,C)$ requires $|\zeta'(\sigma+it)/\zeta(\sigma+it)|\leq C(\log|t|)^9$ for every real $\sigma,t$ with $3<|t|$ and $\sigma\geq1-A/(\log|t|)^9$. It has no hidden upper bound on $\sigma$.

```lean
def LogDerivZetaHasBound (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9
```

**LogDerivZetaIsHoloSmall.** The predicate $\mathsf{SmallHolo}(\sigma_2)$ requires the logarithmic derivative to be holomorphic on the unordered closed rectangle with real endpoints $\sigma_2,2$ and imaginary endpoints $-3,3$, with the point one removed.

```lean
def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})
```

## Consumed analytic estimates

The following twelve clauses retain their own hypotheses independently. Their
exact contracts are displayed to fix the quantifier order, parameter dependence,
strict inequalities, orientations, and zero-free or holomorphic assumptions.

**Vertical-strip Mellin decay.** For every once continuously differentiable real kernel supported in [1/2, 2], one positive constant bounds its complex Mellin transform by that constant divided by the norm of the transform parameter. The bound applies uniformly when the real part is positive and at most two.

The exact quantified contract is:

```lean
lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹
```

**Exact lower smoothing threshold.** A kernel supported in [1/2, 2] with unit multiplicative Haar mass gives a smoothed indicator equal to one for positive x at most 1 minus epsilon times log two, for every positive epsilon.

The exact quantified contract is:

```lean
lemma Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1
```

**Exact upper smoothing threshold.** For a kernel supported in [1/2, 2] and epsilon strictly between zero and one, the smoothed indicator vanishes when x is at least 1 plus twice epsilon times log two.

The exact quantified contract is:

```lean
lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0
```

**Mellin transform of the smoothed indicator.** For a once continuously differentiable kernel supported in [1/2, 2], every positive epsilon and every complex s with positive real part, the Mellin transform of the smoothed indicator equals the Mellin transform of the kernel at epsilon times s divided by s.

The exact quantified contract is:

```lean
lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)
```

**Continuity of the smoothed indicator.** For a nonnegative once continuously differentiable kernel supported in [1/2, 2] and every positive epsilon, its smoothed indicator is continuous at every positive argument.

The exact quantified contract is:

```lean
lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y
```

**Chebyshev smoothing error.** For a nonnegative once continuously differentiable kernel supported in [1/2, 2] with unit multiplicative Haar mass, one positive constant bounds the smoothing error by C times epsilon times X times log X, whenever X is greater than three, epsilon lies strictly between zero and one, and X times epsilon is greater than two.

The exact quantified contract is:

```lean
theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X
```

**Lower vertical-tail bound.** For a nonnegative once continuously differentiable kernel supported in [1/2, 2] with unit multiplicative Haar mass, one positive constant bounds the first vertical tail by C times X times log X divided by epsilon times T, whenever X and T are greater than three and epsilon lies strictly between zero and one.

The exact quantified contract is:

```lean
theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)
```

**Long horizontal-tail bound.** For a once continuously differentiable kernel supported in [1/2, 2], a positive logarithmic-derivative bound constant, and A strictly positive and at most one half, one positive constant bounds the horizontal tail by C times X divided by epsilon times T. The left endpoint is 1 minus A divided by the ninth power of log T; X and T exceed three and epsilon lies strictly between zero and one.

The exact quantified contract is:

```lean
lemma I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)
```

**Long vertical bound.** Under the same kernel, positive zeta-bound constant, and A conditions as the horizontal estimate, one positive constant bounds the long vertical piece by C times X times X to the power minus A divided by the ninth power of log T, divided by epsilon. The same endpoint and parameter restrictions apply.

The exact quantified contract is:

```lean
theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε
```

**Short horizontal bound.** For a once continuously differentiable kernel supported in [1/2, 2], a small-strip holomorphic logarithmic derivative, a lower real part strictly between zero and one, and A strictly positive and at most one half, there are a nonnegative bound constant and a T threshold greater than three. Above that threshold the short horizontal piece satisfies the stated logarithmic-power bound for X greater than three and epsilon strictly between zero and one.

The exact quantified contract is:

```lean
lemma I4Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε
```

**Contour deformation bound.** For a nonnegative once continuously differentiable kernel supported in [1/2, 2] with unit multiplicative Haar mass and a small-strip holomorphic logarithmic derivative, there is a positive constant for the central vertical piece. Under both explicit punctured-rectangle holomorphy assumptions and the stated strict parameter ordering, the error from the Mellin mass term is at most the sum of the eight remaining contour norms and that central bound.

The exact quantified contract is:

```lean
theorem SmoothedChebyshevContourBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    {σ₂ : ℝ} (holoSmall : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1) :
    ∃ C₅ > 0, ∀ (X ε T σ₁ : ℝ), 3 < X → 0 < ε → ε < 1 → 3 < T →
      0 < σ₁ → σ₁ < 1 → σ₂ < σ₁ →
      HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2 ×ℂ Icc (-T) T) \ {1}) →
      HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
        (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) →
      ‖SmoothedChebyshev SmoothingF ε X -
          𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X‖ ≤
        ‖I₁ SmoothingF ε X T‖ + ‖I₂ SmoothingF ε T X σ₁‖ +
        ‖I₃ SmoothingF ε T X σ₁‖ + ‖I₄ SmoothingF ε X σ₁ σ₂‖ +
        C₅ * X ^ σ₂ / ε + ‖I₆ SmoothingF ε X σ₁ σ₂‖ +
        ‖I₇ SmoothingF ε T X σ₁‖ + ‖I₈ SmoothingF ε T X σ₁‖ +
        ‖I₉ SmoothingF ε X T‖
```

**Quantitative prime number theorem.** There exists a positive real c such that the second Chebyshev function minus the identity is bounded asymptotically by a constant times x times exp of minus c times the one-tenth power of log x. Neither c nor the eventual multiplicative bound is asserted to be explicit.

The exact quantified contract is:

```lean
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))
```

The first five estimates use compact support, changes of variables in
multiplicative convolution, integration by parts, and dominated convergence.
The sixth compares Mellin inversion with the von Mangoldt sum and controls the
transition region. The remaining intermediate estimates use the same actual
smoothed integrand, the specified zeta logarithmic-derivative bounds, and
punctured-rectangle contour deformation. Conjugation relates the upper and
lower pieces. The final theorem chooses the smoothing and truncation parameters
together, constructs a nonnegative smooth kernel of unit mass, and combines the
smoothing error with the contour estimates. These are the classical analytic
proofs in the cited source.

## Apache-2.0 license

The complete immutable upstream LICENSE follows verbatim.

```text
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
```

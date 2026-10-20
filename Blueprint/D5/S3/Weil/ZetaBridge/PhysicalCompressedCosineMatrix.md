# Physical Compressed Cosine Matrix

## Abstract

This source formalizes the exact physical correlation on the original half-open interval
`Ioc (-a) a`. A mode is extended by the original indicator zero extension before either
translated copy is evaluated. The whole-line pairing therefore sees the actual overlap
`Ioc (max (-a) (-a-s)) (min a (a-s))`, including empty overlap, touching support, and
both support endpoints. No periodic interval or wrapped translation is used.

For every real frequency pair and shift, the cosine product integral is the sum of the
`u-v` and `u+v` channels with the scaled sinc `S H r = H*sinc(rH)`. The definition
includes the removable zero-frequency value, so both resonances, the zero modes, and
`H=0` are covered. The normalized frequencies are
`omega(a,n)=2*pi*n/(2*a)` and the mode amplitude is `1/sqrt(2*a)` at zero and
`sqrt(2/(2*a))` otherwise. For `a>0`, the retained matrix is the exact compressed
pairing for every signed real shift; it is zero at and beyond both support boundaries,
is even in the shift, symmetric in the mode indices, and has the identity value at
zero shift. The diagonal and off-diagonal formulas are consequences of the same
matrix formula; the diagonal keeps the negative sine term.

## Physical definitions

`window a = Ioc (-a) a` and
`zeroExtension a f = (window a).indicator f`.

`compression a s f x = zeroExtension a (fun y => zeroExtension a f (y+s)) x`.
Thus the translated function is compressed twice, with no endpoint trace assumption.

`pairing a s f g = ∫ x, f x * compression a s g x` over Lebesgue measure. The
kernel is exactly the indicator of the overlap above, yielding
`pairing a s f g = ∫ x in overlap a s, f x * g (x+s)` and, for `0≤s≤2a`,
`∫ x in (-a)..(a-s)`. For `s≤0` and `-(2a)≤s` the interval is
`(-a-s)..a`; outside these bounds the pairing is zero. Reflection is proved on
ordinary interval integrals for even functions, so `pairing a (-s) f g = pairing a s f g`.

`S H r = H * Real.sinc (r*H)`, with `S H 0=H`, `S 0 r=0`, and `S H (-r)=S H r`.
The exact centered integral is
`∫[-H,H] cos(r*y+t) = 2*cos(t)*S H r`.
Consequently
```
∫[-H,H] cos(u*(y-s/2))*cos(v*(y+s/2))
 = cos((u+v)s/2)*S H (u-v)
 + cos((u-v)s/2)*S H (u+v).
```
The midpoint substitution is an ordinary interval change of variables. It is not a
periodic translation.

For `a>0`,
`omega a n = 2*pi*n/(2*a)`,
`amplitude a 0 = 1/sqrt(2*a)`, and
`amplitude a n = sqrt(2/(2*a))` for `n≠0`.
The real mode is `mode a n x = amplitude a n*cos(omega a n*x)`, and
`matrixEntry a n m s = pairing a s (mode a n) (mode a m)`.
The retained matrix uses `|s|` when `|s|≤2a` and is zero otherwise:
```
matrix a n m s = amplitude(a,n)*amplitude(a,m) *
 ( cos((ωn+ωm)|s|/2)*S((2a-|s|)/2)(ωn-ωm)
 + cos((ωn-ωm)|s|/2)*S((2a-|s|)/2)(ωn+ωm) ).
```
The theorem `matrixEntry_eq_matrix` proves this for all `s∈ℝ`, under only `0<a`.
The zero row, zero-zero value `1-s/(2a)`, resonant positive diagonal, off-diagonal
formula, support boundary, symmetry, and zero-shift Kronecker value are all compiled
consequences. No positivity or diagonality assumption is made.

## Complex finite profiles and prime action

For a finite `A : Finset ℕ` and arbitrary `v : ℕ→ℂ`,
`profile a A v x = ∑ n∈A, v n * (mode a n x : ℂ)`.
The exact finite expansion retains every term:
```
pairing a s (conj(profile a A v)) (profile a A v)
 = ∑ n∈A ∑ m∈A (conj(v n)*v m) * (matrixEntry a n m s : ℂ).
```
The matrix symmetry proves this complex value is real; no cross term is removed.

The original arithmetic weight is `primeWeight r = vonMangoldt r / sqrt r` and the
finite action is
```
primeAction a M f x = ∑ r∈Icc 1 M primeWeight(r) *
 (compression a (log r) f x + compression a (-log r) f x).
```
On `window a` this is exactly the existing `primeSymmetric` applied to the zero
extension. `primeCutoff a = floor(exp(2*a))`; terms above it vanish by the original
compression, including the equality boundary through the empty overlap. The finite
quadratic form is integrated on the physical window and, for an even continuous
profile, equals the signed factor-two sum over `Icc 1 (primeCutoff a)`.

The canonical complex identity is
```
∫window conj(profile) * primeAction(profile)
 = 2 * ∑r∈Icc 1 primeCutoff, primeWeight(r) *
     ∑n∈A ∑m∈A (conj(v n)*v m) * (matrix(a,n,m,log r) : ℂ).
```
Its real-part form keeps `Re(conj(v n)*v m)` for every mixed pair, and the full complex
value is proved equal to the real scalar expression. The Weil arithmetic component
uses the existing `-primeSymmetric` and is exactly the negative of this real quadratic
form. The source asserts no Gamma or pole contribution and no Riemann-hypothesis claim.

## Formalization

`D5/S3/Weil/ZetaBridge/PhysicalCompressedCosineMatrix.lean` contains the definitions and
proofs above, including `pairing_overlap`, `pairing_physical`,
`integral_cos_product_overlap`, `matrixEntry_eq_matrix`, `profile_pairing`,
`finite_prime_quadratic`, `finite_prime_quadratic_real`, and
`finite_weil_prime_quadratic`.

## Scope boundaries

All statements are finite and exact in Lean's Lebesgue integral over `ℝ`. They preserve
`Ioc (-a) a`, the original zero extension, signed shifts, support touching and beyond
support, all resonances, exact von Mangoldt prime powers, conjugation, the negative Weil
sign, factor two, and the floor exponential cutoff. They add no periodic surrogate,
trace/smoothness premise, matrix positivity, or spectral/RH conclusion.

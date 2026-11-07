---
bibkey: kowalski2021exponentialsums
authors: Emmanuel Kowalski
year: 2021
title: "Exponential sums over finite fields: elementary methods"
doi: null
url: https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf
claim: "Theorem 2.19 evaluates Salie sums over every odd finite field and gives the bound 2 sqrt(q); Remark 2.20 attributes the elementary additive Fourier method to Sarnak."
strata_touched:
  - D5/S3/Arith/CharacterSums/SalieSum
license: citation-only
triage: anchor
---
<!-- GID: D5/L/CharacterSums/kowalski2021exponentialsums -->
# Salié evaluation over odd finite fields

## Verified locator

https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf

The verified version is September 14, 2021, 94 PDF pages. Definition 2.1
and Remark 2.2, printed page 17 (PDF page 19), define the unnormalised
Gauss sum over nonzero field elements. Extending the nontrivial quadratic
character by zero gives the same sum over the whole field.

Definition 2.18 and Theorem 2.19, equations (2.12)-(2.13), printed page 26
(PDF page 28), state the Salié evaluation and square-root bound over every
odd finite field, with both additive characters nontrivial. The proof ends
on printed page 27 (PDF page 29), including exact vanishing for a nonsquare
root parameter. Remark 2.20 on that page attributes the elementary additive
Fourier proof to Sarnak and cites Iwaniec-Kowalski, *Analytic Number Theory*,
Lemma 12.4. That book locator is Kowalski's attribution, not a separate
verification of the book.

## Parameter correspondence and boundaries

Write the repository sum as
`S(psi,a,b) = sum_x chi(x) psi(a*x+b/x)` and its Gauss sum as `G(psi)`.
For `a*b` nonzero, inversion of `x` exchanges `a` and `b`, since the
quadratic character is invariant under inversion. Apply Theorem 2.19 with
its first additive character `phi(x)=psi(b*x)`, its second character
`eta(x)=psi(a*x)`, and its parameter `a/b`. Its Gauss sum is
`chi(b)*G(psi)`. The change of variable `y=b*t` carries `t^2=4*a/b` to
`y^2=4*a*b`, and `phi(t)=psi(y)`. Thus the repository normalization is
`S(psi,a,b)=chi(b)*G(psi)*sum_[y^2=4*a*b] psi(y)` for `b` nonzero.

The source theorem assumes both characters nontrivial. The elementary
extension `a=0,b` nonzero follows from inversion and the Gauss shift law:
the quadratic root fiber is `{0}`, and `S(psi,0,b)=chi(b)*G(psi)`.
The separate boundary `b=0,a` nonzero is the shifted Gauss sum
`chi(a)*G(psi)`; `a=b=0` gives zero by quadratic-character orthogonality.
The Lean boundary with `b=0` permits even a trivial additive character.
For nontrivial `psi`, the Gauss norm and these boundary evaluations extend
the bound to all `a,b`.

The quadratic root fiber has a stationary interpretation only when
`a*b` is nonzero: `y=2*a*x` identifies it with `a*x^2=b` on the units.
For `a=0,b` nonzero there is no stationary point on the units, despite
the algebraic root zero. No novelty or non-binding admission is asserted
for the classical evaluation, its stated boundary extensions or its bound.

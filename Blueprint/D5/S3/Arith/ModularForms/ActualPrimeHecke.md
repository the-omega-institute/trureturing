# Actual Prime Hecke Action

## Abstract

The actual prime Hecke endomorphism, its complete finite representatives, and its analytic coefficient law.

**Theorem 1.1 (Actual prime Hecke endomorphism).**

$$\operatorname{primeHecke} : CuspForm \Rightarrow CuspForm$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p and an integer weight k, this is the complex-linear map obtained by translating by the rational diagonal p-isogeny matrix and applying Mathlib's finite-index cusp-form trace. The codomain is the level-one CuspForm space itself; the trace construction supplies holomorphy and vanishing at every cusp.

**Theorem 1.2 (The full p+1 action).**

$$(T_{p} f)(z) = p^{k - 1} \cdot \operatorname{f}\left(p \cdot z\right) + \frac{1}{p} \cdot \sum_{a \in \operatorname{Fin}\left(p\right)} \operatorname{f}\left(\frac{z + a}{p}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke_action` (`✓ std3`). ∎

*Citation.* Kenneth A. Ribet and William A. Stein (2017). *Lectures on Modular Forms and Hecke Operators*. URL: <https://wstein.org/books/ribet-stein/main.pdf>.

*Commentary.*

For every prime p, including 2, every integer weight k and every upper-half-plane point z, the actual trace equals p^(k-1) times f(pz) plus p^(-1) times the sum of f((z+a)/p) over a in Fin p. Both points have explicit positivity proofs. Mathlib uses inverse representatives: 1 and (S T^a)^(-1). The actual slash normalization gives these factors without any weight restriction.

The representative map primeTraceEquiv is a proved bijection from Fin p plus Unit onto the actual quotient in the trace. Its coverage and uniqueness are consumed by the trace reindexing.

Ribet and Stein, Lectures on Modular Forms and Hecke Operators, January 12, 2017 version, Proposition 3.5.2, printed p. 20, classifies the triangular representatives. Section 3.5.2, printed pp. 21–22, derives the n^(k-1) d^(-k) normalization and this prime action. The inverse-representative quotient bijection and its Mathlib trace realization are repository implementations of that classical action.

**Theorem 1.3 (The actual congruence intersection).**

$$\operatorname{mapGL}\left(s\right) \in \operatorname{primeHeckeSubgroup}\left(p\right) \Leftrightarrow s \in \Gamma_{0}(p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHeckeSubgroup_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integer determinant-one matrix s, its real image belongs to the conjugate by diag(p,1)^(-1) of SL2(Z) exactly when its lower-left entry is divisible by p. This identifies the actual trace intersection with Gamma0(p). Coverage and uniqueness of the representatives are proved from this entry criterion, using ZMod p as a field; no representative frame is assumed.

**Theorem 1.4 (The analytic coefficient law).**

$$\operatorname{a}\left(T_{p} f, n\right) = \operatorname{a}\left(f, p \cdot n\right) + p^{k - 1} \cdot (\text{if} p \mid n \text{then} \operatorname{a}\left(f, \left\lfloor\frac{n}{p}\right\rfloor\right) \text{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke_qExpansion_coeff` (`✓ std3`). ∎

*Citation.* Kenneth A. Ribet and William A. Stein (2017). *Lectures on Modular Forms and Hecke Operators*. URL: <https://wstein.org/books/ribet-stein/main.pdf>.

*Commentary.*

Writing a(f,n) for coefficient n of the period-one analytic q-expansion, a(T_p f,n) = a(f,p*n) + p^(k-1) * (if p divides n then a(f,n/p) else 0). The theorem quantifies over every prime, every integer weight, every level-one cusp form and every natural coefficient index, including zero.

The proof uses Mathlib's HasSum theorem for the actual function at pz and at each (z+a)/p. The finite root-of-unity filter removes the nonmultiples of p. Finite sums of HasSum and injective integer-multiple reindexing preserve convergence; analytic coefficient uniqueness identifies the resulting coefficients. No formal-series recurrence or coefficient formula is a premise.

Ribet and Stein, Lectures on Modular Forms and Hecke Operators, January 12, 2017 version, section 3.5.2, printed pp. 21–22, derives this normalized prime coefficient law, including the constant coefficient. Proposition 3.5.2, printed p. 20, classifies representatives; it is not itself the coefficient theorem. The convergence and coefficient-uniqueness bridges are repository proofs using Mathlib. This is a reusable analytic library construction. It does not resolve Lehmer's conjecture; the coefficient relation allows a vanishing prime coefficient.

The four-slot escape audit is unfinished under the existing owner issue https://github.com/the-omega-institute/trureturing/issues/5214 (escape registration current interfaces). No declared_validated registration is claimed. Reg.Support.DependentFamily.enrollment_1 supplies a generic enrolled template, not a source registration of these Hecke statements.

For primeHecke_action, the missing evidence is whole-family role sensitivity, nonconstant actual analytic observation in each role, and a typed Contract.Registration with checked source-selection reconstruction. For primeHecke_qExpansion_coeff, it is whole-family role sensitivity, nonconstant actual coefficient observation in each role, and the same typed source-selection bridge. For primeHeckeSubgroup_mem, whole-family law variation, role sensitivity, actual observational dependence, and the typed Contract.Registration source-selection bridge remain unfinished.

The audit must retain every prime including 2, every integer weight, all level-one cusp forms and upper-half-plane points, and every natural coefficient index including 0. Weight and coefficient-index degeneracies remain in scope; no sensitivity at each fixed weight or index is asserted. The missing evidence establishes neither absence of a suitable template nor a mathematical failure of the Hecke laws.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke`
- Truth anchor: `D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHeckeSubgroup_mem`
- Truth anchor: `D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke_action`
- Truth anchor: `D5/S3/Arith/ModularForms/ActualPrimeHecke.primeHecke_qExpansion_coeff`

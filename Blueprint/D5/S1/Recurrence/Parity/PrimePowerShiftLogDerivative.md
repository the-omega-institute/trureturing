# Prime-Power Coefficient Equations and OEIS A393867

## Abstract

The nth prime divides the nth logarithmic-derivative term of OEIS A393866 for n greater than one.

The literature note hanna2026a393867 records Hanna's defining equations for A393866 and the divisibility conjecture in A393867. Here F denotes generatingSeries and L denotes logDerivative, both formal power series over the integers. All indices and exponents are natural numbers; subtraction in an index is natural subtraction. Coefficients and divisibility are over the integers, with natural primes cast to integers.

The notation C embeds an integer as a constant series. The operator derivative is the formal derivative over the integers, and invOfUnit(F,1) is the formal inverse with constant coefficient one. The operator div is integer division; every division used by the coefficient construction is exact.

**Definition 1.1 (The one-based prime index).**

$$\forall n: \mathbb{N}, \operatorname{prime}\left(n\right) = \operatorname{nth}\left(\operatorname{Prime}, n - 1\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.prime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib's nth operator uses a zero-based index, so prime(n) is Nat.nth Nat.Prime (n-1). The subtraction convention also defines prime(0).

**Theorem 1.2 (The prime exceeds its positive index).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (n < \operatorname{prime}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.lt_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's bound k+2 <= Nat.nth Nat.Prime k, with k=n-1, gives the strict inequality.

**Definition 1.3 (The integral coefficient construction).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n\right)\right)\\\operatorname{P}\left(0\right) = 1\\\forall k: \mathbb{N}, \operatorname{P}\left(k + 1\right) = \operatorname{P}\left(k\right) + \operatorname{C}\left(\operatorname{div}\left((\operatorname{prime}\left(k + 1\right) \cdot \operatorname{coeff}\left(k + 1 - 1, (\operatorname{P}\left(k\right))^{\operatorname{prime}\left(k + 1\right)}\right) - \operatorname{coeff}\left(k + 1, (\operatorname{P}\left(k\right))^{\operatorname{prime}\left(k + 1\right)}\right)), \operatorname{prime}\left(k + 1\right)\right)\right) \cdot (X)^{k + 1}\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write P(k) for the private approximation(k). Starting from P(0)=1, the displayed correction changes only degree k+1. In the binomial expansion of B^p=(1+(B-1))^p, the interior binomial coefficients are divisible by p and the pth power of B-1 has no coefficient below p. This proves exact divisibility of the correction numerator. Later approximations preserve every earlier coefficient.

**Definition 1.4 (The generating series).**

$$F = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series F is mk(a), the formal integer series with coefficient a(n) at degree n.

**Theorem 1.5 (The complete defining equations).**

$$(\operatorname{constantCoeff}\left(F\right) = 1) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, (F)^{\operatorname{prime}\left(n\right)}\right) = \operatorname{prime}\left(n\right) \cdot \operatorname{coeff}\left(n - 1, (F)^{\operatorname{prime}\left(n\right)}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two unit-constant series agree below degree n, the difference of their nth coefficients after taking the pth power is p times their original nth-coefficient difference. Factoring the difference of powers proves this identity. The exact correction therefore enforces the nth equation; coefficient stability transfers it to F.

**Theorem 1.6 (Uniqueness among integer series).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, (B)^{\operatorname{prime}\left(n\right)}\right) = \operatorname{prime}\left(n\right) \cdot \operatorname{coeff}\left(n - 1, (B)^{\operatorname{prime}\left(n\right)}\right))) \implies (B = F))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction compares B and F below each degree n. Their defining equations and the difference-of-powers coefficient identity imply prime(n) times the coefficient difference is zero. Cancellation of this nonzero integer proves equality at degree n.

**Theorem 1.7 (Low coefficients of a prime power).**

$$\forall n: \mathbb{N}, \forall j: \mathbb{N}, (1 \le j) \implies ((j < \operatorname{prime}\left(n\right)) \implies (\operatorname{prime}\left(n\right) \mid \operatorname{coeff}\left(j, (F)^{\operatorname{prime}\left(n\right)}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.prime_dvd_coeff_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the binomial divisibility argument to F itself. The bound 1 <= j < prime(n) excludes both exceptional binomial terms.

**Definition 1.8 (The logarithmic derivative).**

$$L = \operatorname{derivative}\left(\mathbb{Z}, F\right) \cdot \operatorname{invOfUnit}\left(F, 1\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.logDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Since F has constant coefficient one, multiplication by its formal unit inverse defines L=F'/F over the integers.

**Definition 1.9 (The sequence indexing).**

$$\forall n: \mathbb{N}, \operatorname{a393867}\left(n\right) = \operatorname{coeff}\left(n - 1, L\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.a393867` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A393867 starts at index one: its nth term is the coefficient of degree n-1 in L. Natural subtraction also specifies the value at zero.

**Theorem 1.10 (Differentiating every power).**

$$\forall n: \mathbb{N}, X \cdot \operatorname{derivative}\left(\mathbb{Z}, (F)^{n}\right) = \operatorname{C}\left(n\right) \cdot (X \cdot L) \cdot (F)^{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.log_derivative_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formal power rule and L times F equals F' give the displayed identity, including exponent zero.

**Theorem 1.11 (Hanna's divisibility conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{prime}\left(n\right) \mid \operatorname{a393867}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a393867-prime-power-shift-log-derivative` (proved) by `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a393867-prime-power-shift-log-derivative","declaration_gid":"D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A393867, logarithmic derivative of A393866 (g.f. with [x^n] A^prime(n) = prime(n) [x^(n-1)] A^prime(n))*. URL: <https://oeis.org/A393867>.

*Commentary.*

Let p=prime(n) and h(j) be the coefficient of degree j in F^p. Coefficient extraction from the power rule, followed by h(n)=p h(n-1) and cancellation of p, gives n h(n-1)=[x^(n-1)](L F^p). For n>1, the left side is divisible by p. In the convolution on the right, every term except [x^(n-1)]L times h(0) has a positive coefficient index below p in F^p and is divisible by p. Since h(0)=1, the remaining term proves the conjecture.

**Theorem 1.12 (The shifted printed formula is false).**

$$\neg (\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{prime}\left(n\right) \mid \operatorname{coeff}\left(n, L\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.printed_formula_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This companion concerns formula (2) of A393866, whose printed coefficient index is n instead of n-1. The first three defining equations give coefficients 1, 2, and 10 for F. Coefficient extraction from L F=F' then gives [x^2]L=25, which is not divisible by prime(2)=3. The separate oddness conjecture is not addressed.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.a`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.a393867`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.logDerivative`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.log_derivative_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.lt_prime`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.prime`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.prime_dvd_coeff_pow`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.printed_formula_false`

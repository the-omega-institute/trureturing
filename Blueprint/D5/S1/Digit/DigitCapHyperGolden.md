# Hyper-ell-ary expansions and the golden ratio

## Abstract

The digit cap ell at radix ell has upper growth exponent log_ell φ, for the count at n and for the hyper-expansion convention at n−1.

**Definition 1.1 (The exponent in the source convention).**

Lean statement: `D5/S1/Digit/DigitCapHyperGolden.hyperExponent`

*Formalization.* `D5/S1/Digit/DigitCapHyperGolden.hyperExponent` (`✓ std3`).

*Citation.* Michael Coons; Lukas Spiegelhofer (2017). *The maximal order of hyper-(b-ary)-expansions*. DOI: [10.37236/5441](https://doi.org/10.37236/5441). URL: <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v24i1p15>.

*Commentary.*

hyperExponent ell is the infimum over N≥2 of the supremum over n≥N of log b(n−1)/log n, where b counts representations with digits 0,…,ell. Coons and Spiegelhofer write s_ell(n) for the number of hyper-(ell-ary)-expansions of n−1.

**Definition 1.2 (The exponent log_ell φ).**

Lean statement: `D5/S1/Digit/DigitCapHyperGolden.claim`

*Formalization.* `D5/S1/Digit/DigitCapHyperGolden.claim` (`✓ std3`).

*Citation.* Michael Coons; Lukas Spiegelhofer (2017). *The maximal order of hyper-(b-ary)-expansions*. DOI: [10.37236/5441](https://doi.org/10.37236/5441). URL: <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v24i1p15>.

*Commentary.*

For every natural ell≥2, both the upper exponent of the cap ell at radix ell and hyperExponent ell equal log_ell φ with φ=(1+√5)/2. Theorem 1 (Defant) in Coons–Spiegelhofer gives the sharper statement that s_ell(m)/m^(log_ell φ) has limsup φ^(log_ell(ell^2−1))/√5.

**Theorem 1.3 (Proof by Fibonacci envelopes and alternating digits).**

Lean statement: `D5/S1/Digit/DigitCapHyperGolden.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapHyperGolden.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michael Coons; Lukas Spiegelhofer (2017). *The maximal order of hyper-(b-ary)-expansions*. DOI: [10.37236/5441](https://doi.org/10.37236/5441). URL: <https://www.combinatorics.org/ojs/index.php/eljc/article/view/v24i1p15>.

*Commentary.*

The lowest-digit recursion gives b(ell·q)=b(q)+b(q−1) and b(ell·q+r)=b(q) for 1≤r<ell. Of two consecutive integers at most one is divisible by ell, so if X bounds the pair window b(q)+b(q−1) and Y the single values below ell^m, then below ell^(m+1) the pair window is at most X+Y and the single values at most X. These Fibonacci envelopes give b(n)≤2·b(0)·φ^m for n<ell^(m+1), so log b(t)/log n≤log_ell φ+log(2·b(0))/log n whenever t≤n. Along quotients whose last digits alternate 0, 1 the pair window v(k) satisfies v(k+2)=v(k+1)+v(k) exactly, so φ·v(k)≥φ^k, and the readouts at n=ell·q(k) and at n=ell·q(k)+1 are at least log_ell φ·(k−1)/(k+2). A common squeeze of the infimum of tail suprema then gives log_ell φ in both conventions.

## References

- Truth anchor: `D5/S1/Digit/DigitCapHyperGolden.claim`
- Truth anchor: `D5/S1/Digit/DigitCapHyperGolden.hyperExponent`
- Truth anchor: `D5/S1/Digit/DigitCapHyperGolden.result`
- Dependency: [D5/S1/Digit/DigitCapSubcritical](DigitCapSubcritical.md)

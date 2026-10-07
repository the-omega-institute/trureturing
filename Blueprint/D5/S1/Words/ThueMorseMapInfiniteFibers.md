# Infinite Odd Fibers of Thue-Morse Maxima

## Abstract

Infinitely many exact global Thue-Morse maxima have infinite positive odd fibers.

**Definition 1.1 (The attained global maximum).**

$$\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; ExactMax\left(d, n\right) \Leftrightarrow \left(\left(\exists s \in \mathbb{N},\; MAP\left(d, s, n\right)\right) \land \left(\forall s \in \mathbb{N},\; \forall L \in \mathbb{N},\; MAP\left(d, s, L\right) \Rightarrow L \le n\right)\right)$$

*Formalization.* `D5/S1/Words/ThueMorseMapInfiniteFibers.ExactMax` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

MAP is reused from ThueMorseMapFirstStart, and thueMorse is the actual zero-indexed binary digit-parity word from ThueMorseReducedAbelianOdd. ExactMax(d,n) requires an attaining start and bounds every progression length at every natural start. The color at each start is unrestricted, so this maximum covers both letters of the entire infinite word.

**Definition 1.2 (Question 3.7, second clause).**

$$claim = \left(\forall N \in \mathbb{N},\; \exists n \in \mathbb{N},\; N < n \land \left(\forall D \in \mathbb{N},\; \exists d \in \mathbb{N},\; D < d \land \left(0 < d \land \left(Odd\left(d\right) \land ExactMax\left(d, n\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/ThueMorseMapInfiniteFibers.claim` (`✓ std3`).

*Citation.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

Joshi and Rust ask whether infinitely many n have O_max(n)=infinity. For natural differences, their assertion is exactly that infinitely many lengths have infinitely many positive odd differences with attained global maximum equal to that length. Infinitude is displayed here by unbounded quantifiers on the natural numbers. The other two clauses of Question 3.7 are outside this statement.

**Theorem 1.3 (Infinitely many infinite fibers).**

$$\forall N \in \mathbb{N},\; \exists n \in \mathbb{N},\; N < n \land \left(\forall D \in \mathbb{N},\; \exists d \in \mathbb{N},\; D < d \land \left(0 < d \land \left(Odd\left(d\right) \land ExactMax\left(d, n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ThueMorseMapInfiniteFibers.result` (`✓ std3`). ∎

*Resolves.* `Problems/joshi-rust-2025-thue-morse-infinite-odd-fibers` (proved) by `D5/S1/Words/ThueMorseMapInfiniteFibers.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"joshi-rust-2025-thue-morse-infinite-odd-fibers","declaration_gid":"D5/S1/Words/ThueMorseMapInfiniteFibers.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

Fix odd m>=3, M=2^m, c=M^2+M+1, B=2^(4m+1)=2M^4, a=c(M^2-1), and U=2B+2. The shared dyadic_block and top_parity suppliers in ThueMorseDyadic give a true triple at a,a+c,a+2c inside one B block, and t(cj)=t(j) for j<M. Since B and c are coprime, residue transport puts a monochromatic triple inside every U-letter c-spaced window. Such a window cannot be a color translate of consecutive Thue-Morse letters, which have no monochromatic triple.

For R=2^k>=2U+1,M and d=cR+1, divide any start by R. Among 2U+1 samples, either the first U precede the carry or U samples starting at the carry follow it. Binary block parity would make one of these segments the forbidden translated shadow. Thus every progression at every start has length at most 2U. Start zero attains length M. Maximizing the finite nonempty set of attained lengths gives an actual maximum in [M,2U], without assuming existence or using an explicit formula.

The eligible exponents form an infinite tail, their positive odd differences are distinct, and the possible maxima are finite. Finite pigeonhole supplies an infinite exact-max fiber at some n>=M. Choosing m=2h+3 makes these lower bounds unbounded, which yields infinitely many such lengths. This proof supplies no formula for the selected maxima and makes no priority or external acceptance claim.

## References

- Truth anchor: `D5/S1/Words/ThueMorseMapInfiniteFibers.ExactMax`
- Truth anchor: `D5/S1/Words/ThueMorseMapInfiniteFibers.claim`
- Truth anchor: `D5/S1/Words/ThueMorseMapInfiniteFibers.result`
- Dependency: [D5/S1/Words/ThueMorseMapFirstStart](ThueMorseMapFirstStart.md)

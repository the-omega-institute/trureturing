# First Longest Thue-Morse Progressions

## Abstract

First starts of longest Thue-Morse progressions at power-of-two differences.

**Definition 1.1 (A progression in the actual word).**

$$\forall d \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall L \in \mathbb{N},\; MAP\left(d, s, L\right) \Leftrightarrow \left(\forall j \in \mathbb{N},\; j < L \Rightarrow t\left(s + j \cdot d\right) = t\left(s\right)\right)$$

*Formalization.* `D5/S1/Words/ThueMorseMapFirstStart.MAP` (`✓ std3`).

*Citation.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

The word t is the zero-indexed binary digit-parity function thueMorse from ThueMorseReducedAbelianOdd, beginning 0110100110010110. False denotes 0 and true denotes 1. It satisfies t(0)=0, t(2u)=t(u), and t(2u+1)=1-t(u). MAP(d,s,L) says that the L letters at s, s+d, ..., s+(L-1)d all equal the letter at s. All indices and lengths are natural numbers.

**Definition 1.2 (An attained global maximum and its least start).**

$$\forall d \in \mathbb{N},\; \forall s \in \mathbb{N},\; FirstLongest\left(d, s\right) \Leftrightarrow \left(\exists L \in \mathbb{N},\; 0 < L \land \left(MAP\left(d, s, L\right) \land \left(\left(\forall a \in \mathbb{N},\; \forall N \in \mathbb{N},\; MAP\left(d, a, N\right) \Rightarrow N \le L\right) \land \left(\forall a \in \mathbb{N},\; a < s \Rightarrow \left(\neg MAP\left(d, a, L\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/ThueMorseMapFirstStart.FirstLongest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

FirstLongest(d,s) requires an actual positive length L at s, bounds every progression length at every natural start by L, and excludes length L at every start smaller than s. Both letters are included because the letter is determined separately at each start. Thus L is the attained global maximum A(d), and s is its first attaining position i(d), in the sense of Joshi and Rust's Definitions 2.2, 2.3 and 2.5.

**Definition 1.3 (The three families of Conjecture 3.8).**

$$claim = \left(\forall e \in \mathbb{N},\; 2 \le e \Rightarrow \left(FirstLongest\left(2^{e} + 1, 3 \cdot \left(2^{e}\right)^{2} - 2^{e} - 1\right) \land \left(\left(Even\left(e\right) \Rightarrow FirstLongest\left(2^{e} - 1, 3 \cdot \left(2^{e}\right)^{2} - 2^{e} + 1\right)\right) \land \left(Odd\left(e\right) \Rightarrow FirstLongest\left(2^{e} - 1, 2^{e} - 1\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/ThueMorseMapFirstStart.claim` (`✓ std3`).

*Citation.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

For every exponent e at least two, put q=2^e. At difference q+1 the first longest progression starts at 3q^2-q-1. At difference q-1 it starts at 3q^2-q+1 when e is even, and at q-1 when e is odd. The printed display in Section 3.2.2 omits parameter ranges; e>=2 is the contextual reading from the immediately preceding maximum-length formulas. In the paper's three separate parameters this means n>=2 for the first equation and n>=1 for the other two. The known value i(3)=45 excludes extending the plus family to e=1; it is a previously known boundary exception.

**Theorem 1.4 (The first starts for every exponent).**

$$\forall e \in \mathbb{N},\; 2 \le e \Rightarrow \left(FirstLongest\left(2^{e} + 1, 3 \cdot \left(2^{e}\right)^{2} - 2^{e} - 1\right) \land \left(\left(Even\left(e\right) \Rightarrow FirstLongest\left(2^{e} - 1, 3 \cdot \left(2^{e}\right)^{2} - 2^{e} + 1\right)\right) \land \left(Odd\left(e\right) \Rightarrow FirstLongest\left(2^{e} - 1, 2^{e} - 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ThueMorseMapFirstStart.result` (`✓ std3`). ∎

*Resolves.* `Problems/joshi-rust-2025-thue-morse-first-longest-start` (proved) by `D5/S1/Words/ThueMorseMapFirstStart.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"joshi-rust-2025-thue-morse-first-longest-start","declaration_gid":"D5/S1/Words/ThueMorseMapFirstStart.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

The positive maximum lengths are q+2 for q+1, q+4 for q-1 with even e, and q for q-1 with odd e. These maxima and the block-recognition principle are due to Aedo, Grimm, Nagai and Staynova, as cited by Joshi and Rust. The dyadic block and top parity identities are supplied by ThueMorseDyadic; the remaining required binary statements are proved inside this argument using the existing Thue-Morse word.

Write a start as aq+b with 0<=b<q. Binary block parity gives t(aq+r)=t(a) xor t(r), and complementary residues control the carries and borrows. A length q+2 progression at difference q+1 forces s+q+1=kq^2 with k>=3; its next letter is opposite. For even e, a length q+4 progression at difference q-1 forces s+q=kq^2+1 with k>=3 and also has an opposite next letter. Block recognition excludes the half-block alternatives, including the boundary e=2. Explicit progressions at k=3 attain the claimed lengths. These facts prove the global bounds and exclude all earlier starts, for either letter.

For odd e, let b=s mod q. The letters at progression indices b and b+1 are opposite, so no run has more than q letters. The start q-1 attains q letters. If s<q-1, then b=s and both opposite letters already occur among the first q positions. This excludes every earlier start. The proof applies to all exponents e>=2.

## References

- Truth anchor: `D5/S1/Words/ThueMorseMapFirstStart.FirstLongest`
- Truth anchor: `D5/S1/Words/ThueMorseMapFirstStart.MAP`
- Truth anchor: `D5/S1/Words/ThueMorseMapFirstStart.claim`
- Truth anchor: `D5/S1/Words/ThueMorseMapFirstStart.result`
- Dependency: [D5/S1/Words/ThueMorseDyadic](ThueMorseDyadic.md)

# Dyadic Thue-Morse Identities

## Abstract

Shared binary block identities for the actual Thue-Morse word.

**Theorem 1.1 (Parity splits at a dyadic boundary).**

$$\forall e \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall r \in \mathbb{N},\; r < 2^{e} \Rightarrow t\left(a \cdot 2^{e} + r\right) = xor\left(t\left(a\right), t\left(r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ThueMorseDyadic.dyadic_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

This is the general binary block proof extracted from the existing ThueMorseMapFirstStart result. The binary recursion proves it by induction on e, splitting the residue into even and odd cases. Both ThueMorseMapFirstStart.result and ThueMorseMapInfiniteFibers.result consume this shared supplier on their live proof paths.

**Theorem 1.2 (The all-one block has its length's parity).**

$$\forall e \in \mathbb{N},\; t\left(2^{e} - 1\right) = oddBit\left(e\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ThueMorseDyadic.top_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

The existing top parity proof is extracted without changing its statement. Adding one leading binary digit negates the color, so t(2^e-1)=oddBit(e), where oddBit is the Boolean test e mod 2=1. The old first-start proof and the new triple construction both use this theorem.

## References

- Truth anchor: `D5/S1/Words/ThueMorseDyadic.dyadic_block`
- Truth anchor: `D5/S1/Words/ThueMorseDyadic.top_parity`
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](Complexity/ThueMorseReducedAbelianOdd.md)

# Golden Beatty Count

## Abstract

The golden shift s(v)=⌊(v+1)/φ⌋ satisfies s(v)≤N exactly when v<⌊(N+1)φ⌋, so the count of such v is ⌊(N+1)φ⌋.

**Theorem 1.1 (The golden shift threshold is a Beatty floor).**

$$\left\lfloor \frac{v+1}{\varphi} \right\rfloor \le N \iff v < \lfloor (N+1)\varphi \rfloor$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/GoldenBeattyCount.golden_beatty_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the golden shift s(v) = ⌊(v+1)/φ⌋, the theorem proves the membership equivalence s(v) ≤ N ⟺ v < ⌊(N+1)φ⌋. Since the natural numbers v with s(v) ≤ N are then exactly {0, 1, …, ⌊(N+1)φ⌋ − 1}, their count is exactly ⌊(N+1)φ⌋.

The proof is elementary: the floor threshold unfolds to (v+1)/φ < N+1, hence v+1 < (N+1)φ, and the irrationality of (N+1)φ (as a nonzero natural multiple of the golden ratio) upgrades the strict real inequality to v+1 ≤ ⌊(N+1)φ⌋, i.e. v < ⌊(N+1)φ⌋. No Beatty complementarity beyond this count is asserted.

## References

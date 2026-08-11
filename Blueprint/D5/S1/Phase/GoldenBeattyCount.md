# Golden Beatty Count

## Abstract

The golden shift s(v)=floor((v+1)/phi) satisfies s(v)<=N exactly when v<floor((N+1)phi), so the count of such v is floor((N+1)phi).

**Theorem 1.1 (The golden shift threshold is a Beatty floor).**

$$\lfloor\frac{v+1}{\phi}\rfloor \le N \iff v < \lfloor(N+1)\phi\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/GoldenBeattyCount.golden_beatty_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the golden shift s(v) = floor((v+1)/phi), the theorem proves the membership equivalence s(v) <= N iff v < floor((N+1)*phi). Since the natural numbers v with s(v) <= N are then exactly {0, 1, ..., floor((N+1)*phi) - 1}, their count is exactly floor((N+1)*phi).

The proof is elementary: the floor threshold unfolds to (v+1)/phi < N+1, hence v+1 < (N+1)*phi, and the irrationality of (N+1)*phi (as a nonzero natural multiple of the golden ratio) upgrades the strict real inequality to v+1 <= floor((N+1)*phi), i.e. v < floor((N+1)*phi). No Beatty complementarity beyond this count is asserted.

## References

- Truth anchor: `D5/S1/Phase/GoldenBeattyCount.golden_beatty_count`

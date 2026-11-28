# Binary Singleton attainment is impossible

## Abstract

No binary linear entanglement-assisted stabilizer code attains the Singleton equality in the k = σ = 2 case.

**Theorem 1.1 (Exclusion of exact binary Singleton attainment).**

$$\neg \operatorname{Attainment}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/baek-won-kim-2026-binary-singleton-attainment` (refuted) by `D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baek-won-kim-2026-binary-singleton-attainment","declaration_gid":"D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jae-Hyun Baek; Byung-Sun Won; Jon-Lark Kim (2026). *Validity and maximum violation of the entanglement-assisted quantum Singleton bound for linear stabilizer codes*. DOI: [10.48550/arXiv.2611.32126](https://doi.org/10.48550/arXiv.2611.32126). URL: <https://arxiv.org/abs/2611.32126v1>.

*Commentary.*

Baek, Won and Kim write in Section 5 of arXiv:2611.32126v1, “The code ⟦8,2,5;2⟧₃ attains this bound, and binary attainment is open.” In their Section 2 notation the binary question asks whether an ⟦n,2,n−3;n−6⟧₂ code exists for any natural n ≥ 6, with degenerate codes included.

Take U to be the symplectic dual of the sender's stabilizer. The claim Attainment requires dim U = 8 and dim (U ∩ U⊥) = 4. Every word of U outside U ∩ U⊥ must have weight at least n − 3, and some such word must have weight exactly n − 3. The weight counts nonzero coordinate pairs.

The lower weight bound gives at most three zeros in every nonradical word. The radical needs at least seven occupied sites, which excludes length six. The attainment bridge excludes every length from eight onward and excludes length seven when every radical site map has rank at most one. At length seven a surjective radical site falls under the shortening obstruction with H = U ∩ U⊥ and the original symplectic form.

## References

- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result`
- Dependency: [D5/S3/Quantum/Codes/BinaryEAAttainmentBridge](BinaryEAAttainmentBridge.md)
- Dependency: [D5/S3/Quantum/Codes/BinaryEAShorteningLengthSeven](BinaryEAShorteningLengthSeven.md)

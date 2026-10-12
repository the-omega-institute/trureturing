# LownerHeinzCore

## Abstract

Attributed general C-star power convexity with its consumed integral proof.

This module is a consumed supporting source transplant for the Lieb-Ando trace curvature endpoints and their general power supplier. Its definitions and proof steps come from Kei Tsukamoto, Kento Mori and Hayata Yamasaki's Apache-2.0 Physlib source at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142. The Lean file records the exact original module and retained supplier license. No mathematical originality is claimed.

**Theorem 1.1 (General C-star power convexity on the positive cone).**

$$\forall u: \operatorname{Level}(), A: \operatorname{Type}(u),\ [\operatorname{CStarAlgebra}(A)], [\operatorname{PartialOrder}(A)], [\operatorname{StarOrderedRing}(A)], [\operatorname{Nontrivial}(A)], [\operatorname{NonnegSpectrumClass}(\mathbb{R}, A)],\ p: \mathbb{R}, 1 \le p \le 2 \implies\ \operatorname{OperatorConvexOn}(\operatorname{Ici}(0), \Lambda x\mapsto\operatorname{rpow}(x, p))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The source-owning power_Icc_one_two_operatorConvexOn_Ici is the exact Physlib endpoint at original line 1785. Its convexOn_nnrpow_Ioo_one_add supplier is at line 1427. The consumed slice preserves arbitrary ordered C-star algebras, Nontrivial and NonnegSpectrumClass, the entire positive cone including singular inputs, both exponent endpoints and noncommuting products. The shifted-inverse input calls pinned Mathlib convexOn_ringInverse_algebraMap_add; its CFC rewrite is the only compatibility adapter. The positivity helper calls the existing IsSelfAdjoint.conjugate_nonneg API.

PowerConvexity consumes this theorem to preserve the general ConvexOn interface, including the trivial algebra, and the uniform Jensen condition. No new general power proof or originality is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici`

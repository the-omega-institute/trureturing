# PowerConvexity

## Abstract

Consumed general C-star power convexity and its all-Hilbert Jensen adapter.

**Theorem 1.1 (Full operator power interval).**

$$\forall u: \operatorname{Level}(), A: \operatorname{Type}(u),\ [\operatorname{CStarAlgebra}(A)], [\operatorname{PartialOrder}(A)], [\operatorname{StarOrderedRing}(A)],\ p: \mathbb{R}, 1\le p\le 2\implies\ \operatorname{ConvexOn}(\mathbb{R}, \operatorname{Ici}(0: A), \Lambda X\mapsto\operatorname{rpow}(X, p))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/PowerConvexity.convexOn_rpow` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

For every 1 <= p <= 2, spectral CFC power is convex on the full nonnegative cone of every complete ordered complex C-star algebra, including the trivial algebra. The nontrivial case directly consumes the attributed Physlib LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici; the trivial case is automatic. NonnegSpectrumClass follows from the existing ordered C-star structure. The original upstream integral proof and its consumed helpers live in LownerHeinzCore. They use one common measure for exponent q=p-1 and integrate the entire kernel x times rpowIntegrand01(q,t,x), with norm integrability obtained by constant left multiplication. The polynomial, inverse and constant summands are never integrated separately.

At p=1 the map is affine. At p=2 the convexity gap is s t times (X-Y)* (X-Y), where s+t=1. Cross products retain their order, so the square identity includes noncommuting inputs. The cone includes zero and singular operators.

**Theorem 1.2 (Uniform all-Hilbert Jensen input).**

$$\forall u: \operatorname{Level}(), p: \mathbb{R},\ 1\le p\le 2\implies\ \operatorname{CondIciAll}(\Lambda x\mapsto\operatorname{rpow}(x, p))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/PowerConvexity.condIciAll_rpow` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

For every universe and every complete nontrivial complex Hilbert space K, x to exponent p is operator convex on the nonnegative real spectrum, continuous on that interval, and zero at zero. Thus it supplies the actual CondIciAll required by the public Jensen perspective theorem. Finite Hilbert-Schmidt convexity is not substituted for this uniform condition.

The supplier is Physlib revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and Hayata Yamasaki, Apache-2.0. Pinned Mathlib by Frederic Dupuis supplies shifted-inverse convexity directly. OperatorGeometricMean consumes the uniform condition and LiebAndoTrace consumes its joint-convexity endpoint via the existing public unrestricted-real-exponent phiK bridge. Its matrix transport and reverse Young endpoint optimizer interpolation supply CarlenLiebConvexity. The original Hiai theorem and support boundary remain separate obligations. Native four-slot audit is unfinished under #5214: a faithful enrolled template and realization covering the full C-star and all-Hilbert telescopes, rigid universe reconstruction and variation/sensitivity evidence have not been supplied. No declared_validated status is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/PowerConvexity.condIciAll_rpow`
- Truth anchor: `D5/S3/Quantum/Lieb/PowerConvexity.convexOn_rpow`
- Dependency: [D5/S3/Quantum/Lieb/JensenOperatorInequality](JensenOperatorInequality.md)

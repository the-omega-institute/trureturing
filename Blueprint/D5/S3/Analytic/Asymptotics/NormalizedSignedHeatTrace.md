# Monotonicity of the normalized signed heat trace

## Abstract

Signed mass prefixes control the normalization of a finite heat trace.

**Theorem 1.1 (Strict increase under the signed prefix and denominator conditions).**

$$\forall n:\mathbb{N}, g,z:\mathbb{N}\to\mathbb{R}, B,B_{d}:\mathbb{R}\to\mathbb{R}, b:\mathbb{R}, (\forall k\leq n, \sum_{i<k}g(i)\leq 0)\land \sum_{i<n}g(i)<0\land (\forall i,0\leq z(i))\land Monotone(z)\land (\forall x\in (0,b], B(x)<0\land HasDerivAt(B,B_{d}(x),x)\land B(x)<xB_{d}(x))\to StrictMonoOn(x\mapsto\frac{x^{2}\sum_{i<n}g(i)exp(-\frac{z(i)}{x})}{B(x)},(0,b])$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/NormalizedSignedHeatTrace.normalized_cutoff_heat_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The active spectrum consists of the first n masses of a nonnegative nondecreasing sequence. The signed weight sum over every prefix is nonpositive, and the total is negative. On (0,b] the denominator B is negative, has derivative dB, and satisfies B(x) < x*dB(x).

Finite Abel summation applies to the positive decreasing exponential weights and to the positive decreasing weights (1+u)*exp(-u) that result from differentiating the heat trace multiplied by x. This makes that factor negative and strictly decreasing. The denominator inequality makes x/B(x) a second negative strictly decreasing factor. Their product increases strictly.

For the proper-time cutoff model, the denominator is K-1 and the strict derivative condition follows from the bound on the mass-weighted logarithmic term. This analytic implication requires the model-specific mass and denominator bounds as inputs.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/NormalizedSignedHeatTrace.normalized_cutoff_heat_strictMono`

# Power families in mixed norm spaces

## Abstract

Exact power-family means and point-evaluation violations.

**Definition 1.1 (Principal-branch power family).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.powerFamily`

*Formalization.* `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.powerFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real p and a, the entire affine expression 1+aw is raised to the principal complex power 2/p using exp and log. The later estimates assume p>0 and 0<=a<1.

**Theorem 1.2 (Holomorphy on the unit disc).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.powerFamily_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.powerFamily_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive p and 0<=a<1, the power family is complex differentiable on the open unit disc. The affine factor lies in the slit plane because its displacement from one has norm less than one.

**Theorem 1.3 (The exact modulus).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.norm_powerFamily`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.norm_powerFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive p and 0<=a<1 and any w of norm less than one, the norm is the real power |1+aw| raised to 2/p. The logarithm of the affine modulus is the real part of the complex logarithm.

**Theorem 1.4 (The exact circle mean).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.circleMean_powerFamily`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.circleMean_powerFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive p, 0<=a<1 and 0<=rho<1, the p-circle mean is (1+a squared rho squared) raised to 1/p. Raising the modulus to p gives the squared affine modulus; its cross term integrates to zero over a full angular period.

**Theorem 1.5 (The finite radial norm identity).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive p, q and alpha and 0<=a<1, the mixed norm is radialIntegral(p,q,alpha,a squared) raised to 1/q. The change of variable u=1-rho squared proves integrability of the radial weight also when alpha q<1.

**Theorem 1.6 (Finite mixed norm).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_lt_top`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_lt_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every power family with positive finite p, q and alpha and 0<=a<1 has finite mixed norm. This supplies the membership condition in the conjecture.

**Theorem 1.7 (The normalized evaluation identity).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.evaluation_powerFamily`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.evaluation_powerFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With c=1/(1+alpha p), evaluating the family at ca and taking the q-th power of the normalized evaluation gives evaluationExcess(p,q,alpha,a squared). This holds for positive p and alpha, 0<=a<1 and every real q.

**Theorem 1.8 (From a strict radial gap to a violation).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.refutes_of_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.refutes_of_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive finite p, q and alpha and 0<a<1, a strict inequality radialIntegral<evaluationExcess gives a holomorphic family with finite mixed norm and a point ca inside the disc at which the multiplied evaluation bound is strictly violated. Positivity of the radial integral justifies taking q-th roots. The witness also has the uniform disc bound (1+a) raised to 2/p.

**Theorem 1.9 (The infinity norm is one).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_infinity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_infinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive finite p and alpha, 0<=a<1 and a squared<=alpha p, every weighted circle mean is at most one. The logarithmic inequality log(x)<=x-1 supplies the upper bound, and the limit as the positive radius tends to zero supplies equality.

**Theorem 1.10 (Every finite p fails at infinite q).**

Lean statement: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.refutes_at_infinity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.refutes_at_infinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive finite p and positive alpha there is a parameter 0<a<1 and an interior point at which the normalized evaluation exceeds the infinity mixed norm, which equals one. The normalized evaluation as a function of a squared has positive derivative 1/(p(1+alpha p)) at zero. The witness also has the uniform disc bound (1+a) raised to 2/p.

## References

- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.circleMean_powerFamily`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.evaluation_powerFamily`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_finite`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_infinity`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.mixedNorm_powerFamily_lt_top`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.norm_powerFamily`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.powerFamily`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.powerFamily_differentiableOn`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.refutes_at_infinity`
- Truth anchor: `D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.refutes_of_gap`
- Dependency: [D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs](Defs.md)
- Dependency: [D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Radial](Radial.md)

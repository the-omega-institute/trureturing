# Bayesian Reverse Recovery at Zero DPI Defect

## Abstract

Zero general-support DPI defect is equivalent to Bayesian reverse recovery.

This result closes only the Bayesian reverse-recovery clause of residual atom sha256:11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574.

The permutation-channel zero-defect specialization REMAINS OPEN. The residual atom as a whole is not discharged.

**Theorem 1.1 (Zero DPI defect is Bayesian reverse recoverability).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\((\forall x: X, 0\le p(x)) \land \sum_{x}p(x) = 1) \Rightarrow\\((\forall x: X, 0\le q(x)) \land \sum_{x}q(x) = 1) \Rightarrow\\(\forall x: X, q(x) = 0 \Rightarrow p(x) = 0) \Rightarrow\\((\forall x: X, y: Y, 0\le W(x, y)) \land (\forall x: X, \sum_{y}W(x, y) = 1)) \Rightarrow\\D(p\Vert\Vert q) - D((Wp)\Vert\Vert (Wq)) = 0 \Leftrightarrow\\\exists R: Y\to X\to \mathbb{R},\\(\forall y, x, R(y, x) = \begin{cases}q(x), &(Wq)(y) = 0\\\widehat{q}_{y}(x), &\text{otherwise}\end{cases}) \land\\(\forall y, x, 0\le R(y, x)) \land\\(\forall y, \sum_{x}R(y, x) = 1) \land\\\operatorname{channelOutput}(R, (Wp)) = p \land\\\operatorname{channelOutput}(R, (Wq)) = q.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/Equality/PetzRecovery.dpi_defect_eq_zero_iff_exists_bayes_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This finite result is the classical form of the equality condition named for Denes Petz.

Petz's 1988 paper "Sufficiency of Channels over von Neumann Algebras" is credited here.

The bibliographic record is verified at DOI 10.1093/qmath/39.1.97.

Its full text was not accessible for this provenance assessment.

No claim is made that the paper states this theorem or an equivalent result.

The recovery channel is the posterior of q at outputs with positive q-mass and the prior q at zero-mass outputs. It is nonnegative and row-stochastic under the stated hypotheses.

Zero defect makes the p and q posteriors coincide wherever p has positive output mass, which gives exact recovery of both inputs. Conversely, data processing for the recovery channel bounds the defect in the reverse direction, while forward data processing bounds it below.

The theorem constructs this finite classical recovery channel only. It does not prove the outstanding permutation-channel specialization or discharge the residual atom as a whole.

## References

- Truth anchor: `D5/S3/DivergenceSupport/Equality/PetzRecovery.dpi_defect_eq_zero_iff_exists_bayes_recovery`
- Dependency: [D5/S3/DivergenceSupport/ZeroSupportDefectEquality](../ZeroSupportDefectEquality.md)

# Quadratic loss of the complete hockey-stick curve

## Abstract

At fixed gamma greater than one, the complete curve loses a quadratic amount near zero under the full Kraus-product span and Choi support hypotheses.

**Definition 1.1 (Complete curve at an input budget).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve.completeCurve`

*Formalization.* `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve.completeCurve` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Take the supremum of the output hockey-stick divergence over every finite reference and every pair of density matrices with equal reference marginals and input divergence at most the budget. Include zero in the supremum.

**Theorem 1.2 (Two-sided quadratic loss).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve.quadratic_loss_near_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve.quadratic_loss_near_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Fix gamma greater than one. Suppose the input matrix algebra is spanned by the Kraus products and the normalized Choi support contains no full reference fiber over a nonzero output vector. For all sufficiently small positive budgets a, the loss a minus the complete curve lies between positive channel- and parameter-dependent multiples of a squared.

The uniform upper bound for a single pair is increasing in its input divergence, so it also bounds the supremum at the budget. For the other direction, a finite Choi orbit with zero common support gives a classical-input preparation. Calibrating the simplex makes its divergence equal to the budget, and its graph effect gives payoff at least a divided by (1 + D a). Bell preparation preserves equal marginals and the output payoff while respecting the input budget. One finite reference dimension suffices for every small budget in this construction.

Hirche, George, Nuradha and Wilde propose nonlinear inequalities with references in arXiv:2608.27171v1, Section 9, fourth bullet. Nuradha, George and Hirche give the ordinary curve in arXiv:2512.16778, Equation (4.1). The simplex and graph effect use Eriksson’s classical-input achievability mechanism. The quadratic estimate concerns the equal-reference-marginal curve near zero under the two stated channel hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve.completeCurve`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve.quadratic_loss_near_zero`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearUpper](NonlinearUpper.md)
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport](../CompleteHockeyStickChoiSupport.md)

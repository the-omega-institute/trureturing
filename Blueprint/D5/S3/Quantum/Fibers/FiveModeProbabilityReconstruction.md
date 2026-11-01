# Classical five-mode probability reconstruction

## Abstract

Three marginal coordinates and one overlap parameter determine a normalized five-event classical mass vector. Endpoint inequalities give nonnegative masses, strict endpoint inequalities give positive masses, and the coordinates are recovered from the vector.

**Theorem 1.1 (Classical reconstruction).** For real $X,Y,Z,\kappa$, define
\[
 p=(1-X-Y-Z+\kappa,\;X-\kappa,\;Z,\;Y-\kappa,\;\kappa).
\]
Then $\sum_i p_i=1$. If $0\le Z$ and
\[
 \max(0,X+Y+Z-1)\le\kappa\le\min(X,Y),
\]
then every $p_i\ge0$. Replacing both endpoint inequalities and $0\le Z$ by strict inequalities makes every $p_i>0$. Finally,
\[
 p_1+p_4=X,\qquad p_3+p_4=Y,\qquad p_2=Z,\qquad p_4=\kappa.
\]

Here $p_i$ uses the zero-based `Fin 5` index, so the displayed vector is
$(p_0,p_1,p_2,p_3,p_4)$.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModeProbabilityReconstruction.probabilities_sum`, `probabilities_nonneg`, `probabilities_pos`, and `probabilities_recover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a classical probability-coordinate bridge. The endpoint conditions are exactly the inequalities needed by the five displayed masses. The declaration does not assert that the masses are native quantum amplitudes, that they arise from a Born rule, or that $\kappa$ is a phase. Any source-to-quantum interpretation must supply those additional physical hypotheses separately.

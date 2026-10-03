# FiniteLocalFrontierMoment

## Abstract

The same-law finite frontier bound for the original Bellman value.

**Theorem 1.1 (Same-tree frontier certificate and uniform Bellman gap).**

Lean statement: `D5/S3/Quantum/Recovery/FiniteLocalFrontierMoment.same_tree_stopped_moment_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FiniteLocalFrontierMoment.same_tree_stopped_moment_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a strict-interior source latitude, one finite barycentric tree and one success marking whose successful endpoints lie in the actual K_s. Define S as its success mass, Delta as its failure defect, Z = 1 - 4 h, H = Z times (1 - kappa) divided by 2 kappa, and C as the mean of the two squared polar coordinates. The same labelled law satisfies Delta nonnegative and g S + Delta = the root defect. At the zero root, its expected C minus Z is at least H - (2 Z / g) Delta.

For every inductively complete cut of this same tree, Delta is the sum of cut mass times each conditional failure defect. The terminal C expectation is bounded by the sum of cut mass times C at the cut state plus half its total squared-norm deficit. These are finite weighted identities and estimates; no measure-theoretic stopping-time assumption is required.

For any positive epsilon, nonnegative tau and complete cut whose positive-mass members are exact-threshold states or terminal leaves above threshold, let W count the mass of threshold states with C at least Z + tau. At the zero root, H - (2 Z / g) Delta is at most tau + W + 8 epsilon + Delta / epsilon. The theorem retains the fixed marking throughout. For the original tau = H / 4 and epsilon = H squared / 8192, the same cut satisfies W at least H / 2 - (2 Z / g + 1 / epsilon) Delta and Delta at least epsilon W / 2. Consequently Delta is at least H cubed / 65536. The conditional success bound uses the separately affine separating function (1 - n dot x)(1 - n dot y) / 4 with n the normalized active Bloch direction.

The refinement within this proof is the pseudo-weak interpolation and protocol splitting of Matthias Kleinmann, Hermann Kampermann and Dagmar Bruss, Asymptotically perfect discrimination in the LOCC paradigm, arXiv:1105.5132v2, Section III.1 equations (5a), (5b), (6) and Section III.2; see the Finite local threshold splitting section of Library/Dynamics/beiglbocknutz2014martingale.md. At a node with d greater than epsilon, alpha_i = w_i max(epsilon - d_i, 0) / (d - epsilon) and beta = 1 / (1 + sum alpha_i). Row mass is beta (w_i + alpha_i), and joint recovery mass is beta (delta_ij + alpha_i) w_j. Each column sums to its original mass. Zero-mass rows use an identity continuation. The complete original subtrees are copied with every endpoint and terminal label unchanged; one leaf map preserves the expectation of every real original-leaf function. Recursion enters only shorter original children and yields one complete prefix-free first-threshold cut, with depth at most twice the original depth.

For the source defect, the regular deviation is the minus marginal of the two-state ensemble gamma_minus = P_minus / 4 and gamma_plus = P_W / 4, whose average state is I / 4. On a normalized product effect Q its conditional value is Tr(P_minus Q) = d. The marginal is continuous in the joint probabilities and unchanged by postprocessing; staged postselection expresses it as a weighted average of conditional marginals. This identifies the known refinement construction without importing a state-discrimination conclusion or a reverse physical realization premise.

The law-preserving finite refinement is applied to each tree marked by its original terminal payoff. Taking the supremum over all finite trees gives 4 VInfinity at the zero root at most U - H cubed / (49152 kappa), strictly below U. The root value of psi is at least H cubed / (196608 kappa). VInfinity is the original Bellman supremum. There is no uniform resource bound, limiting attainment or reverse physical realization premise. FiniteLocalPhysicalGap proves the physical p and eta_fin bounds separately by translating every actual normalized CP protocol to the abstract tree value.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FiniteLocalFrontierMoment.same_tree_stopped_moment_certificate`
- Dependency: [D5/S3/Quantum/Recovery/FiniteLocalBellmanEnvelope](FiniteLocalBellmanEnvelope.md)

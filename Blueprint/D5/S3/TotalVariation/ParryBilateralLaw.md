# The bilateral Parry source and its signed path law

## Abstract

The bilateral Parry source and its signed path law.

The classical maximal-entropy application concerns the unsigned relation law mu supplied here. Fix k >= 2, put p = parryParameter k, and let T be the actual relationShift on RelationPath k. For every Borel probability measure rho preserved by T, its Kolmogorov-Sinai entropy in nats is at most -log p. The same mu attains this value; equality holds exactly when rho = mu, and every distinct invariant probability has strictly smaller entropy. The competitors range over all invariant probabilities. Neither ergodicity nor a Markov property is an assumption. The signed extension nu is used to construct mu, and does not replace the unsigned competitor space in this application.

Use the coding's full suffix contract to define J(r,t) as the suffix component of e(false,r) at the integer t. Thus J(r,t) is the length of the true run immediately preceding t, independently of the sign anchor. The contract gives J(r,t+1) = 0 when r_t is false and J(r,t+1) = J(r,t)+1 when r_t is true. In particular r_t is false exactly when J(r,t+1) = 0. Translating a relation path by any integer c translates this suffix coordinate by c. These identities apply to every admissible path and every integer origin, including paths and cylinders of zero probability.

For a competitor rho, take the finite measurable partition P_j = {r : J(r,0) = j}, j in Fin k. The shift T is a measurable automorphism, with inverse translation by -1. All integer translates of P generate the ambient Borel sigma-algebra: each suffix cell is measurable, and the preceding bit identity reconstructs each relation-coordinate event from a translated zero-suffix cell. The two-sided finite-generator theorem therefore identifies the actual EReal KS supremum with the entropy rate of P. The required supplier is ErgodicTheory/Entropy/GeneratorTheoremTwoSided.lean, together with ErgodicTheory/Krieger/ZIterate.lean, at marcmorningstar/lean4-ergodic-theory revision 040fec2e0ddf4fcba49af9f76c866d295308dd7f; its attribution and Apache-2.0 license are recorded in Library/Entropy/morgenstern2026ks.md. The repository's one-sided IsGenerating condition alone does not give this bilateral step.

Write A_n(w) = {r : J(r,i) = w_i for every i in Fin n}, H_n = H_rho(A_n), and c_n = H_rho(J_n | A_n). In particular A_0 is the one-cell partition and H_0 = 0. The finite chain rule entropy_join_eq_add_condEntropyGivenPartition gives H_(n+1) = H_n + c_n. The conditioning and pullback suppliers documented in GeneratorConditioning show that c_n decreases with n and that h_rho(T,P) <= c_n for every n. This is the existing stationary finite-history envelope applied to these actual joint events. Shift invariance is used for the same joint law throughout; no separate-marginal or presumed Markov substitution is involved.

Let Q be suffixKernel k and R_j = suffixWeight k p j. On an allowed transition j to h, log Q(j,h) = log p + log R_h - log R_j. The allowed destinations are zero and, when it exists, j+1. The bounds and normalization in parry_stationary_law give positive R_j and stochastic rows of Q. The native recurrence for J makes a forbidden transition event empty under every competitor, rather than merely declaring it null under mu.

For any history length n >= 1, consider the actual joint masses a(w,j) = rho(A_n(w) intersect {J_n = j}) and the reference masses b(w,j) = rho(A_n(w)) Q(w_(n-1),j). Both finite arrays are probability distributions. If a history has zero mass then every extension has zero mass. If Q(w_(n-1),j) is zero then the extension is forbidden and empty. These two facts supply absolute continuity a << b, including all boundary cases. The row and column sums are those of this same joint distribution. Stationarity makes the expected log R of the next suffix equal to that of the last suffix in the history.

Expanding the finite KL divergence with these row sums and the logarithmic kernel identity gives D(a || b) = -log p - c_n. GrandmotherTheorem.kl_divergence_nonneg therefore gives c_n <= -log p, and the generator identification and history envelope give h_KS(rho,T) <= -log p. If the actual KS entropy equals -log p, both inequalities force D(a || b) = 0 at every history length. GibbsEquality.kl_divergence_eq_zero_iff then gives a(w,j) = b(w,j) for every word and destination. Dividing by a positive history mass gives precisely the canonical next-suffix conditional distribution. The undivided identity also covers zero histories. Translation invariance extends the identities to every integer origin.

For the same canonical mu constructed by bilateral_parry_law, its full cylinder formula already gives these transition identities. Hence D(a || b) = 0 and c_n = -log p for every n >= 1. Monotonicity also gives c_0 >= -log p. The finite chain rule yields H_n >= n(-log p); the Fekete limit tendsto_ksEntropySeq and the preceding universal upper bound then give h_KS(mu,T) = -log p. This uses the original unsigned cylinder-law witness, including its initial suffixLaw mass and every zero transition.

The initial suffix marginal is determined without assuming the competitor is Markov. Indeed every row of Q assigns at least 1/2 to zero, by the p and R bounds. Subtract the common row mass b_j = (1/2) 1_(j=0) and rescale to the stochastic kernel U(i,j) = 2(Q(i,j)-b_j). For two normalized stationary rows u and v, the common part cancels and DataProcessing.total_variation_channel_le gives TV(u,v) <= (1/2) TV(u,v). Metric.total_variation_nonneg and total_variation_eq_zero_iff force u = v. The length-one transition identity proves stationarity of the suffix marginal of every maximizing competitor, so it equals the marginal of mu.

Starting from that common marginal, the transition identity determines every finite suffix-cylinder mass recursively. It therefore gives the canonical full cylinder formula at every integer origin. The relation bits are recovered from whether the following suffix is zero. Applying this measurable postprocessing to the suffix windows gives equality of every actual relation-bit cylinder; TwelveStateGhost.visible_eq_of_cylinders supplies uniqueness of the bilateral bit measure, and the measurable subtype inclusion gives rho = mu on RelationPath k. Conversely rho = mu gives attainment. The strict inequality for rho distinct from mu follows from the universal upper bound and this equality criterion in EReal.

This derivation is an application of the cited generator, finite conditioning, Gibbs, total-variation contraction and cylinder-uniqueness suppliers, with their parameters matched to the native unsigned law. It introduces no separate Lean declaration or new mathematical novelty claim. The theorem statement bilateral_parry_law below supplies the measure, coding and cylinders; its statement itself does not include the entropy conclusion. The application makes no topological-entropy, first-return Abramov, physical-realization or quantitative entropy-gap claim.

**Theorem 1.1 (Measurable bilateral reconstruction).**

Lean statement: `D5/S3/TotalVariation/ParryBilateralLaw.bilateral_reset_coding`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryBilateralLaw.bilateral_reset_coding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix k >= 2. A relation path is a function r from the integers to Bool with a zero in every block of k consecutive bits. Its suffix j_t counts the true bits immediately before t. The nearest preceding zero exists and gives 0 <= j_t < k; specifically r_(t-j_t-1) is false and the j_t bits after it are true. Starting with a sign b at zero, finite XOR of the complemented relation bits reconstructs a_t in each time direction.

The map (b,r) to the path (a_t,j_t) is a measurable equivalence onto the bilateral paths whose every edge has positive mass under TwistedResetPaths.kernel k (parryParameter k). Its inverse reads a_0 and r_t = not (a_t xor a_(t+1)). The coding intertwines the path shift with (b,r) to (b xor not r_0, relationShift r). The suffix characterization and inverse hold for every supported path, including negative times.

**Theorem 1.2 (The actual stationary source and joint law).**

Lean statement: `D5/S3/TotalVariation/ParryBilateralLaw.bilateral_parry_law`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryBilateralLaw.bilateral_parry_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k >= 2 there exist a stationary probability measure mu on the actual relation space, a stationary probability measure nu on integer-indexed signed state paths, and a measurable coding with all the preceding properties. Writing p = parryParameter k, h_j = suffixWeight k p j and S = normalizer k, the suffix stationary mass is p^j h_j / S. Its transition kernel is p/h_j to zero, p h_(j+1)/h_j to j+1 when that state exists, and zero otherwise. At every integer origin, every finite suffix cylinder under mu has exactly the product of this initial mass and these transition probabilities. The suffix is the preceding true run specified by the coding, so this identifies mu with the forbidden-run Parry source.

The image of fairAnchor times mu under the coding is exactly nu as a measure. For every integer ell, natural m and word w of m+1 signed states, its cylinder mass is ofReal(parryLaw k (w_0) times the product, over i < m, of kernel k p (w_i) (w_(i+1))). This includes m=0 and words with zero transition mass. The anchor is fair and independent of the entire relation path, not merely of a suffix coordinate or a finite window.

The construction first extends the compatible signed Markov masses on centered finite blocks using the existing inverse-limit probability theorem, and then identifies coherent blocks with paths on the integers. Sign-complement symmetry and uniqueness of that extension give equal masses to the two anchor slices over every measurable relation event; these slices establish the product disintegration. Summing the signed word masses over signs gives the source suffix cylinders. Shift invariance follows from the same finite-dimensional characterization. This result supplies the law identification; mixing and measurable-section obstructions require further theorems.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryBilateralLaw.bilateral_parry_law`
- Truth anchor: `D5/S3/TotalVariation/ParryBilateralLaw.bilateral_reset_coding`
- Dependency: [D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension](../Estimation/DataProcessing/InverseLimitProbabilityExtension.md)
- Dependency: [D5/S3/TotalVariation/ParryResetLaw](ParryResetLaw.md)

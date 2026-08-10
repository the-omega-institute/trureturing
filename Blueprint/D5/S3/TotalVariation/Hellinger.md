# Squared Hellinger Distance and Total Variation

## Abstract

Intrinsic squared Hellinger distance is pinned on arbitrary finite real functions and compared sharply with total variation.

**Definition 1.1 (Squared Hellinger distance is intrinsic square-root geometry).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\H^{2}(p, q):=\sum _{i} (\sqrt {p(i)}-\sqrt {q(i)})^{2}.\end{gathered}$$

*Formalization.* `D5/S3/TotalVariation/Hellinger.hellingerSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite real functions p and q, the squared Hellinger distance is defined intrinsically as the sum of the squared coordinatewise gaps between their square roots. The definition itself requires neither nonnegativity nor normalization.

Two forms were available: this square-root geometry and the probability-domain formula 2(1-BC(p,q)). The latter was deliberately rejected as a definition. It would make the bridge identity true by reflexivity, and an identity that holds by definition pins nothing. It would also build normalization-dependent coordinates into an object otherwise defined on arbitrary finite real functions.

The choice records a general methodological principle: a definition must not be selected merely to make its own pinning identity trivial. The bridge to Bhattacharyya affinity is therefore proved between independently defined quantities.

**Theorem 1.2 (Squared Hellinger distance vanishes on the diagonal).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p: \iota\to \mathbb{R},\\H^{2}(p, p)=0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Hellinger.hellinger_sq_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The definition is defended by four identities arranged in layers. Each successive layer governs a strictly larger domain of two-input behavior than the preceding pin can inspect. The first layer is the diagonal, and it establishes self-distance zero without hypotheses.

This first identity cannot detect a corruption that ignores q entirely, such as summing (sqrt(p(i))-sqrt(p(i)))^2. The corruption also vanishes on every diagonal input, so it passes the self-distance theorem. The next layer must therefore leave the diagonal.

**Theorem 1.3 (Probability Hellinger square is twice one minus affinity).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land\\((\forall i, 0\le q(i)) \land \sum _{i} q(i)=1) \Rightarrow\\H^{2}(p, q)=2(1-\operatorname{BC}(p, q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_two_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second layer governs pairs of probability vectors and proves the nontrivial bridge H^2(p,q)=2(1-BC(p,q)). It kills the one-sided corruption: on two opposite Bool point masses, the intrinsic value is two, whereas the corruption from the first layer remains zero.

Normalization is essential to this coordinate form. Consequently, the identity still cannot inspect a corruption engineered to vanish whenever both total masses equal one. The third layer removes normalization while retaining the natural nonnegative mass-function domain.

**Theorem 1.4 (Nonnegative Hellinger square expands through affinity).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\(\forall i, 0\le p(i)) \land (\forall i, 0\le q(i)) \Rightarrow\\H^{2}(p, q)=\sum _{i} p(i)+\sum _{i} q(i)-2\operatorname{BC}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_sum_add_sub_two_bhattacharyya` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third layer governs nonnegative finite mass functions without normalization. A compiled corruption can augment the intrinsic expression by a diagonal-vanishing term proportional to (sum_i p(i)-1)^2(sum_i q(i)-1)^2. It passes self-distance because the added term vanishes on the diagonal, and it passes the probability bridge because both normalization defects vanish there.

Off the normalized domain the corruption is exposed. On Unit with p=0 and q=4, it evaluates to 148 while the intrinsic squared Hellinger distance is four. The mass-expansion identity rules it out throughout the nonnegative, nonnormalized domain.

**Theorem 1.5 (Hellinger square has an all-real algebraic expansion).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\H^{2}(p, q)=\sum _{i} (\sqrt {p(i)}^{2}+\sqrt {q(i)}^{2}-2(\sqrt {p(i)}\sqrt {q(i)})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_sum_expanded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fourth and final layer is a pure algebraic expansion valid for every finite real input. A corruption that activates only on negative coordinates can pass all three earlier layers. On Unit with p=-1 and q=0, the compiled corruption gives one, whereas the intrinsic value is zero because Real.sqrt of a negative number is zero. The all-real expansion detects it.

This last identity closes the defense: no further corruption can survive because its right side is extensionally equal to the definition on every finite real input. Its proof is elementary ring algebra. It is cheap defensive infrastructure rather than deep mathematics, and its strength comes precisely from that complete extensional coverage.

Every corruption and witness in the four-layer progression was compiled independently by the caller, including the negative-input fact used in the final case.

**Theorem 1.6 (The squared square-root gap contracts the absolute gap).**

$$\begin{gathered}\forall a, b\in \mathbb{R},\\(\sqrt {a}-\sqrt {b})^{2}\le \Vert a-b \Vert .\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Hellinger.sq_sqrt_sub_sqrt_le_abs_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar contraction is stated for arbitrary real a and b. No sign hypothesis is hidden in its signature. When both inputs are nonnegative, the usual factorization of a-b through their square roots gives the comparison.

The remaining sign cases are not accidental exceptions. Real.sqrt is zero on nonpositive inputs, so the same inequality remains valid when one or both arguments are negative. This all-real scalar statement is exactly what permits the lower bracket to inherit no mass-function hypotheses.

**Theorem 1.7 (Half the Hellinger square is bounded by total variation).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\frac{H^{2}(p, q)}{2}\le \operatorname{TV}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Hellinger.hellinger_sq_div_two_le_total_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower bracket H^2(p,q)/2 <= TV(p,q) holds for arbitrary finite real functions. In particular, p and q need not be nonnegative and need not be normalized. Summing the all-real scalar contraction coordinatewise and applying the factor one half in total variation proves the result.

This strength follows from deriving the hypothesis set for the statement itself rather than copying assumptions from a neighboring theorem. That discipline has now produced strictly stronger results in six consecutive waves in this bucket.

**Theorem 1.8 (The upper bracket is the frozen affinity bound in Hellinger coordinates).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land\\((\forall i, 0\le q(i)) \land \sum _{i} q(i)=1) \Rightarrow\\\operatorname{TV}(p, q)^{2}\le H^{2}(p, q)-\frac{(H^{2}(p, q))^{2}}{4}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Hellinger.total_variation_sq_le_hellinger_sq_sub_quarter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem is not new mathematics. It is the frozen bound TV(p,q)^2 <= 1-BC(p,q)^2 rewritten under the independently proved bridge H^2(p,q)=2(1-BC(p,q)). Thus the displayed term H^2-H^4/4 is only the Bhattacharyya square bound expressed in Hellinger coordinates.

The restatement is included solely because it makes the two-sided comparison readable beside H^2(p,q)/2 <= TV(p,q). It must not be read as an independent inequality or a second analytic contribution. Unlike the lower bracket, this coordinate rewrite assumes that both inputs are nonnegative probability vectors.

**Theorem 1.9 (The lower bracket is strict on a Bool witness).**

$$\begin{gathered}p=\Delta_{\operatorname{true}},\\q(\operatorname{true})=\frac{9}{25}, q(\operatorname{false})=\frac{16}{25},\\\frac{H^{2}(p, q)}{2}<\operatorname{TV}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Hellinger.hellinger_sq_lower_strict_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strictness statement is a theorem, not a comment. On Bool, p is the point mass at true and q assigns masses 9/25 and 16/25 to true and false, respectively. Lean evaluates the lower side as 2/5 and total variation as 16/25, so the strict inequality is kernel-checked and frozen rather than asserted informally.

The TotalVariation bucket now contains Pinsker's bound, the metric structure with the attained variational characterization, data-processing contraction, Bretagnolle--Huber with the Bhattacharyya coefficient, and the present Hellinger comparison. All divergence units mentioned in this narrative are nats.

No Renyi divergence, Hellinger-to-KL bound, equality analysis, or measure-theoretic analogue is claimed.

## References

- Truth anchor: `D5/S3/TotalVariation/Hellinger.hellingerSq`
- Truth anchor: `D5/S3/TotalVariation/Hellinger.hellinger_sq_div_two_le_total_variation`
- Truth anchor: `D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_sum_add_sub_two_bhattacharyya`
- Truth anchor: `D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_sum_expanded`
- Truth anchor: `D5/S3/TotalVariation/Hellinger.hellinger_sq_eq_two_sub`
- Truth anchor: `D5/S3/TotalVariation/Hellinger.hellinger_sq_lower_strict_witness`
- Truth anchor: `D5/S3/TotalVariation/Hellinger.hellinger_sq_self`
- Truth anchor: `D5/S3/TotalVariation/Hellinger.sq_sqrt_sub_sqrt_le_abs_sub`
- Truth anchor: `D5/S3/TotalVariation/Hellinger.total_variation_sq_le_hellinger_sq_sub_quarter`
- Dependency: [D5/S3/TotalVariation/Bhattacharyya](Bhattacharyya.md)

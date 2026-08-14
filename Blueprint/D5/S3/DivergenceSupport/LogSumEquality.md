# Equality in the Finite Log-Sum Inequality

## Abstract

Equality in the finite log-sum inequality is characterized by proportionality on the positive reference support.

The frozen LogSumInequality module proves the log-sum inequality under discrete absolute continuity, exhibits a counterexample showing that the claim is false without that condition, and gives an explicit strict instance. It does not characterize equality. The three declarations below complete that account by proving attainment from proportionality, extracting common ratios from equality, and combining the two directions into a biconditional.

The proportionality hypothesis is deliberately written as a i = c * b i for an explicit constant c. It requires no sign hypotheses and is immediately usable downstream. Under the repository's totalization x / 0 = 0 and log 0 = 0, both sides reduce directly to (c log c) * SUM b, including the all-zero boundary. A pairwise-ratio formulation would require additional support bookkeeping before downstream results could recover this global form.

The converse is stated only on the positive support of b, and this is the honest strength of the result rather than a weakness. Where the reference mass vanishes, totalized division assigns the ratio zero and the ratio carries no information about proportionality. Equality therefore forces agreement of a(i) / b(i) precisely between coordinates at which b is positive.

The converse rests on strict convexity. The frozen inequality uses the non-strict Jensen bound convexOn_klFun.map_sum_le, whereas its equality case uses InformationTheory.strictConvexOn_klFun together with StrictConvexOn.map_sum_eq_iff_of_nonneg. Thus the inequality and its equality case rest on different halves of the same convexity fact.

All three displays are authored legally because the current statement projector has no pinned projectable fixture for these declarations. Document construction therefore records a ProjectionGap for each theorem.

**Theorem 1.1 (Proportional families attain log-sum equality).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall a, b: \iota\to \mathbb{R}, c \in \mathbb{R},\\\forall i, a(i) = c \cdot b(i) \Rightarrow\\(\sum _{i} a(i)) \log (\frac{\sum _{i} a(i)}{\sum _{i} b(i)}) = \sum _{i} a(i) \log (\frac{a(i)}{b(i)}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LogSumEquality.log_sum_eq_of_proportional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No nonnegativity or absolute-continuity hypothesis is needed. At a coordinate where b vanishes, proportionality makes a vanish and totalization makes the summand zero. Elsewhere the quotient is c. The same division into zero and nonzero cases applies to the total reference mass, so both sides equal (c log c) times the total mass of b even when that total is zero.

**Theorem 1.2 (Log-sum equality forces common positive-support ratios).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall a, b: \iota\to \mathbb{R},\\(\forall i, 0 \le a(i)) \land\\(\forall i, 0 \le b(i)) \land\\(\forall i, b(i) = 0 \Rightarrow a(i) = 0) \Rightarrow\\((\sum _{i} a(i)) \log (\frac{\sum _{i} a(i)}{\sum _{i} b(i)}) = \sum _{i} a(i) \log (\frac{a(i)}{b(i)})) \Rightarrow\\\forall j k, 0 < b(j) \Rightarrow 0 < b(k) \Rightarrow \frac{a(j)}{b(j)} = \frac{a(k)}{b(k)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LogSumEquality.ratios_eq_of_log_sum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume nonnegativity and discrete absolute continuity. If the total mass of b vanishes, positive-support coordinates do not exist and the conclusion is vacuous. Otherwise the normalized b-masses are nonnegative weights summing to one. Rewriting log-sum equality as equality in Jensen's inequality for klFun and applying its strict-convexity equality criterion forces all ratios carrying positive weight to coincide.

**Theorem 1.3 (Log-sum equality is equivalent to common positive-support ratios).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall a, b: \iota\to \mathbb{R},\\(\forall i, 0 \le a(i)) \land\\(\forall i, 0 \le b(i)) \land\\(\forall i, b(i) = 0 \Rightarrow a(i) = 0) \Rightarrow\\((\sum _{i} a(i)) \log (\frac{\sum _{i} a(i)}{\sum _{i} b(i)}) = \sum _{i} a(i) \log (\frac{a(i)}{b(i)})) \Leftrightarrow\\\forall j k, 0 < b(j) \Rightarrow 0 < b(k) \Rightarrow \frac{a(j)}{b(j)} = \frac{a(k)}{b(k)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LogSumEquality.log_sum_eq_iff_ratios_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward implication is the strict-convexity result above. For the reverse implication, a positive coordinate of b supplies the explicit common ratio when the total reference mass is positive; discrete absolute continuity extends the resulting proportionality across zero-reference coordinates. When the total reference mass is zero, both families vanish and the proportionality theorem applies with c = 0. The biconditional therefore includes the all-zero boundary without adding a separate exception.

## References

- Truth anchor: `D5/S3/DivergenceSupport/LogSumEquality.log_sum_eq_iff_ratios_eq`
- Truth anchor: `D5/S3/DivergenceSupport/LogSumEquality.log_sum_eq_of_proportional`
- Truth anchor: `D5/S3/DivergenceSupport/LogSumEquality.ratios_eq_of_log_sum_eq`
- Dependency: [D5/S3/DivergenceSupport/LogSumInequality](LogSumInequality.md)

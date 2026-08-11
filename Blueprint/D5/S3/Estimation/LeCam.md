# Le Cam's Two-Point Lemma for Every Finite Test

## Abstract

Le Cam's finite two-point lemma bounds every test's total and maximum error masses by the total variation between its candidate laws.

**Theorem 1.1 (Le Cam forces one error mass of every test to be large).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\forall A: \operatorname{Finset}(\iota),\\(\sum _{i} p(i)=\sum _{i} q(i)) \land (\sum _{i} q(i)=1) \Rightarrow \\\frac{1-\operatorname{TV}(p, q)}{2}\le \max \left\{\sum _{i\in A} p(i), \sum _{i\in A^c} q(i)\right\}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/LeCam.le_cam_two_point_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Le Cam's two-point lemma is the second major family of information-theoretic lower bounds in this bucket, beside Fano's inequality. Fano converts conditional entropy into an estimator-error bound; Le Cam instead converts the statistical distance between two candidate laws into a test-error bound. For unit-mass laws, no test can drive its total error below one minus their total variation. The mechanisms differ, but both prevent uniformly reliable inference.

The acceptance region A is universally quantified, and this is the content of the statement. The test reports q on A, so its two error masses are the p-mass of A and the q-mass of the complement of A. The bound holds for every such A, hence for every test, rather than for a conveniently selected event. A result restricted to one particular acceptance region would provide no lower bound on arbitrary tests.

The three declarations form a deliberate hierarchy. The base theorem le_cam_two_point_sum_mass assumes only that p and q have equal total mass and lower-bounds the sum of the two error masses by that common mass minus total variation. It assumes no coordinatewise nonnegativity: the frozen variational lever already applies to arbitrary real functions of equal mass, and the remaining argument is purely order-theoretic and algebraic. The theorem le_cam_two_point_sum adds unit mass only to rewrite the common total as one. Finally, le_cam_two_point_max passes from the sum to the displayed maximum bound.

The proof is short because the required structural work has already been frozen in total_variation_eq_sup_event_gap. It applies that variational characterization to the supplied event A, takes only the upper-bound half of its IsGreatest conclusion--no event gap exceeds total variation--and adds the complement identity for q. It does not use the attainment half: Le Cam bounds an already supplied test and does not select an optimizing event. The module therefore consumes the characterization rather than re-deriving it, which is precisely why that characterization was worth proving.

The maximum form is the operational conclusion. A maximum is at least the average of its two entries, so every test has at least one error mass no smaller than one half of one minus total variation. Equivalently, no test can make both error masses smaller than that threshold simultaneously.

The lower bound is tight. For two identical unit laws, total variation is zero, while the acceptance region and its complement partition the total mass. The two error masses therefore sum to one for every test, making the sum bound an equality for every acceptance region. A test cannot distinguish identical laws, and the lemma states exactly that obstruction.

The inequality is not an identity. On Bool, take the two opposite unit point masses and the empty acceptance region. Their total variation is one, so the lower bound is zero, whereas the test's total error mass is one; the inequality is strict. The checks that neither rfl nor simp closes any of the three general bounds were compiled as fail_if_success obligations.

No minimax or sample-complexity corollary, multi-point generalization of Assouad or Fano type, converse, or measure-theoretic analogue is claimed. Divergences elsewhere in this program are measured in nats, although the present lemma contains no logarithm and hence introduces no logarithmic unit.

## References

- Truth anchor: `D5/S3/Estimation/LeCam.le_cam_two_point_max`
- Dependency: [D5/S3/TotalVariation/Metric](../TotalVariation/Metric.md)

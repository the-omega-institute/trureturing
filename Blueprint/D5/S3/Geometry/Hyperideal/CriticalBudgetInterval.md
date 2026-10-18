# The four-plus-two budget interval

## Abstract

Exact opposite-edge floor for the prescribed four-plus-two critical angle budget.

Let q=49/sqrt(6534), beta=arccos(q), and aStar=(25-33sqrt((1-q)/2))/8. The target edge has upper cosine-length bound 2; high neighbours have bound 5/4. The parameter a is the floor on a favourable opposite edge, restricted to 1<a<7/5.

**Theorem 1.1 (The endpoint cosine and exact strict interval).**

$$\forall a \in Real,\; \left(1 < a \land a < \frac{7}{5}\right) \Rightarrow \left(cosine\left(2, \frac{5}{4}, \frac{5}{4}, a, \frac{5}{4}, \frac{5}{4}\right) = \frac{25-8\cdot a}{33} \land \left(\left(0 < 2\cdot \pi-6\cdot arccos\left(\frac{2\cdot (2-a)}{a+1}\right) \land 0 < 4\cdot arccos\left(cosine\left(2, \frac{5}{4}, \frac{5}{4}, a, \frac{5}{4}, \frac{5}{4}\right)\right)+2\cdot \beta-2\cdot \pi\right) \Leftrightarrow \left(oppositeThreshold < a \land a < \frac{7}{5}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/CriticalBudgetInterval.exact_budget_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At target value 2, four neighbours at 5/4 and opposite value a, the original six-coordinate cosine equals (25-8a)/33. This is the favourable upper-face endpoint, with no cosine value supplied as a premise.

The prescribed lower budget is 2pi-6arccos(2(2-a)/(a+1)); the upper budget is 4arccos of the original favourable cosine, plus 2beta-2pi. The endpoint equality rewrites it as 4arccos((25-8a)/33)+2beta-2pi. Within 1<a<7/5 both are strictly positive exactly when aStar<a. The displayed upper endpoint is in (0,1), so the double-angle identity and strict decrease of cosine on [0,pi] give the threshold without decimal estimates.

The theorem identifies strictness of this specified analytic budget. It does not assert that a global length vector attains every endpoint or that a geometric realization exists.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CriticalBudgetInterval.exact_budget_interval`
- Dependency: [D5/S3/Geometry/Hyperideal/CriticalTransitionStar](CriticalTransitionStar.md)

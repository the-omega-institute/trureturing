# Permutation-equivariant calibration on a finite grid

## Abstract

Exact seed budgets on finite probability grids under all label permutations.

**Definition 1.1 (Calibrating law with permutation symmetry).**

$$\operatorname{CalibratingLaw}\left(k, m, S, w, f\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/PermutationGridSupport.CalibratingLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The labels are the first k natural numbers and the profiles are natural coordinate vectors with sum m. A finite seed set S carries an action of the full permutation group on the labels. Its real weights w are positive, sum to one and are invariant under this action. The mass of the seeds that f sends to a label equals that profile coordinate divided by m. Relabeling the profile and acting by the same permutation on the seed relabels the output of f.

**Theorem 1.2 (Sharp support budget for the complete probability grid).**

$$\forall k q n, 2 \le k \land 0 < q \land \operatorname{DivisibleThrough}\left(k, k\cdot(k-1)\cdot q\right) \Rightarrow (\operatorname{SeedBudget}\left(k, k\cdot(k-1)\cdot q, \operatorname{factorial}\left(k\right)\cdot n\right) \iff k\cdot q+1 \le (k+1)^n)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/PermutationGridSupport.grid_support_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be at least two, let q be a positive natural number and set m to k times k minus one times q, with parentheses around k minus one. Suppose every positive integer through k divides m. SeedBudget(k,m,B) means there is a calibrating law with at most B seeds. For any natural n the budget k factorial times n is feasible exactly when k times q plus one is at most k plus one to the power n, with parentheses around the base.

For any nonidentity permutation, the profile constant on its moved labels and zero elsewhere has integer coordinates. A fixed seed would return a fixed label at that profile, which has zero mass. Each seed orbit is therefore regular. At a profile tying k minus one labels, the subgroup fixing the distinguished label divides each regular orbit into k blocks. For a tied label the number of seeds selected in each block is either zero or the factorial of k minus two. The possible per-orbit block counts are the k plus one digits from zero through k.

For attainment, group the labels by their coordinate values. Let H be the product of the group-size factorials and let D be the factorial of k minus two. Each regular seed orbit has k factorial divided by H blocks for the profile stabilizer action. The desired block mass for a group of size s and coordinate value v is D times s times v divided by H. The frozen factorial divisibility theorem gives integer demands. If there are t groups, each orbit has at least k times t minus one blocks, with parentheses around t minus one.

Use clipped powers of k plus one, summing to q, as common orbit weights. The rounded capacities of each group suffice to assign all new blocks while the earlier orbits realize the remainder. The bounded-digit weights use Rødseth, Minimal r-Complete Partitions, Journal of Integer Sequences 10 (2007), Article 07.8.3, Lemmas 3.1–3.2. The allocation step follows by comparing the sum of the remainders with the mass needed for one more block.

A block assigned to a group has an equivariant map to that label orbit, giving each of its labels H divided by s seeds. Extend the readout from one profile representative per orbit and normalize the weights on positive support.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/PermutationGridSupport.CalibratingLaw`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/PermutationGridSupport.grid_support_budget_iff`
- Dependency: [D5/S3/Combinatorics/Partitions/StabilizerFactorialDivisibility](../../Combinatorics/Partitions/StabilizerFactorialDivisibility.md)

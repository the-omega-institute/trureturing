# Incompatible Coupled Seven Budgets

## Abstract

The two displayed prime-palette envelopes cannot both reach one when their low allocations share one unit pool and their high allocations share a separate unit pool. All four allocations may be real.

**Definition 1.1 (The first ordinary-prime palette).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.smallPalette`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.smallPalette` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first palette is {5,11,13,17,19,23,29,31,37,41,43}. The shared prime seven is excluded from this ordinary palette.

**Definition 1.2 (The second palette's additional primes).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.tailPalette`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.tailPalette` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additional primes are {47,53,59,61,67,71}.

**Definition 1.3 (One partition determines both palettes).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.otherPalette`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.otherPalette` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a subset A of the first palette, the second palette consists of the first palette minus A, together with all additional primes.

**Definition 1.4 (Prime weights).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.ordinaryWeight`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.ordinaryWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each ordinary prime p has rational weight 1/(p-3).

**Definition 1.5 (Product of the ordinary contributions).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.ordinaryProduct`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.ordinaryProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary product is the product of 1+1/(p-3) over the selected primes.

**Definition 1.6 (The coarse rational budget).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.budget`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.budget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For parameters kappa and b, the budget is (2+kappa) times ((1+b) times the ordinary product minus one), minus twice the sum of b and the ordinary prime weights.

**Definition 1.7 (The shared-axis coefficient).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.gain`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.gain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gain is (2+kappa) times (the ordinary product minus one).

**Definition 1.8 (The rational endpoint demand).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.rawDemand`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.rawDemand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At low allocation t, the raw high-allocation demand is ((1-budget(kappa,0,A)) times (5-t) minus gain(kappa,A)) divided by kappa. It is not truncated at zero.

**Theorem 1.9 (Every partition has an obstruction).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.partition_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.partition_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every subset A of the first palette, either a coarse budget with shared weight 1/4 is strictly below one, or the sum of the two raw demands is strictly above one at both complementary allocation endpoints. The first envelope uses kappa=1/2 and the second uses kappa=1/3.

**Definition 1.10 (The envelope with real allocations).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.envelope`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.envelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real low and high allocations t and v, the envelope is budget(kappa,0,A) plus (gain(kappa,A)+kappa times v)/(5-t), with the rational coefficients interpreted in the reals.

**Definition 1.11 (The real demand).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.demand`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.demand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same raw-demand expression is evaluated at a real low allocation. The palette coefficients remain the specified rational constants.

**Definition 1.12 (Simultaneous feasibility).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.claim`

*Formalization.* `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exists a subset A of the first palette and four nonnegative real allocations t0,t1,v0,v1 such that t0+t1 is at most one, v0+v1 is at most one, and both corresponding envelopes are at least one.

**Theorem 1.13 (The two real budgets are incompatible).**

Lean statement: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Simultaneous feasibility is false. A failing coarse bound gives an immediate contradiction. Otherwise increase the second low allocation to 1-t0, which enlarges its envelope because its numerator is nonnegative. The affine sum of their required lower bounds is then strictly above one, contradicting their joint unit pool. This result concerns the stated scalar inequalities; deriving them from an arithmetic covering family is a separate implication.

## References

- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.budget`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.claim`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.demand`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.envelope`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.gain`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.ordinaryProduct`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.ordinaryWeight`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.otherPalette`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.partition_obstruction`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.rawDemand`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.result`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.smallPalette`
- Truth anchor: `D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.tailPalette`

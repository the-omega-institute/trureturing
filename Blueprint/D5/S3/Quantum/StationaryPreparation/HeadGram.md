# Head Occupation Gram Construction

## Abstract

Cumulative square-root increments realize the head occupation kernel in a small memory span.

**Theorem 1.1 (The explicit Gram family, recurrence, and span).**

$$\forall a: sigma \to Nat, h: sigma,\ {\forall r,s: Box\left(a\right), inner\left(chi\left(r\right), chi\left(s\right)\right) = K\left(r, s\right)} \land\ {\forall r,s: Profiles\left(sigma\right), r \neq 0, s \neq 0 \implies K\left(r, s\right) = commonPositiveLoweringSum\left(r, s\right)} \land\ finrank\left(Complex, H\left(a, h\right)\right) \leq product\left(aPlusOne\left(a\right)\right) - a\left(h\right) \land\ {0 < a\left(h\right) \implies span\left(nonterminalChi\left(a, h\right)\right) = H\left(a, h\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/HeadGram.head_gram_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let sigma be finite, let a assign a natural capacity to every letter, and choose any head h in sigma. Box(a) contains r with 0<=r(i)<=a(i). Write M(r)=|r|!/product(i,r(i)!), where |r| is the total occupation. Two profiles have the same tail when they agree away from h. Define K(r,s)=M(min(r,s)) for equal tails and K(r,s)=0 otherwise; min is coordinatewise.

For a tail b and natural j, let m(b,j)=M(j,b). Its value is a fixed positive tail multinomial times choose(j+|b|,|b|), so it is nondecreasing in j. Put delta(b,0)=m(b,0) and delta(b,j)=m(b,j)-m(b,j-1) for j>0. In the complex Euclidean space indexed by bounded tails and head levels 0 through a(h), the vector chi(r) has coordinate sqrt(delta(b,k)) when b is the tail of r and k<=r(h), and zero otherwise. All roots are nonnegative real roots.

Let H be the complex span of these vectors. Their inner product is K(r,s): different tails have disjoint support, and equal tails give a telescoping sum through min(r(h),s(h)). Thus K is the actual positive semidefinite Gram matrix. For nonzero r and s the recurrence sums K(r-e(i),s-e(i)) over letters with both occupations positive. Simultaneous lowering preserves tail equality, and the multinomial erasure identity proves the recurrence at the coordinatewise minimum.

All pure-head vectors coincide with chi(0). Removing the a(h) nonzero pure-head profiles from the generating family leaves a spanning family of size product(i,a(i)+1)-a(h). This proves the dimension upper bound. If a(h)>0, chi(0)=chi(e(h)), so the nonterminal vectors alone span H. Zero capacities and equal maximizing head capacities require no exclusions.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/HeadGram.head_gram_realization`
- Dependency: [D5/S3/Quantum/StationaryPreparation/PhysicalGram](PhysicalGram.md)

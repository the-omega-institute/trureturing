# Cyclic contracted-algebra coefficients

## Abstract

Exact powers and the field criterion in the two cyclic contracted algebras.

**Definition 1.1 (The actual generator span).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.combination`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.combination` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The vector is the sum of a(i) times the basis image of generator i in the original contracted Finsupp algebra of Model n q. Both Boolean presentations use this same construction. No constant basis element or identity is introduced.

**Theorem 1.2 (Complete terminal coefficients).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.terminal_coefficients`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.terminal_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every positive n, every field F, both presentations and arbitrary a,b,c in F, the nth power of ax+by+cz is exactly ((a+b)^n-b^n) times terminal 0, plus ((b+c)^n-c^n) times terminal 1, plus ((c+a)^n-a^n) times terminal 2. This equality excludes every other support coordinate. The proof expands actual products of basis images, reduces their monomial multisets by normal_mul, and evaluates the two-letter and one-letter word filters. Unitization is used only to apply the pinned finite sum-power theorem; the result is an identity in the original nonunital algebra. positivePower v k always means k+1 factors.

**Theorem 1.3 (Every positive multiple of six).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.root_witness`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.root_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every positive n divisible by six and every primitive cube root omega in F, the actual vector x+omega y+omega^2 z belongs to the three-generator span, is nonzero, and has nth power zero, for either presentation. The coefficient of x is one and the three generator basis images are distinct for n at least two. The geometric sum 1+omega+omega^2=0, evenness of n and divisibility by three cancel all terminal coefficients. This applies in particular over every characteristic-zero field containing such a root.

**Theorem 1.4 (The exact sixth-power field criterion).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.sixth_power_criterion`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.sixth_power_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every characteristic-zero field and either n=6 presentation, a nonzero vector of the actual three-generator span has sixth power zero if and only if the field contains a primitive cube root. A nonzero cancellation has all three generator coefficients nonzero. The ratios (a+b)/b, (b+c)/c, (c+a)/a are sixth roots unequal to one. If there is no primitive cube root, factoring X^6-1 forces all three ratios to be minus one; the resulting equations give 9a=0, a contradiction in characteristic zero.

**Theorem 1.5 (All three actual two-generator spans).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.pair_span_nonvanishing`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.pair_span_nonvanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every n at least two, every field and either presentation, choose any one of the three generators to omit. Every nonzero vector in the span of the other two basis images has nonzero nth power. A coordinate functional vanishes on that span, and the terminal coefficient identities then force the other two coefficients to vanish if the power vanishes. In particular this proves all three n=6 assertions.

For these two n=6 presentations the criterion rules out cancellation over Q and R and permits it over Q(omega) and C. The application uses the usual absence of nontrivial cube roots in ordered fields and the primitive cube roots in those extensions. It makes no obstruction claim for other rational semigroups. The original Question-15 partition remains distinct from both cyclic presentations. No general Question-11 or characteristic-p Eggert conclusion follows here. The related residue-class binomial identities and root-of-unity filtering are prior mathematics, including Benjamin and Scott, Theorem 1.1 and its proof. The present statements concern the specified semigroups and algebras.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.combination`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.pair_span_nonvanishing`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.root_witness`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.sixth_power_criterion`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanCyclicCoefficients.terminal_coefficients`
- Dependency: [D5/S0/Certificates/Algebra/BergmanContractedAlgebra](BergmanContractedAlgebra.md)
- Dependency: [D5/S0/Certificates/Algebra/BergmanCyclicSemigroup](BergmanCyclicSemigroup.md)

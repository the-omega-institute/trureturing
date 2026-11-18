# Noncommutative semigroups and contracted witnesses

## Abstract

Two actual noncommutative nilpotent constructions preserve contracted span cancellation.

**Definition 1.1 (The four-element auxiliary semigroup).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.FourElement`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.FourElement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The carrier consists of the four distinct elements zero,p,q,r. Its only nonzero product is pq=r. Every triple product is zero in either bracketing, so the multiplication is associative. In particular pq differs from qp=zero.

**Definition 1.2 (The full Cartesian product).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.ProductModel`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.ProductModel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Take the full direct product of the actual cyclic xyz-zero quotient Model 6 true with the four-element auxiliary semigroup. Every pair occurs, including pairs with exactly one zero component. Multiplication is componentwise and only the pair (zero,zero) is the absorbing zero. The size is therefore 49 times 4, or 196; this construction is distinct from a smash product.

**Definition 1.3 (The original quotient inside the product).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.includeZero`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.includeZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The map s to (s,zero) is injective, preserves zero and preserves multiplication on the actual quotient49. No quotient elements are identified by this inclusion.

**Definition 1.4 (The contracted algebra embedding).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.embedding`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.embedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Apply the existing BergmanContractedAlgebra.mapHom to the literal inclusion s to (s,zero). This is an F-linear multiplicative map between the original contracted Finsupp algebras, with no commutativity assumption on the target. The induced linear map of the first projection is a left inverse, as checked on every scalar basis vector and extended linearly. It therefore gives an injective homomorphism of nonunital algebras.

**Theorem 1.5 (The product preserves the sixth-power witness).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.product_family`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.product_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Over every field, the full product has 196 elements and is strictly noncommutative: (zero,p)(zero,q)=(zero,r), whereas the reversed product is zero. The contracted embedding sends the basis image of s to the basis image of (s,zero). The three included generators have pairwise distinct nonzero sixth powers. Every seven-fold product of arbitrary semigroup elements is zero. The entire subspace spanned by seven-fold products of arbitrary algebra vectors is zero as well, and the sixth power of the first included generator basis vector survives. Thus both exact nilpotency indices are seven. For each primitive cube root omega in the field, take the existing cyclic quotient's actual nonzero sixth-power-zero witness u. Its image is a nonzero vector in the span of the three included generator images and still has sixth power zero. The source construction of u is x+omega*y+omega^2*z; its coefficient at x is one. Multiplicativity preserves that very witness, rather than introducing an unrelated algebra. This includes every characteristic-zero field containing a primitive cube root, with its original field hypothesis intact.

**Definition 1.6 (The actual right-zero truncation).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.RightZero`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.RightZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For a natural n, the carrier has a separate zero and a pair (i,a) for every degree 1 through n and every label a in {e,f}. The Lean index in Fin n is one less than the written degree. Multiply (i,a) by (j,b) to obtain (i+j,b) when i+j is at most n, and zero otherwise. Both bracketings of a triple keep the rightmost label and total degree when that degree is at most n; otherwise both are zero. This is a literal carrier with associative multiplication and a two-sided absorbing zero.

**Definition 1.7 (The two degree-one generators).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.generator`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.generator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Choose x=(1,e) and y=(1,f). These are distinct nonzero elements. For each k below n their (k+1)st powers are (k+1,e) and (k+1,f). In particular their nth powers are distinct and nonzero. When n is at least two, xy=(2,f) differs from yx=(2,e).

**Definition 1.8 (The contracted square-zero vector).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.difference`

*Formalization.* `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.difference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

In the original contracted algebra take the basis image of x minus that of y. This is nonzero because its coefficient at x is one. Its square is (2,e)-(2,f)-(2,e)+(2,f)=zero. The semigroup zero maps to the zero vector and is never included as an extra basis vector.

**Theorem 1.9 (The full quantified right-zero family).**

Lean statement: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.right_zero_family`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.right_zero_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

For every n at least two, the actual carrier has exactly 2n+1 elements and is strictly noncommutative. Its two generators have distinct nonzero nth powers. Over every field, their contracted difference is a nonzero member of their span, has square zero and hence nth power zero. Every product of n+1 arbitrary semigroup elements vanishes. The whole subspace spanned by n+1-fold products of arbitrary contracted algebra vectors vanishes, so every such vector product vanishes. The nth power of the first generator's basis image is nonzero, which makes both exact nilpotency indices n+1. No cube-root hypothesis is required here; in particular the claim holds over every characteristic-zero field. The application n=6 has 13 elements and exact common index seven. These numerical applications require no additional retained theorem wrappers.

The arbitrary-vector bounds follow from the actual object correspondence: the span of basis images of all (k+1)-fold semigroup products equals the (k+1)-fold contracted product subspace. Bilinearity and a split of each actual positive word prove this equality by induction. Semigroup nilpotence therefore controls all algebra products, rather than only the power of the displayed witness.

The square-zero identity for differences of idempotents in a common Green L- or R-class is prior work of Almeida, Margolis, Steinberg and Volkov (2007), Proposition 3.4 proof, page 11. The right-zero truncation is the source manuscript's separate semigroup consequence, using degree truncation as in Bergman's Example 12. The 196-element direct product is a different source construction and retains its cube-root witness hypothesis. These are the Question-15 branch of Question 19 only; the independent quadratic field countermodel is not this family.

The original formal59 Question-15 settlement and the distinct cyclic59 and quotient49 carriers remain separate. All positive-six-divisible-n cyclic results and arbitrary-n terminal-partition results retain their original domains. The n35 set {0,...,13,20,21} is one of four derived unfoldings of von zur Gathen and Roche's first n35 Table 2 row, not a printed I-set; their Theorem 4.4 proofs are omitted. Benjamin and Scott's binomial identities remain prior. No novelty, priority, minimality, additional paper or solved-credit claim is made. Universal Question 11, Questions 16-18 and the characteristic-p Eggert conjecture are outside this result. Wenlin Zhang is affiliated with National University of Singapore and ChronoAI Pte Ltd, Singapore; Haobo Ma with ChronoAI Pte Ltd, Singapore only.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.FourElement`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.ProductModel`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.RightZero`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.difference`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.embedding`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.generator`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.includeZero`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.product_family`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup.right_zero_family`
- Dependency: [D5/S0/Certificates/Algebra/BergmanCyclicGrading](BergmanCyclicGrading.md)

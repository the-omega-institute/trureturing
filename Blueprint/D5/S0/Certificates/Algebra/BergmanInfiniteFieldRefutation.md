# The infinite-field branch of Bergman's Question 19 for Question 16

## Abstract

An associative commutative nilpotent rational algebra of dimension three has a two-dimensional subspace on which every nonzero vector has nonzero square.

**Definition 1.1 (One common vanishing product length).**

$$\forall (F : \operatorname{Type}^{*}), [\operatorname{Field}\left(F\right)] \forall (R : \operatorname{Type}^{*}), [\operatorname{AddCommGroup}\left(R\right)] [\operatorname{Module}\left(F, R\right)] \forall (\mu : \operatorname{LinearMap}\left(F, R, \operatorname{LinearMap}\left(F, R, R\right)\right)), (\operatorname{CommonNilpotent}\left(F, R, \mu\right) : \operatorname{Prop}) \Leftrightarrow (\exists (k : \mathbb{N}), \forall (xs : \operatorname{List}\left(R\right)), \forall (z : R), (\operatorname{length}\left(xs\right) = k) \Rightarrow (\operatorname{foldr}\left(\mu, z, xs\right) = 0))$$

*Formalization.* `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.CommonNilpotent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

LinearMap(F,A,B) denotes an F-linear map from A to B. Thus the curried type LinearMap(F,R,LinearMap(F,R,R)) supplies actual F-bilinear multiplication. Type* permits arbitrary universes. The implicit scalar and carrier arguments are displayed explicitly. foldr(mu,z,xs) means xs.foldr (fun x y => mu x y) z, with the terminal factor z included. A list of length k therefore gives k+1 factors; k=0 permits only the zero algebra. The quantifier selects one length for every list and terminal factor. Under associativity this is the usual global nilpotence condition, equivalently vanishing of the corresponding product-span.

**Definition 1.2 (The complete affirmative field assertion).**

$$(claim : \operatorname{Prop}) \Leftrightarrow (\forall (F : \operatorname{Type}), [\operatorname{Field}\left(F\right)] [\operatorname{Infinite}\left(F\right)] \forall (R : \operatorname{Type}), [\operatorname{AddCommGroup}\left(R\right)] [\operatorname{Module}\left(F, R\right)] [\operatorname{FiniteDimensional}\left(F, R\right)] \forall (\mu : \operatorname{LinearMap}\left(F, R, \operatorname{LinearMap}\left(F, R, R\right)\right)), (\forall (x : R), \forall (y : R), \forall (z : R), \mu(\mu(x,y),z) = \mu(x,\mu(y,z))) \Rightarrow ((\forall (x : R), \forall (y : R), \mu(x,y) = \mu(y,x)) \Rightarrow ((\operatorname{CommonNilpotent}\left(F, R, \mu\right)) \Rightarrow (\forall (V : \operatorname{Submodule}\left(F, R\right)), \forall (n : \mathbb{N}), (0 < n) \Rightarrow ((\forall (v : R), (v \in V) \Rightarrow ((v \ne 0) \Rightarrow (\operatorname{foldr}\left(\mu, v, \operatorname{replicate}\left(n - 1, v\right)\right) \ne 0))) \Rightarrow (n \cdot \operatorname{finrank}\left(F, V\right) \le \operatorname{finrank}\left(F, R\right)))))))$$

*Formalization.* `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.claim` (`✓ std3`).

*Citation.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Bergman's Question 16 asks for the dimension bound over algebraically closed fields. Question 19 explicitly asks whether that assumption can be dropped, or weakened to an infinite field. The displayed closed claim is the infinite-field alternative, with associativity and commutativity retained. The source's Convention 2 assumes associative algebras, without requiring an identity. No identity is introduced here. Every dimension and linearity condition uses F. The subspace V is a Submodule, and finrank(F,V) is the dimension of its subtype. Natural subtraction is truncated; for the required positive n, replicate(n-1,v) followed by v has exactly n factors, including n=1. The assertion quantifies over all nonzero vectors, all positive exponents, all finite-dimensional carriers and all infinite fields in Type, without an ordering or characteristic hypothesis.

**Definition 1.3 (A bilinear quadratic multiplication).**

$$\forall (F : \operatorname{Type}^{*}), [\operatorname{Field}\left(F\right)] \operatorname{product}\left(F\right) : \operatorname{LinearMap}\left(F, ((F \times F) \times F), \operatorname{LinearMap}\left(F, ((F \times F) \times F), ((F \times F) \times F)\right)\right), \forall (a : F), \forall (b : F), \forall (c : F), \forall (d : F), \forall (e : F), \forall (f : F), \operatorname{product}\left(F, ((a,b),c), ((d,e),f)\right) = ((0,0),a \cdot d + b \cdot e)$$

*Formalization.* `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.product` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Use the ordinary product vector space (F x F) x F, with its coordinatewise addition and scalar multiplication, for any field F. The displayed type is a curried linear map, constructed by LinearMap.mk2; the four additivity and scalar-linearity obligations are proved in its definition. Only the first two coordinates enter the scalar product. Every output lies on the third-coordinate line, which annihilates the whole algebra. Consequently both bracketings of every triple product are zero, and symmetry of the scalar product gives commutativity. These laws are verified for the rational model in the proof of result.

**Definition 1.4 (The coordinate plane as a linear range).**

$$\forall (F : \operatorname{Type}^{*}), [\operatorname{Field}\left(F\right)] \operatorname{modelSubspace}\left(F\right) : \operatorname{Submodule}\left(F, ((F \times F) \times F)\right), \operatorname{modelSubspace}\left(F\right) = \operatorname{range}\left(\operatorname{inl}\left(F, (F \times F), F\right)\right)$$

*Formalization.* `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.modelSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

The map inl(F,F x F,F) is the linear injection w maps to (w,0). Its range is precisely the coordinate plane of vectors ((a,b),0). This is a genuine linear subspace, rather than an arbitrary set of individually selected vectors. Injectivity and the dimension of a linear range give its dimension two over the same F.

**Theorem 1.5 (The infinite-field dimension bound fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bergman-question19-question16-field-condition` (refuted) by `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bergman-question19-question16-field-condition","declaration_gid":"D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* George M. Bergman (2014). *Thoughts on Eggert's Conjecture*. DOI: [10.1090/conm/609/12101](https://doi.org/10.1090/conm/609/12101). URL: <https://arxiv.org/abs/1206.0326v2>.

*Commentary.*

Take F=Q, R=(Q x Q) x Q, V=modelSubspace(Q), and n=2. The field Q is infinite and the ambient dimension is three. Every product of three elements is zero, witnessed by k=2 in CommonNilpotent. For a vector ((a,b),0) in V its square is ((0,0),a*a+b*b). The ordered-field identity mul_self_add_mul_self_eq_zero implies that this vanishes only when a=b=0, so every nonzero vector in V has nonzero square. The dimension of V is two, and the asserted bound would read 2*2 <= 3, which is false. Associativity, commutativity, common nilpotence, nonannihilation and both dimensions are established inside the proof; none is assumed as a countermodel premise. Since Q is infinite, this also rules out the alternative with no field restriction. It does not settle Question 16 over algebraically closed fields, the noncommutative branches of Question 19, or Eggert's conjecture.

Bergman's Example 20 already uses an inner product and graded pieces of dimensions d,1,d to obtain a nonassociative real cubing example. The quadratic mechanism here is its degree-one/degree-two truncation: the scalar output is made annihilating, so every triple product vanishes and associativity holds. The model uses rational coordinates and squares at n=2, rather than the source's nonassociative cubing at n=3. Credit for the inner-product mechanism belongs to Bergman. The bounded literature screen located no exact settlement of this associative field branch; worldwide priority remains unverified.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.CommonNilpotent`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.modelSubspace`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.product`
- Truth anchor: `D5/S0/Certificates/Algebra/BergmanInfiniteFieldRefutation.result`

# A simplicial-poset Chow counterexample

## Abstract

Two tetrahedra sharing a vertex have a non-real-rooted Chow polynomial.

**Definition 1.1 (Rank in the original poset).**

$$\forall (P:\operatorname{Type})[\operatorname{PartialOrder}\left(P\right)](x:P),\operatorname{rank}\left(x\right) = (\operatorname{Order}.\operatorname{height}(x)).\operatorname{toNat}$$

*Formalization.* `D5/S3/Zeros/SimplicialPosetChowRefutation.rank` (`✓ std3`).

*Citation.* Elena Hoster and Christian Stump (2025). *Chow polynomials of simplicial posets with positive h-vector are real-rooted*. URL: <https://arxiv.org/abs/2508.15538v1>.

*Commentary.*

Section 1, p. 1 uses the rank of a face. The rank is (Order.height x).toNat: the number of strict steps from the bottom to x in a finite graded poset.

**Definition 1.2 (Finite graded simplicial posets).**

$$\forall (P:\operatorname{Type})[\operatorname{Fintype}\left(P\right)][\operatorname{DecidableEq}\left(P\right)][\operatorname{PartialOrder}\left(P\right)][\operatorname{OrderBot}\left(P\right)](n:\operatorname{Nat}),\operatorname{simplicial}\left(P, n\right) = (\forall (m:P),\operatorname{IsMax}\left(m\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{OrderIso}\left(\operatorname{Set}.\operatorname{Iic}(m), \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Zeros/SimplicialPosetChowRefutation.simplicial` (`✓ std3`).

*Citation.* Elena Hoster and Christian Stump (2025). *Chow polynomials of simplicial posets with positive h-vector are real-rooted*. URL: <https://arxiv.org/abs/2508.15538v1>.

*Commentary.*

Section 1, p. 1: “Let P be a finite graded simplicial poset. This is, P is a finite poset with 0̂ for which all maximal intervals are boolean of the same rank n.” Set.Iic m is the lower interval. The subset order on Finset (Fin n) is the Boolean lattice of rank n. The assumptions include Fintype, DecidableEq, PartialOrder and OrderBot; no positivity assumption on the h-vector is added.

**Definition 1.3 (The flag f-vector).**

$$\forall (P:\operatorname{Type})[\operatorname{Fintype}\left(P\right)][\operatorname{DecidableEq}\left(P\right)][\operatorname{PartialOrder}\left(P\right)][\operatorname{OrderBot}\left(P\right)](n:\operatorname{Nat})(T:\operatorname{Finset}\left(\operatorname{Nat}\right)),\operatorname{alpha}\left(P, n, T\right) = \operatorname{let} Q:\operatorname{Type}=\{x:\operatorname{WithTop}\left(P\right) \mid x = \operatorname{Bot}.\operatorname{bot} \lor \left(x = \operatorname{Top}.\operatorname{top} \lor \operatorname{WithTop}.\operatorname{recTopCoe}(n+1,(\operatorname{rank}:P \to \operatorname{Nat}),x) \in T\right)\};((((\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(Q\right))).\operatorname{powerset}).\operatorname{filter}(\lambda (C:\operatorname{Finset}\left(Q\right)),\operatorname{IsMaxChain}\left((\cdot \le \cdot), (C:\operatorname{Set}\left(Q\right))\right))).\operatorname{card}$$

*Formalization.* `D5/S3/Zeros/SimplicialPosetChowRefutation.alpha` (`✓ std3`).

*Citation.* Elena Hoster and Christian Stump (2025). *Chow polynomials of simplicial posets with positive h-vector are real-rooted*. URL: <https://arxiv.org/abs/2508.15538v1>.

*Commentary.*

Section 1, p. 1: “for α_P̂(T) being the flag f-vector counting maximal chains in the subposet of P̂ with only the ranks in T selected.” The selected subtype Q of WithTop P contains bottom, the added top, and elements of intrinsic rank in T. WithTop.recTopCoe gives the added top rank n+1 and original elements rank (Order.height x).toNat. The powerset filter counts exactly IsMaxChain sets. Example 1.3 fixes α(∅)=1. A consumed private lemma equates this literal count and the computation on P₂ for the isolated rank sets in {2,…,4}, which include all subsets required by the β sums in (1.1).

**Definition 1.4 (The flag h-vector).**

$$\forall (P:\operatorname{Type})[\operatorname{Fintype}\left(P\right)][\operatorname{DecidableEq}\left(P\right)][\operatorname{PartialOrder}\left(P\right)][\operatorname{OrderBot}\left(P\right)](n:\operatorname{Nat})(S:\operatorname{Finset}\left(\operatorname{Nat}\right)),\operatorname{beta}\left(P, n, S\right) = \sum_{T \in (S).\operatorname{powerset}}(-1)^{(S\setminus T).\operatorname{card}}\cdot (\operatorname{alpha}\left(P, n, T\right):\mathbb{Z})$$

*Formalization.* `D5/S3/Zeros/SimplicialPosetChowRefutation.beta` (`✓ std3`).

*Citation.* Elena Hoster and Christian Stump (2025). *Chow polynomials of simplicial posets with positive h-vector are real-rooted*. URL: <https://arxiv.org/abs/2508.15538v1>.

*Commentary.*

Section 1, p. 1 defines β_P̂(S) = Σ_{T⊆S} (−1)^{|S∖T|} α_P̂(T). The sum is over S.powerset, with integer coefficients and the natural count alpha P n T explicitly cast to integers.

**Definition 1.5 (Isolated rank sets).**

$$\forall (S:\operatorname{Finset}\left(\operatorname{Nat}\right)),\operatorname{isolated}\left(S\right) = (\forall i\in S,\neg (i+1\in S))$$

*Formalization.* `D5/S3/Zeros/SimplicialPosetChowRefutation.isolated` (`✓ std3`).

*Citation.* Elena Hoster and Christian Stump (2025). *Chow polynomials of simplicial posets with positive h-vector are real-rooted*. URL: <https://arxiv.org/abs/2508.15538v1>.

*Commentary.*

Section 1, p. 1: “Here, a set S ⊂ ℤ is isolated if i ∈ S implies i+1 ∉ S.” The selected ranks are natural numbers; the same adjacency condition applies.

**Definition 1.6 (The Chow polynomial).**

$$\forall (P:\operatorname{Type})[\operatorname{Fintype}\left(P\right)][\operatorname{DecidableEq}\left(P\right)][\operatorname{PartialOrder}\left(P\right)][\operatorname{OrderBot}\left(P\right)](n:\operatorname{Nat}),\operatorname{H}\left(P, n\right) = \sum_{S \in ((\operatorname{Finset}.\operatorname{Icc}(2,n)).\operatorname{powerset}).\operatorname{filter}(\operatorname{isolated})}\operatorname{Polynomial}.\operatorname{C}(\operatorname{beta}\left(P, n, S\right))\cdot \operatorname{Polynomial}.\operatorname{X}^{(S).\operatorname{card}}\cdot (1+\operatorname{Polynomial}.\operatorname{X})^{n-2\cdot (S).\operatorname{card}}$$

*Formalization.* `D5/S3/Zeros/SimplicialPosetChowRefutation.H` (`✓ std3`).

*Citation.* Elena Hoster and Christian Stump (2025). *Chow polynomials of simplicial posets with positive h-vector are real-rooted*. URL: <https://arxiv.org/abs/2508.15538v1>.

*Commentary.*

Section 1, p. 1, (1.1): H_P̂(x) = Σ_{S⊆{2,…,n}, S isolated} β_P̂(S) x^{|S|} (1+x)^{n−2|S|}. The formal polynomial has integer coefficients. The filter selects isolated subsets of Finset.Icc 2 n. The exponent uses natural-number subtraction; C is Polynomial.C and X is Polynomial.X.

**Definition 1.7 (The first real-rootedness assertion).**

$$\operatorname{claim} = (\forall (P:\operatorname{Type})[\operatorname{Fintype}\left(P\right)][\operatorname{DecidableEq}\left(P\right)][\operatorname{PartialOrder}\left(P\right)][\operatorname{OrderBot}\left(P\right)](n:\operatorname{Nat}),\operatorname{simplicial}\left(P, n\right) \Rightarrow \operatorname{D5}.\operatorname{S3}.\operatorname{Zeros}.\operatorname{Jensen}.\operatorname{JensenPolynomialObstruction}.\operatorname{PolynomialHyperbolic}((\operatorname{H}\left(P, n\right)).\operatorname{map}(\operatorname{Int}.\operatorname{castRingHom}(\operatorname{Real}))))$$

*Formalization.* `D5/S3/Zeros/SimplicialPosetChowRefutation.claim` (`✓ std3`).

*Citation.* Elena Hoster and Christian Stump (2025). *Chow polynomials of simplicial posets with positive h-vector are real-rooted*. URL: <https://arxiv.org/abs/2508.15538v1>.

*Commentary.*

Conjecture 1.5, p. 3: “Let P be a simplicial poset. Then H_P̂(x), H_P̂*(x) and H^aug_P̂(x) are real-rooted. Moreover, the roots of both H_P̂(x) and H_P̂*(x) interlace the roots of H^aug_P̂(x) = H^aug_P̂*(x).” The claim quantifies over every finite partial order P with bottom and every n : ℕ, and asserts simplicial P n → D5.S3.Zeros.Jensen.JensenPolynomialObstruction.PolynomialHyperbolic ((H P n).map (Int.castRingHom ℝ)). The predicate says every complex zero of the real coefficient polynomial is real. It is the first real-rootedness assertion, which the full conjecture implies.

**Theorem 1.8 (Conjecture 1.5 is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/SimplicialPosetChowRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hoster-stump-2025-chow-polynomials-simplicial-posets` (refuted) by `D5/S3/Zeros/SimplicialPosetChowRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hoster-stump-2025-chow-polynomials-simplicial-posets","declaration_gid":"D5/S3/Zeros/SimplicialPosetChowRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Elena Hoster and Christian Stump (2025). *Chow polynomials of simplicial posets with positive h-vector are real-rooted*. URL: <https://arxiv.org/abs/2508.15538v1>.

*Commentary.*

The face poset consists of all subsets of {0,1,2,3} or {0,4,5,6}, ordered by inclusion, with the empty face as bottom. Each maximal interval is Boolean of rank four. Its flag f-values on ∅, {2}, {3}, {4}, {2,4} are 1, 12, 8, 2, 12, giving flag h-values 1, 11, 7, 1, −1. Thus (1.1) is X⁴+23X³+43X²+23X+1. Put a=(23−√365)/2 and b=(23+√365)/2. The polynomial factors as (X²+aX+1)(X²+bX+1). Since 0<a<2, z=(−a+i√(4−a²))/2 is a zero with positive imaginary part. This contradicts the universal first assertion.

## References

- Truth anchor: `D5/S3/Zeros/SimplicialPosetChowRefutation.H`
- Truth anchor: `D5/S3/Zeros/SimplicialPosetChowRefutation.alpha`
- Truth anchor: `D5/S3/Zeros/SimplicialPosetChowRefutation.beta`
- Truth anchor: `D5/S3/Zeros/SimplicialPosetChowRefutation.claim`
- Truth anchor: `D5/S3/Zeros/SimplicialPosetChowRefutation.isolated`
- Truth anchor: `D5/S3/Zeros/SimplicialPosetChowRefutation.rank`
- Truth anchor: `D5/S3/Zeros/SimplicialPosetChowRefutation.result`
- Truth anchor: `D5/S3/Zeros/SimplicialPosetChowRefutation.simplicial`
- Dependency: [D5/S3/Zeros/Jensen/JensenPolynomialObstruction](Jensen/JensenPolynomialObstruction.md)

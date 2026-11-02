# Negative Rank One Has No Finite Strong Generating Family

## Abstract

Every finite family of arbitrary actual states has a proper negative-word span in negative rank one.

For an integer d, datum(d) is the actual even LatticeData of rank one with Gram entry -2d. The charge charge(d,s) is the constant function Fin(1) to Z with value s. The actual bilinear form is B(s,t)=-2dst, chargeEnergy(s)=-ds^2, and a charge-s oscillator monomial of oscillator energy r has energy r-ds^2. The carrier is the full finite-support charge direct sum of complex oscillator polynomials, with the original all-state map LatticeAllStateField.Y.

For a finite set S of arbitrary actual states, negativeWord(D,S) evaluates every finite list of pairs (a,n), with a in S and n a natural number: W([])=vacuum and W((a,n)::w)=Y(a)_(-n-1) W(w), using normalized coefficients. negativeWordSpan is the complex linear span of this entire range, including the empty word. StronglyGenerates(D,S) means exactly that this subspace equals the whole actual carrier. This specifies the right-nested convention. Word length, negative mode order, oscillator degree and the finite charge mixtures in S are unrestricted.

**Theorem 1.1 (Every finite arbitrary-state family has a proper negative-word span).**

$$\forall d\in \mathbb{Z}, 0<d\Rightarrow \forall S\in \operatorname{Finset}\left(\operatorname{Carrier}\left(\operatorname{datum}\left(d\right)\right)\right), \neg \operatorname{StronglyGenerates}\left(\operatorname{datum}\left(d\right), S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.negative_rank_one_no_finite_strong_generation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be the maximum absolute charge in the union of the finite charge supports of S, with maximum zero for an empty union. Linearity of the original Y expands every mixed state into its actual charge-homogeneous components. Enlarge the labels to all single(charge(d,s),p) with -M<=s<=M and arbitrary oscillator polynomial p. Finite charge expansion and induction on words put the original negative-word span inside this enlarged palette span.

For q>M, let lambda_q extract the oscillator-constant coefficient in charge q. On actual charge/oscillator basis vectors, charge homogeneity and actual_mode_grade force a nonzero outer-insertion coefficient at a negative mode m to satisfy 0=r+t+2ds(q-s)-m-1. If 0<s<=M, positivity of d and q-s makes this impossible. For s=0 a nonconstant oscillator monomial has strictly positive oscillator energy, giving the same vanishing. The remaining scalar oscillator constant is a multiple of the actual vacuum, whose field has identity mode -1 and zero at all other modes. Basis extension gives these insertion statements on arbitrary inputs. There is no positive-definite Gram or lower-bounded-total-energy premise.

Strong induction on total word length proves that lambda_q kills every palette word. A word with only negative-charge labels has nonpositive total charge; this also handles the empty word. Otherwise take its first nonnegative-charge label a. An inner induction moves a left across its initial negative-charge prefix. Swapping adjacent labels b,a uses the actual finite mode_commutator. The j-th correction is the actual state b_j a at mode m+n-j. Charge homogeneity writes it as one palette label: its charge is charge(b)+charge(a), still in [-M,M], and its mode is strictly negative. Each correction replaces two factors by one. The outer induction therefore kills it with its full outer prefix and tail. The swapped term advances the inner induction. At the far left a positive label vanishes by the insertion calculation; a zero-charge label gives a scalar multiple of a shorter word under lambda_q. No same-sign commutation or assumed normal form is used.

Consequently the enlarged palette span lies in ker(lambda_q), whereas lambda_q(single(charge(d,q),1))=1. Taking q=M+1 makes the enlarged span, and hence the original arbitrary-state span, proper.

The charge-palette and shorter-word proof is an author-supplied derivation from the repository's actual_mode_grade, charge_homogeneity and finite mode_commutator. The original lattice-field construction retains the Bakalov--Kac math/0402315v1 section 4.1 attribution; its residue and locality suppliers retain their Matsuo--Nagatomo and Carnahan attributions. Mathlib supplies basis extension, finite-support expansion and linear spans. No external-literature novelty or equivalence with other bracketing conventions is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.negative_rank_one_no_finite_strong_generation`
- Dependency: [D5/S3/VertexAlgebra/Energy/LatticeCoefficientEnergy](../Energy/LatticeCoefficientEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus](../LatticeActualStateFieldCalculus.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner](../Sectors/LatticeSectorIntertwiner.md)

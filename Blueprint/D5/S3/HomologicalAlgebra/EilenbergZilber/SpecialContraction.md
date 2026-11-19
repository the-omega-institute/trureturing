# The special contraction identities

## Abstract

The special contraction identities

Take independent universe levels u and v, C : Type u with Category.{v} C and Abelian C, an arbitrary bisimplicial object X, and any natural degree n. The diagonal normalized complex is NTwo(X), and NOne(X) is the twice-normalized total. Write S for normalizedShuffleMap X : NOne(X) → NTwo(X), A for normalizedAlexanderWhitney X : NTwo(X) → NOne(X), and H(n) for the existing phiHomNorm X n (n+1). In the displayed formula, Category(v,C) means Category.{v} C, component(f,n) means f.f n, and then(f,g) means f followed by g, namely Lean’s f ≫ g.

The recursive operator is exactly phiOp(0)=0 and phiOp(n+1)=−(phiOp n).prime+(hOp(n+1)).prime.comp(D0op(n+1)). The convention MTwo.comp MOne applies MOne first. Realization is contravariant in the paired simplex maps and covariant as a morphism from degree s to degree q for DerivedOp(s,q). The normalized H is diagonal Moore inclusion, followed by this realized phiOp, followed by Moore retraction.

For a supported paired map of phiOp, the first coordinate has an adjacent repeat j and the second has an adjacent repeat k with j ≤ k. Priming shifts both repeats. In the other recursive summand, horizontal frontality gives a repeat at zero; monotonicity from a longer simplex to a shorter one supplies the second repeat. Every hOp split encounters one of these repeats, so hOp(n+1).comp(phiOp n) is a structural norm.

The signed first-step shuffle recursion gives the other mixed norm, (phiOp n).comp(hOp n), by cancellation of the unique surviving staircase at the matching split. The two mixed norms both enter the induction for (phiOp(n+1)).comp(phiOp n): its successor is the prime of the preceding square, minus the primed phi-h mixed term followed by D0, plus the primed h-phi mixed term followed by D0. Structural norms are closed under prime, addition, negation and composition on the input side.

The same recursion shows that phiOp preserves diagonal degeneracies modulo structural norms. After realization and Moore retraction, these statements give DegeneraciesVanish for phiOp and hOp. Let P be the actual diagonal PInfty projector, equal to retraction followed by inclusion. DegeneraciesVanish kills QInfty followed by the relevant realized operator and retraction. The identity PInfty+QInfty=id therefore absorbs each intervening PInfty. This argument holds also in degree zero.

Let K=A followed by S on the normalized diagonal. The mixed norms give K(n) followed by H(n)=0 and H(n) followed by K(n+1)=0. The existing exact identity S followed by A=id gives S followed by K=S and K followed by A=A; composing these equalities yields the first two side conditions. Projector absorption and the square norm give H(n) followed by H(n+1)=0. Thus all three equalities use the actual recursive normalized homotopy in every degree.

Eilenberg and Mac Lane, On the Groups H(Π,n), II: Methods of Computation, Annals of Mathematics, second series 60 (1954), 49–139, DOI 10.2307/1969702, printed pages 53–55, develops the classical product-chain recursive homotopy and side identities. Shih, chapter II, pages 25–26 (running pages 113–114), and Franz, arXiv:2006.02819v2, footnote 3, discuss the corresponding contraction conditions. Their product or quotient normalization is distinguished from the universal paired-map calculation and the Moore-projector argument given here. The frontal and norm closure is received from Jeffrey Li’s qualified author release; the all-degree paired-map cancellation and Moore-projector argument supply the stated arbitrary abelian-category result.

**Theorem 1.1 (normalized_special_contraction).**

$$\forall u: Level, \forall v: Level, \forall C: Type u, [\operatorname{Category}\left(v, C\right)], [\operatorname{Abelian}\left(C\right)], \forall X: \operatorname{BisimplicialObject}\left(C\right), \forall n: Nat, \operatorname{then}\left(\operatorname{component}\left(\operatorname{normalizedShuffleMap}\left(X\right), n\right), \operatorname{phiHomNorm}\left(X, n, n+1\right)\right)=0 \land \operatorname{then}\left(\operatorname{phiHomNorm}\left(X, n, n+1\right), \operatorname{component}\left(\operatorname{normalizedAlexanderWhitney}\left(X\right), n+1\right)\right)=0 \land \operatorname{then}\left(\operatorname{phiHomNorm}\left(X, n, n+1\right), \operatorname{phiHomNorm}\left(X, n+1, n+2\right)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction.normalized_special_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every independent u,v, every C : Type u with Category.{v} C and Abelian C, every bisimplicial X and every n : Nat, S.f n ≫ H(n)=0, H(n) ≫ A.f(n+1)=0, and H(n) ≫ H(n+1)=0, with S, A and H as defined above. These are a conjunction of exact morphism equalities. The homotopy has the boundary A followed by S minus identity.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction.normalized_special_contraction`
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/BisimplicialNormalized](BisimplicialNormalized.md)
- Dependency: [D5/S3/HomologicalAlgebra/EilenbergZilber/SpecialContractionShuffle](SpecialContractionShuffle.md)

// Copyright (c) 2026 Jeffrey Li. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Jeffrey Li
// Received frontal and norm closure: LeanPool/EilenbergZilber/BisimplicialDerivedOp.lean,
// author release fd0147a1ffe4f3c14c247574e148893d7cdf8cf6, LeanPool PR 588.
// Modifications: universal paired-map cancellation and mathematical exposition.
// Full legal custody: Library/HomologicalAlgebra/li2026bisimplicialeilenbergzilber.md.

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.EilenbergZilber;

internal sealed class SpecialContractionDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Next(byte step) => Seq(V("n"), Plus, Num(step));
    private static Formula Hom(Formula degree, Formula target) => Call("phiHomNorm", V("X"), degree, target);
    private static Formula Component(string map, Formula degree) => Call("component", Call(map, V("X")), degree);
    private static Formula Vanishes(Formula first, Formula second) => Seq(Call("then", first, second), Eq, Num(0));
    private static Formula Statement => Disp(Seq(
        All("u", V("Level")), All("v", V("Level")),
        All("C", Seq(V("Type"), Sp, V("u"))),
        OpenBracket, Call("Category", V("v"), V("C")), CloseBracket, Comma, Sp,
        OpenBracket, Call("Abelian", V("C")), CloseBracket, Comma, Sp,
        All("X", Call("BisimplicialObject", V("C"))), All("n", V("Nat")),
        Vanishes(Component("normalizedShuffleMap", V("n")), Hom(V("n"), Next(1))), Sp, Land, Sp,
        Vanishes(Hom(V("n"), Next(1)), Component("normalizedAlexanderWhitney", Next(1))), Sp, Land, Sp,
        Vanishes(Hom(V("n"), Next(1)), Hom(Next(1), Next(2)))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The special contraction identities", H("The special contraction identities"), Blocks(
        Paragraph(Text("Take independent universe levels u and v, C : Type u with Category.{v} C and Abelian C, an arbitrary bisimplicial object X, and any natural degree n. The diagonal normalized complex is NTwo(X), and NOne(X) is the twice-normalized total. Write S for normalizedShuffleMap X : NOne(X) → NTwo(X), A for normalizedAlexanderWhitney X : NTwo(X) → NOne(X), and H(n) for the existing phiHomNorm X n (n+1). In the displayed formula, Category(v,C) means Category.{v} C, component(f,n) means f.f n, and then(f,g) means f followed by g, namely Lean’s f ≫ g.")),
        Paragraph(Text("The recursive operator is exactly phiOp(0)=0 and phiOp(n+1)=−(phiOp n).prime+(hOp(n+1)).prime.comp(D0op(n+1)). The convention MTwo.comp MOne applies MOne first. Realization is contravariant in the paired simplex maps and covariant as a morphism from degree s to degree q for DerivedOp(s,q). The normalized H is diagonal Moore inclusion, followed by this realized phiOp, followed by Moore retraction.")),
        Paragraph(Text("For a supported paired map of phiOp, the first coordinate has an adjacent repeat j and the second has an adjacent repeat k with j ≤ k. Priming shifts both repeats. In the other recursive summand, horizontal frontality gives a repeat at zero; monotonicity from a longer simplex to a shorter one supplies the second repeat. Every hOp split encounters one of these repeats, so hOp(n+1).comp(phiOp n) is a structural norm.")),
        Paragraph(Text("The signed first-step shuffle recursion gives the other mixed norm, (phiOp n).comp(hOp n), by cancellation of the unique surviving staircase at the matching split. The two mixed norms both enter the induction for (phiOp(n+1)).comp(phiOp n): its successor is the prime of the preceding square, minus the primed phi-h mixed term followed by D0, plus the primed h-phi mixed term followed by D0. Structural norms are closed under prime, addition, negation and composition on the input side.")),
        Paragraph(Text("The same recursion shows that phiOp preserves diagonal degeneracies modulo structural norms. After realization and Moore retraction, these statements give DegeneraciesVanish for phiOp and hOp. Let P be the actual diagonal PInfty projector, equal to retraction followed by inclusion. DegeneraciesVanish kills QInfty followed by the relevant realized operator and retraction. The identity PInfty+QInfty=id therefore absorbs each intervening PInfty. This argument holds also in degree zero.")),
        Paragraph(Text("Let K=A followed by S on the normalized diagonal. The mixed norms give K(n) followed by H(n)=0 and H(n) followed by K(n+1)=0. The existing exact identity S followed by A=id gives S followed by K=S and K followed by A=A; composing these equalities yields the first two side conditions. Projector absorption and the square norm give H(n) followed by H(n+1)=0. Thus all three equalities use the actual recursive normalized homotopy in every degree.")),
        Paragraph(Text("Eilenberg and Mac Lane, On the Groups H(Π,n), II: Methods of Computation, Annals of Mathematics, second series 60 (1954), 49–139, DOI 10.2307/1969702, printed pages 53–55, develops the classical product-chain recursive homotopy and side identities. Shih, chapter II, pages 25–26 (running pages 113–114), and Franz, arXiv:2006.02819v2, footnote 3, discuss the corresponding contraction conditions. Their product or quotient normalization is distinguished from the universal paired-map calculation and the Moore-projector argument given here. The frontal and norm closure is received from Jeffrey Li’s qualified author release; the all-degree paired-map cancellation and Moore-projector argument supply the stated arbitrary abelian-category result.")),
        Describe.Lean(DescribeId.Create("ez-specialcontraction-normalized-special-contraction"), DeclarationHandle.Create("D5/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction.normalized_special_contraction"), H("normalized_special_contraction"), StatementSource.FromAuthor(Statement), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every independent u,v, every C : Type u with Category.{v} C and Abelian C, every bisimplicial X and every n : Nat, S.f n ≫ H(n)=0, H(n) ≫ A.f(n+1)=0, and H(n) ≫ H(n+1)=0, with S, A and H as defined above. These are a conjunction of exact morphism equalities. The homotopy has the boundary A followed by S minus identity."))), DescribeRole.Theorem))));
}

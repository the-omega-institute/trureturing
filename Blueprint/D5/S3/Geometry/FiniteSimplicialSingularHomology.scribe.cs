using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteSimplicialSingularHomologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteSimplicialSingularHomology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered and singular integer H1 of a finite coordinate complex.", H("Ordered and singular integer H1 of a finite coordinate complex"), Blocks(
            Node("orderedchaincomplex", "orderedChainComplex", "The full ordered face complex",
                "For any finite linearly ordered V and pre-abstract simplicial complex K, degree p is the coproduct of copies of the integer module indexed by actual faces with p+1 vertices. Deletion has sign minus one to the number of smaller vertices. All degrees of K remain present.", DescribeRole.Definition),
            Node("intersectionsimplexequiv", "intersectionSimplexEquiv", "Actual intersection simplices",
                "Continuous singular simplices in a positive-coordinate face intersection correspond to small singular simplices carried by every selected star. The maps are the actual subspace inclusion and its pointwise subtype lift, and commute with singular faces.", DescribeRole.Definition),
            Node("columncoproductiso", "columnCoproductIso", "Intersection chain identification",
                "For each ordered degree p, the Cech-singular column is isomorphic as a chain complex to the coproduct of actual singular chains of the p-face intersections. The basis maps identify actual continuous simplices. Empty intersections have no generators.", DescribeRole.Definition),
            Node("columnaugmentation-isiso", "columnAugmentation_isIso", "Coefficient-sum comparison",
                "For every pair p,q of natural numbers, the actual coefficient-sum augmentation of column p induces a degree-q homology isomorphism. The proof combines the explicit chain identification, intersection contractions, and preservation of finite coproducts by homology.", DescribeRole.Theorem),
            Node("orderedh1isosingular", "orderedH1IsoSingular", "The exact degree-one comparison",
                "For every V and K above, homology of the ordered triangle-to-edge-to-vertex short complex is isomorphic to Mathlib singular homology in degree one of TopCat.of of the subtype FiniteConeCollapse.realization K, with coefficient object ModuleCat.of Z Z. The actual coefficient-sum and small-chain augmentations give the two total comparisons. No good-cover or homology-isomorphism premise is assumed. Empty realizations and ghost vertices are included.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

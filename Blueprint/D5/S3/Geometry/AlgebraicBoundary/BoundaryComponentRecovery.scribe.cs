using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class BoundaryComponentRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recovering an original full closed cone from complement components of an arbitrary boundary equation.",
        H("Entire complement components recover the original cone"),
        Blocks(
            Paragraph(Text("Let C be a closed full convex cone in a finite-dimensional real vector space, choose continuous linear coordinates, and let p be any nonzero real polynomial vanishing on the entire ambient frontier of C. Put U={p nonzero}. The closure of the union of those connected components of U that lie inside the original interior of C is exactly C. There is no degree bound, homogeneity condition or assumption that p has no zeros in the interior.")),
            Paragraph(Text("A nonzero polynomial has dense nonzero locus. Indeed, vanishing on a nonempty open set supplies a product neighborhood with an infinite set in every coordinate. Polynomial extensionality on that product forces the polynomial to be zero. Pull back density through the actual coordinate homeomorphism. Intersecting a dense set with the original open interior is dense in that interior. Convexity and full dimensionality identify the closure of the interior with the original closed cone.")),
            Paragraph(Text("A connected component of U containing an interior point cannot cross the original frontier because p vanishes there. The original interior and the complement of C are disjoint open sets covering that component. Connectedness puts the entire component in one side, and its specified interior point excludes the outside. Hence the selected components contain every point of the interior where p is nonzero. They all lie in the interior, so taking closures proves the exact recovery equality.")),
            Paragraph(Text("This recovery equality isolates the topological step of the semialgebraic argument. To conclude semialgebraicity one additionally needs that U has finitely many connected components, that each component is semialgebraic, and that semialgebraic sets are closed under taking Euclidean closure. The recovery equality itself does not assert any of these three properties.")))));
}

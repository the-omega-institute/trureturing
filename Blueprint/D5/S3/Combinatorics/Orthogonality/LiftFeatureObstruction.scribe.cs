using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class LiftFeatureObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.";
    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(
            LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original full lift-feature obstruction.", H("The original full lift-feature obstruction"),
        Blocks(
            Item("projection", "J", "The whole original projection plane",
                "The exact projection plane consists of all three-coordinate vectors with last coordinate zero.", DescribeRole.Definition),
            Item("first-lift", "fu", "The entire first lift",
                "The full linear lift sends p to (p1,p0+p1,0); on the source projection basis1,4 its T-coordinate values are12,15.", DescribeRole.Definition),
            Item("second-lift", "fw", "The entire second lift",
                "The full linear lift sends p to (p0+p1,p0,0); its source-basis values are15,3.", DescribeRole.Definition),
            Item("first-placement", "f", "The actual first quotient map",
                "The full placement map has quotient codomain T/K with K zero. The quotient is not replaced by a scalar.", DescribeRole.Definition),
            Item("second-placement", "g", "The actual second quotient map",
                "The entire second original quotient placement map has the same complete domain and quotient codomain.", DescribeRole.Definition),
            Item("kernels", "kernels", "Both entire kernels are zero",
                "Both complete quotient maps are injective.", DescribeRole.Theorem),
            Item("ranges", "ranges", "Both entire images agree",
                "Each complete image is exactly the image of the full two-dimensional coordinate plane under the canonical quotient map. In original T coordinates this is the span of masks3,12.", DescribeRole.Theorem),
            Item("ranks", "ranks", "Both full maps have rank two",
                "The actual image submodules have dimension two, using full injectivity and the complete domain equivalence.", DescribeRole.Theorem),
            Item("first-plane", "U", "The first full actual plane",
                "Represent the entire source plane from its exact K/P and quotient-valued placement.", DescribeRole.Definition),
            Item("second-plane", "W", "The second full actual plane",
                "Represent the entire second source plane from its exact K/P and placement.", DescribeRole.Definition),
            Item("source-planes", "source_planes", "Exact original source spans",
                "The represented full submodules are exactly span(13,6) and span(9,14), in the original six binary coordinates.", DescribeRole.Theorem),
            Item("adjacent", "planes_adjacent", "The original planes are adjacent",
                "The full reconstructed submodules are distinct and all pairs of their vectors have zero cross pairing. The proof consumes the complete X/Y/Z criterion.", DescribeRole.Theorem),
            Item("shear", "shearElement", "The actual original shear",
                "The simultaneous coordinate swaps0/1 and2/3 are exactly the original T/S shear diag(1,1,0). It preserves the full bilinear form and fixes T pointwise, so belongs to the entire orthogonal stabilizer.", DescribeRole.Definition),
            Item("plane-orbit", "plane_orbit", "The original plane orbit",
                "The full mapped-submodule action carries span(13,6) exactly to span(9,14), through the original generator images13 to14 and6 to9.", DescribeRole.Theorem),
            Item("shear-labels", "shear_labels", "Every clique label is fixed",
                "The actual shear fixes every full nonzero subspace of T, hence the entire original clique-label domain.", DescribeRole.Theorem),
            Item("feature-claim", "featureClaim", "The full lift-feature rule",
                "The proposed proper coloring quantifies every actual nonzero six-coordinate Submodule and every entire K/P/placement fiber, with equal actual rank, image and kernel. It includes every degenerate fiber producing a nonzero vertex.", DescribeRole.Definition),
            Item("claim", "claim", "The original feature and full-group rules",
                "The prohibited claim combines the full lift-feature rule with both entire-stabilizer coloring rules. The actual original plane orbit refutes all three branches.", DescribeRole.Definition),
            Item("result", "result", "Refute the full lift-feature and full-group rules",
                "The original planes have equal entire K/P, rank, image and kernel but are adjacent. No proper coloring can depend solely on those data. Their actual label-fixing shear orbit also refutes full-stabilizer equivariance and arbitrary-label invariance. The full placement maps still reconstruct every vertex; a structural fifteen-color assignment remains open. Finite witness-profile statistics and the written n7 bounds are separate obligations.", DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/SixDimensionalProfiles")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction"))]));
}

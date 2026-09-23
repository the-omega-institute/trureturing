using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeScalarDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual face counts are scalar coefficients with two low-degree corrections.",
        H("The auxiliary scalar polynomial"),
        Blocks(
            Paragraph(Text("This is a repository-derived coefficient reorganization of source Theorem 3.6, with no novelty claim for the published face count.")),
            Describe.Lean(
                DescribeId.Create("crown-geometric-face-count-eq-scalar-coeff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar.crownGeometricFaceCount_eq_scalar_coeff"),
                H("Geometric coefficients and the scalar sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every positive n and natural d, the rational image of the actual geometric face count equals the coefficient of degree d in S_n, with two added when d is zero and one added when d is one. Here S_n is the sum, for 1 <= m <= n, of A(n,m)(1+X)^(n+m), where A(n,m)=(n/m)choose(n+m-1,2m-1). The proof discharges natural division, binomial support and the interchange of sums. S_n is an auxiliary polynomial, not the full geometric f-polynomial."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive"))
        ]));
}

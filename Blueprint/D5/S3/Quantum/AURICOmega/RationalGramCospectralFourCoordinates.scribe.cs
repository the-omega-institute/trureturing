using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class RationalGramCospectralFourCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/RationalGramCospectralFourCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-coordinate realizability of cospectral rational unit Gram matrices.",
        H("The common four-coordinate criterion"),
        Blocks(
            Describe.Lean(DescribeId.Create("four-coordinate-criterion"),
                DeclarationHandle.Create(Module + ".four_coordinate_criterion"),
                H("The exact four-coordinate criterion for both families"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For rational t, either matrix is realizable in four rational "
                        + "coordinates exactly when t is one half or the following two arithmetic "
                        + "conditions hold. One plus four times t must be a rational square, "
                        + "and double the difference between one and twice t must be a sum of two rational squares.")),
                    Paragraph(Text("Away from the two singular endpoints, a square Gram factor "
                        + "forces the common determinant to be a square. Dividing by the square "
                        + "of the repeated eigenvalue gives the first condition. When it holds away from the endpoints, "
                        + "the forms are rationally congruent. After aligning two unit axes, the "
                        + "remaining directions require the second condition. A pair of orthogonal "
                        + "vectors in two coordinates gives the converse. At t equal to minus one "
                        + "quarter both forms require five coordinates. At t equal to one half "
                        + "the paired-edge matrix requires four and the triangle-block matrix two."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/AURICOmega/RationalGramCospectral"))]));
}

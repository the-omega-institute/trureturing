using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class MollifiedDyadicMeanSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic mean square of the Möbius-mollified zeta function",
        H("Dyadic mean square of the Möbius-mollified zeta function"),
        Blocks(Describe.Lean(
            DescribeId.Create("dyadic-mollified-zeta-mean-square"),
            DeclarationHandle.Create("D5/S3/Weil/MollifiedDyadicMeanSquare.dyadic_mollified_zeta_mean_square"),
            H("Uniform power saving on a fixed vertical strip"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a strip with lower edge a strictly between one half and one, put d = a − 1/2 and "
                + "truncate the Möbius polynomial at floor(T^(d/4)). The integral of the squared mollified "
                + "error over T − 1 ≤ |t| ≤ 2T + 1 is bounded uniformly by a constant times T^(1−d²/4). The "
                + "bounds for the finite convolution and the actual zeta truncation control the two "
                + "contributions on this band."))),
            DescribeRole.Theorem))));
}

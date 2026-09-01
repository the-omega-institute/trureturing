using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class OfflineZeroSpectralQuotientDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/OfflineZeroSpectralQuotient."
            + "offline_zero_spectral_quotient_coordinate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection identifies the spectral quotient coordinate of an offline-zero "
            + "parameter by an exact complex polynomial formula.",
        H("Offline-Zero Reflection-Quotient Coordinate"),
        Blocks(Describe.Lean(
            DescribeId.Create("offline-zero-spectral-quotient-coordinate"),
            DeclarationHandle.Create(Declaration),
            H("The reflection quotient gives the exact offline-zero coordinate"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The coordinate lambda(s) is defined as s times its existing "
                        + "functional reflection 1 - s, so the offline-zero parameter "
                        + "rho is shared with the preceding character construction.")),
                Paragraph(Text(
                    "Substituting rho = 1/2 + delta + i gamma gives real part "
                        + "1/4 + gamma squared - delta squared and imaginary part "
                        + "-2 delta gamma.")),
                Paragraph(Text(
                    "The definition is realized concretely at delta = gamma = 1, where "
                        + "rho = 3/2 + i and lambda(rho) = 1/4 - 2i."))),
            DescribeRole.Definition))));
}

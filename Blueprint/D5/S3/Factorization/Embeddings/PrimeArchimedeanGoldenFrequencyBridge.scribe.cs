using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class PrimeArchimedeanGoldenFrequencyBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Embeddings/"
            + "PrimeArchimedeanGoldenFrequencyBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The diagonal p-adic logarithmic defect recovers the Archimedean "
                + "prime scale and its first golden frequency.",
            H("Prime-Archimedean Golden Frequency Bridge"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-finite-place-profile-injective"),
                    DeclarationHandle.Create(
                        Prefix + "golden_finite_place_profile_injective"),
                    H("The diagonal finite-place profile identifies primes"),
                    StatementSource.FromAuthor(
                        Disp(F.Id("goldenFinitePlaceProfile is injective"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "At the target prime the p-adic norm is one over p, "
                                + "so its negative logarithm is log p.")),
                        Paragraph(Text(
                            "At every other prime place the norm is one and the "
                                + "logarithmic defect vanishes."))),
                    DescribeRole.Theorem))));
}

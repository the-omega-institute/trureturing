using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy.Scalar;

internal sealed class LogisticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational logistic enclosures.",
        H("Exact rational logistic enclosures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-logistic-checked-logistic-sound"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic.checked_logistic_sound"),
                H("Scaled positive exponential bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a rational argument in (0,1/2], the smooth transition equals 1/(1+exp(1/t-1/(1-t))). A supplied positive scaling and Taylor depth give rational lower and upper bounds for the exponential, and the decreasing logistic map reverses the endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-logistic-checked-cutoff-logistic-sound"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic.checked_cutoff_logistic_sound"),
                H("Endpoint-safe cutoff bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every rational argument, a successful cutoff check supplies an enclosure of the exact real smooth transition with width at most 2^-m. Arguments outside (0,1) give exact zero or one; reflection handles the upper half, and a far-tail bound handles large logistic differences."))),
                DescribeRole.Theorem)),
        []));
}

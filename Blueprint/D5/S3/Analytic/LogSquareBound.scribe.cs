using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class LogSquareBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A power majorant controls the logarithmic singularity and growth.",
        H("Squared logarithm bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-square-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/LogSquareBound.log_square_bound"),
                H("A global positive-half-line majorant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive real x, log(x)^2 is at most 16*x^(-1/2)+x^2. Below one the reciprocal power controls the logarithmic singularity; above one the square controls its growth."))),
                DescribeRole.Theorem))));
}

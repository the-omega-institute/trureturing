using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExpRatioCM;

internal sealed class ExtractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient extraction from scaled alternating derivatives.",
        H("A vanishing tail isolates the second coefficient"), Blocks(
            Describe.Lean(DescribeId.Create("exp-ratio-cm-extraction-limit"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Extraction.extraction_limit"),
                H("Extraction limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the scaled derivative sequence equals a fixed second coefficient plus a tail converging to zero, then it converges to that coefficient. The exponential-series estimate supplies the equality and the geometric tail in the quotient application."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-negative-extraction"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Extraction.not_completelyMonotone_of_extraction"),
                H("Negative extracted coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete monotonicity makes every scaled alternating derivative nonnegative. A convergent sequence of such values cannot have a negative limit, so a negative extracted coefficient rules out complete monotonicity."))),
                DescribeRole.Theorem))));
}

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
                Blocks(Paragraph(Text("An eventual decomposition of the scaled derivative sequence into its second coefficient and a vanishing tail gives convergence to that coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-quotient-extraction"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Extraction.quotient_extraction_limit"),
                H("Extraction for the consecutive ratios"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every index i, evaluating the signed derivative of order k at k log(7/4) and multiplying by (49/32)^k converges to b(2). The normalized weight is a(n)=(49/32)n(4/7)^n, with a(1)=7/8, a(2)=1, and a(n+3) at most (6/7)(16/21)^n. If B=2^(i+2) and B(16/21)^k is at most one half, absolute convergence and the coefficient bound give an error at most |b(1)|(7/8)^k+2B^3(6/7)^k. Both terms tend to zero. The quotient derivative series applies eventually because k log(7/4) tends to infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-negative-extraction"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Extraction.not_completelyMonotone_of_extraction"),
                H("Negative extracted coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete monotonicity makes every scaled alternating derivative nonnegative. A convergent sequence of such values cannot have a negative limit, so a negative extracted coefficient rules out complete monotonicity."))),
                DescribeRole.Theorem))));
}

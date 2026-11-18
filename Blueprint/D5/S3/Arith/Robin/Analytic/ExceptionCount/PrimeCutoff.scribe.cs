using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.ExceptionCount;

internal sealed class PrimeCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit cutoff with sufficient prime capacity and a strict logarithmic gap.",
        H("Prime cutoff and its capacity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("second-order-count"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.second_order_count"),
                H("Second prime-counting coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized second-order prime-counting error log(x)*(log(x)*primeCount(x)/x-1) tends to one. The same result supplies the uniform central density estimate used for prime exchanges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff"),
                H("Prime cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For t the cutoff is exp(t-1/(2t)), strictly below exp(t) for positive t."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cutoff-top"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff_top"),
                H("Divergence of the cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cutoff tends to positive infinity as t tends to positive infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("enough-primes"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.enough_primes"),
                H("Prime capacity at the cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Eventually the real prime count below exp(t-1/(2t)) is at least exp(t)/t. The second prime-counting coefficient supplies a positive residual limit of one half after normalization."))),
                DescribeRole.Theorem))));
}

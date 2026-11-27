using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord.Effective;

internal sealed class RobinEffectiveChebyshevBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary Chebyshev estimates and the finite prime counts give the strict Robin reserve.",
        H("The Robin prime-band reserve from Chebyshev estimates"),
        Blocks(
            Paragraph(Text("At square cutoff a = sqrt(2z) at least 25000, use the intervals (a, 4a], (4a, 8a] and (8a, 16a]. The Chebyshev estimates give a lower bound of 19/(160a) for the sum of log(p)/p^2 over these primes. Normalizing the actual Robin weights gives a lower bound of 931/16000 for the prime band.")),
            Describe.Lean(
                DescribeId.Create("chebyshev-band-reserve"),
                DeclarationHandle.Create(Prefix + "neededReserve_lt_normalizedPrimeBand_of_sqrt_ge"),
                H("Strict reserve above the Chebyshev cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real z at least 10000 with sqrt(2z) at least 25000, the normalized prime-band surplus strictly exceeds the Robin reserve."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-large-cutoffs"),
                DeclarationHandle.Create(Prefix + "neededReserve_lt_normalizedPrimeBand"),
                H("Strict reserve for all large cutoffs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real z at least 10000, the normalized prime-band surplus strictly exceeds the Robin reserve."))),
                DescribeRole.Theorem)
        )));
}

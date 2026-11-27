using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord.Effective;

internal sealed class RobinEffectiveFiniteBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveFiniteBand.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eight certified prime-count rows give the Robin reserve up to the Chebyshev cutoff.",
        H("Finite prime-count rows for the Robin reserve"),
        Blocks(
            Paragraph(Text("Each row covers square cutoffs from A to 2A and counts primes in (2A, 3A] and (3A, 4A]. The two upper endpoints bound the reciprocal-square weights from below. The row inequalities give a common lower bound of 2/25 for the normalized prime band.")),
            Describe.Lean(
                DescribeId.Create("finite-band-reserve"),
                DeclarationHandle.Create(Prefix + "neededReserve_lt_normalizedPrimeBand_of_sqrt_le"),
                H("Strict reserve through the finite cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real z at least 10000 with sqrt(2z) at most 25000, the normalized prime-band surplus strictly exceeds the Robin reserve."))),
                DescribeRole.Theorem)
        )));
}

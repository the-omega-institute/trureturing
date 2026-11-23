using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SectorChannels;

internal sealed class MaxentRankPhaseRoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact rank-count rounding minimum controls the scalar residual packing loss with an optimal factor.",
        H("Sharp rounding at a prescribed residual rank phase"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sharp-rank-phase-rounding"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/SectorChannels/MaxentRankPhaseRounding.phase_rounding"),
                H("Sharp comparison of the rank-count partition and greedy cap packing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write the rank-scaled weights as integer parts and squared residual caps. If the residual sum is the integer K, rounding up the K largest residuals attains the literal minimum label L1 error among all nonnegative integer counts of the required rank.")),
                    Paragraph(Text("The greedy scalar packing error is at most that minimum and at least (K+1)/(2K+1) times it. An additional lower bound becomes asymptotically exact near integer phases. For each positive K an explicit sorted K+3-label profile attains the factor at nonzero distance.")),
                    Paragraph(Text("This is the scalar maximally entangled matched-label benchmark. It does not assert the physical channel converse, arbitrary Schmidt spectra, or a solution of coherent RT."))),
                DescribeRole.Theorem))));
}

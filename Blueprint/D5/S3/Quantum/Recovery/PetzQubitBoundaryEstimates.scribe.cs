using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzQubitBoundaryEstimatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One correlated pair among three logistic modes improves the endpoint evaluation bound.",
        H("Logistic endpoint evaluation with a correlated pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petzqubitboundaryestimates-close-pair-weighted-evaluation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzQubitBoundaryEstimates.close_pair_weighted_evaluation"),
                H("Three-mode evaluation bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let three real frequencies carry arbitrary complex coefficients. If the logistic correlation between the first slot and either other slot is at least one fifth, the logistic weighted squared amplitude is integrable and its integral multiplied by 8/3 bounds the squared endpoint amplitude. The frequency values may coincide.")),
                    Paragraph(Text("The square root of the correlation Gram supplies three unit vectors. The trace represents evaluation on their rank-one projectors. The Hermitian part of an outer product constructed from an orthogonal complement is perpendicular to all three projectors. Subtracting its component from the identity gives a trace representer with squared Hilbert–Schmidt norm at most 8/3."))),
                DescribeRole.Theorem))));
}

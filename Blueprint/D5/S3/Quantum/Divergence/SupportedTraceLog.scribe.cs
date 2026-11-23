using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SupportedTraceLogDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite joint convexity for supported PSD trace-log pairings.",
        H("Supported trace-log joint convexity"),
        Blocks(Describe.Lean(
            DescribeId.Create("supported-trace-log-joint-convexity"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/SupportedTraceLog.traceLog_jointConvex"),
            H("Joint convexity for arbitrary finite masses"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonaccimixedqubit")),
            Blocks(
                Paragraph(Text(
                    "Take finite matrix and family index types, nonnegative common weights wᵢ, "
                    + "and positive semidefinite pairs Sᵢ and Tᵢ with ker Tᵢ contained in ker Sᵢ. "
                    + "For D(S,T) = Re Tr[S(log S − log T)], the pairing of the two weighted sums "
                    + "is bounded by the weighted sum of the individual pairings. The spectral "
                    + "logarithm takes the value zero at eigenvalue zero. Both sides vanish when "
                    + "either index type is empty.")),
                Paragraph(Text(
                    "When the numerator sum is nonzero, both aggregate traces are positive. Normalize each "
                    + "family by its own aggregate trace and apply the flag-erasure log-sum inequality. "
                    + "The support projections absorb the logarithmic scale corrections, and trace "
                    + "additivity cancels the common correction. A zero numerator sum forces every weighted "
                    + "numerator block to vanish. The same-scale identity includes vanishing weights."))),
            DescribeRole.Theorem))));
}

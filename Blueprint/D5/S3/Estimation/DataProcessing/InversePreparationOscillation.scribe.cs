using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class InversePreparationOscillationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/DataProcessing/InversePreparationOscillation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite inverse preparation matrix controls trace identifiability by its column oscillation.",
        H("Inverse Preparation and Signed Identifiability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-mass-oscillation"),
                DeclarationHandle.Create(Prefix + "zero_sum_pairing_bound"),
                H("Zero-mass pairing"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On any nonempty finite type, a real signed row with total mass zero pairs "
                    + "with an observable of oscillation at most L with absolute value at most "
                    + "L/2 times its total absolute mass. Subtract the midpoint of the interval "
                    + "from a minimum coefficient to that coefficient plus L. The zero-mass "
                    + "condition cancels the subtraction, and the triangle inequality gives the bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-preparation-trace"),
                DeclarationHandle.Create(Prefix + "inverse_preparation_trace_bound"),
                H("An inverse-column estimate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "M, N and P are real square matrices on any nonempty finite type. "
                        + "M and P preserve the all-ones column, N M is the identity, and every "
                        + "column of N has oscillation at most L. P need not be nonnegative. "
                        + "The absolute difference between trace(P) and one is at most L/2 "
                        + "times the sum of absolute entries of M P minus the uniform matrix.")),
                    Paragraph(Text(
                        "Write Z=M P-Pi. Every row of Z has zero mass. The inverse preserves "
                        + "the all-ones vector and hence N Pi=Pi, so N Z=P-Pi. Taking traces "
                        + "expresses trace(P)-1 as the sum of row pairings of Z with the "
                        + "columns of N. The preceding oscillation estimate applies to each row.")),
                    Paragraph(Text(
                        "The quantum consumer uses P as Born probabilities of complete conditional "
                        + "density matrices. It separately proves domination of the measured "
                        + "defect by the full input-Choi trace distance; this scalar theorem "
                        + "does not identify those two defects or assume that a quantum recovery is diagonal."))),
                DescribeRole.Theorem))));
}

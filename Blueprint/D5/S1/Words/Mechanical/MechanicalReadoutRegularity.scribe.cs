using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalReadoutRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalReadoutRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cumulative integer hits determine precisely where the completed numerical readout is continuous at a fixed phase.",
        H("Mechanical Readout Regularity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-geometric-readout-continuity-jump"),
                DeclarationHandle.Create(Prefix + "geometric_readout_continuity_and_jump"),
                H("Exact continuity locus and a positive jump certificate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every ratio strictly between zero and one, every slope strictly between zero and one, and any fixed real phase, the actual completed geometric readout is continuous in the explicit epsilon-delta sense exactly when no x+k*alpha with positive integer k is an integer. If time k hits an integer, its value exceeds the value at every smaller admissible slope by at least (1-r)^2*r^(k-1). The proof constructs positive finite-prefix stability margins, combines equal actual prefixes with the already proved one-sided geometric tails, and derives a noncancelling lower jump from the actual cumulative-floor Abel identity. A smaller parameter witnessing failure of continuity is constructed inside any proposed neighborhood. Ratio zero is deliberately excluded because it discards all later bits. The arbitrary-phase classification does not assume a staircase representation or a jump formula. Related floor-series and Sturmian staircase literature is credited in the theory; exact total jump masses and the atomic-measure representation there are ordinary mathematical consequences, not additional declarations of this source."))),
                DescribeRole.Theorem))));
}

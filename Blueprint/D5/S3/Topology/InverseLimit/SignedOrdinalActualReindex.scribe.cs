using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalActualReindexDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalActualReindex.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual selected events at one reindexed label", H("Actual support and measure fidelity"), Blocks(
            Describe.Lean(DescribeId.Create("actual-delayed-support"),
                DeclarationHandle.Create(Owner + "actualDelayedSupport"), H("The actual omega zero delayed support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The original omega birth support at zero is pulled back along the literal finalPrefix map from the given row to omega. Surjectivity follows from the same Prefix onto law; no support supplier is assumed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-birth"),
                DeclarationHandle.Create(Owner + "actualBirth"), H("Reindexing the identical whole birth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The input is exactly wholeBirth of the original fixed run on its finalPrefix carrier. The generic reindexBirth changes U and nu indices while retaining V and B. Delayed U uses the actual omega zero pullback, whereas nu uses measureIndex of this same wholeBirth."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eta"),
                DeclarationHandle.Create(Owner + "eta"), H("One label for every actual selected event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The reservation is checked against its actual local delayed semantics. Valid ordinary and delayed branches use the generic eventIndex on their own original whole birth. Every rejected or invalid task instead uses eta zero directly, avoiding hole coloring of fallback events."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("event-row-le"),
                DeclarationHandle.Create(Owner + "eventRow_le"), H("The actual row is already born"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The packaged row is at most the event stage. The selected target equality pins it to the treatment row of the already selected event."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eta-le"),
                DeclarationHandle.Create(Owner + "eta_le"), H("The actual common label is eligible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original event, eta is at most its stage. Valid tag occurrences use the generic bound; rejected events use zero directly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("selected-target"),
                DeclarationHandle.Create(Owner + "selected_target"), H("The actual selected target is fixed"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Both the packaged row and its decoded original measure target equal the treatment of the same selected Q and Result. The construction does not select a replacement treatment or Result."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("selected-measure"),
                DeclarationHandle.Create(Owner + "selected_measure"), H("All natural indices read the same selected measure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every stage and every natural index, the reindexed birth measure at eta is heterogeneously equal to the actual selected Q measure at its actual treatment row and label. Old rows use original whole birth coherence. Self row events use the same newborn Q. This supplies the exact target readback consumed by the same selected Result quantitative_g, for either ordinary or delayed selection, without rebuilding G or its signed endpoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-cofinal"),
                DeclarationHandle.Create(Owner + "actual_cofinal"), H("Every new label has cofinal actual events"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every born row, every new Label and every bound, there is a later actual event on that row with eta equal to that Label. The witness is strictly after the row. Generic tag occurrences are converted to actual ordinary execution or, using stable_local and intrinsic_cast, actual eligible delayed execution. Holes and zero use only valid ordinary zero reservations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("universal-launch"),
                DeclarationHandle.Create(Owner + "universal_launch"), H("Every actual newborn support launches at the same eta"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every actual event and every natural index, newborn V is exactly the inverse image of the reindexed U at its actual row and the same eta used by selected_measure. Self row events use Prepared.launch_eq with the same Q.U and Q.V; old ordinary rows use original birth coherence. Delayed launches use omega zero and literal composition of restrictions. Invalid and rejected tasks retain the original omega zero fallback. This statement covers every stage, including self row events, rather than only cofinal witnesses."))), DescribeRole.Theorem))));
}

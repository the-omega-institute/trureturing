using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalSupportAveragedCutDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportAveragedCut.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original full EJM supports force a cut on all thirty-two factors.",
        H("Averaging a real event conflict over the original source actions"),
        Blocks(
            Paragraph(Text("Inside means that the complete ordered local event belongs to the 132-row triangle support or the 168-row singleton support. Outside is its integer zero-or-one complement. These supports include all four outcomes, all twelve local coordinate actions and every simultaneous outcome relabeling. The theorem quantifies over every actual twenty-coordinate event.")),
            Describe.Lean(DescribeId.Create("averaged-outside-cut"),
                DeclarationHandle.Create(Prefix + "averaged_outside_cut"),
                H("Twice the triangle outside count plus the singleton outside count is at least sixteen"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each of the 192 original source actions, simultaneous inside membership would transport to the three-factor conflict at triangle indices 2 and 3 and singleton index 8. At least one transported factor is therefore outside. The kernel checks closure on every actual support row and counts all source-action fibers: each seed triangle and the singleton visit every original index twelve times. Summing gives twenty-four copies of the triangle outside count and twelve copies of the singleton outside count, at least 192. Dividing by twelve gives the stated cut. This is an exact support constraint; the original positive score margin and a strict quantum noise region still require their own certificate."))),
                DescribeRole.Theorem))));
}

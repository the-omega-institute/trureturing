using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PrincipalPlaquetteGaugeBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Checkerboard gauge and coherent error budgets for two contracting blocks.",
        H("Gauge budgets for two contracting plaquette blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rt-signed-coherent-two-block-quarter"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalPlaquetteGaugeBudget."
                    + "quarter_plaquette_of_signed_coherent"),
                H("Coherent block tests exclude a closed quarter sublevel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The checkerboard gauge projects the entry errors onto four real lines. "
                    + "Separate flat and alternating complex sums control their combined "
                    + "linear budget, while the row probes provide the sum-of-squares budget. "
                    + "The contraction bounds then exclude a quarter on the given phase sector. "
                    + "The importing native module supplies all three probes from channels."))),
                DescribeRole.Theorem))));
}

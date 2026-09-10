using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class ArchiveCarrierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite archived events retain their exact attributes and causal order beside a separate current region.",
        H("Finite Spacetime Archives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-causal-archive"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/ArchiveCarrier.Archive"),
                H("The exact archived event domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite archive contains HF event names. Time, finite-dimensional integer position, "
                    + "sign and source tree are functions on precisely those events. A strict transitive causal "
                    + "relation must increase time. The dimension is arbitrary and includes three."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rich-context-selection"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/ArchiveCarrier.Rich"),
                H("A context and its selection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A context carries an archive and a finite current region inside it; a selection is any "
                    + "subset of that region. Empty archives, regions and selections are permitted. "
                    + "Archive embeddings preserve attributes and reflect causal order without constraining "
                    + "current regions. Context embeddings and generated operations belong to later work."))),
                DescribeRole.Definition))));
}

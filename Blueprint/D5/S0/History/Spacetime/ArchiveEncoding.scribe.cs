using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class ArchiveEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite contexts and rich selections correspond exactly to structurally legal HF records.",
        H("Context and Selection Representation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("context-code-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/ArchiveEncoding.context_code_equiv"),
                H("An exact context representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The independent context grammar specifies an event set, legal attribute and causal graphs, "
                    + "and a current region contained in the event set. Graph reconstruction restores the "
                    + "complete archive. Both round trips and equality reflection hold for the actual context."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rich-selection-code-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/ArchiveEncoding.rich_code_equiv"),
                H("Selections preserve both containment guards"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A rich record appends a selected HF set contained in the current region. Reconstruction "
                    + "keeps the archive, current region and selection distinct. These predicates are specified "
                    + "through tuple structure, graph legality and membership, independently of encoder ranges.")),
                    Paragraph(Text(
                        "This batch proves finite representation in Lean. Infinite rational Cauchy sequences, "
                        + "arithmetic quotients and a first-order definition-elimination or conservativity "
                        + "bridge are outside these declarations."))),
                DescribeRole.Definition))));
}

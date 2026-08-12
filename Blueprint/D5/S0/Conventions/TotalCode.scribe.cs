using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class TotalCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Total-code-preserving transformations cannot hide object changes.",
            H("No Invisible Register"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("no-hidden-register"),
                    DeclarationHandle.Create("D5/S0/Conventions/TotalCode.no_hidden_register"),
                    H("Preserving the total code preserves the object"),
                    StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                                            "The semantic kernel-identity criterion is represented here by "
                                            + "Lean structure equality, not claimed as a proof of an ontological "
                                            + "identity criterion. Extensionality proves both the preservation "
                                            + "clause and its componentwise dual. This is the C3a identity pillar "
                                            + "announced for use in 23.4."))),
                    DescribeRole.Theorem
                ))));
}

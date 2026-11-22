using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringBPowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grouping by phase",
        H("Grouping by phase"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bpow"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringBPow.normSq_pow_T_fiber"),
                H("Grouping by phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("A positive integer power of the squared norm of a displacement sum expands over phase fibers, weighted by their cardinalities."))),
                DescribeRole.Theorem)
        )));
}

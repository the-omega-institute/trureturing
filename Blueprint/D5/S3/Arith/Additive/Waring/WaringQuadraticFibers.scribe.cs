using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringQuadraticFibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero quadratic phase fibers",
        H("Nonzero quadratic phase fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadraticfibers"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringQuadraticFibers.qQ_le_sigma"),
                H("Nonzero quadratic phase fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("For a nonzero quadratic coefficient and target, the count of quadratic differences in a box obeys a bound in terms of the target's reciprocal-divisor statistic."))),
                DescribeRole.Theorem)
        )));
}

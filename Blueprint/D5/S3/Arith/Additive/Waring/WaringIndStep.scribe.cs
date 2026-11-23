using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringIndStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounding a phase fiber by an integral",
        H("Bounding a phase fiber by an integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("indstep"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringIndStep.BCount_le_integral"),
                H("Bounding a phase fiber by an integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("For a positive power s, the cardinality of any phase fiber is bounded by the unit-interval integral of the displacement norm to the power 2s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bpow"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringIndStep.normSq_pow_T_fiber"),
                H("Grouping by phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("A positive integer power of the squared norm of a displacement sum expands over phase fibers, weighted by their cardinalities."))),
                DescribeRole.Theorem)
        )));
}

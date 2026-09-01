using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class DegenerateModeHiddenFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact spectral degeneracy leaves a nonzero antisymmetric direction invisible at every time.",
        H("Degenerate-Mode Hidden Fiber"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-time-trace-not-injective"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber.all_time_trace_not_injective"),
                H("Exact degeneracy defeats the full scalar time trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two equal modal multipliers make the antisymmetric amplitude invisible for every natural observation time, so even the complete scalar time trace is noninjective.")),
                    Paragraph(Text(
                        "This is a constructive hidden-fiber certificate. It isolates spectral degeneracy as an obstruction that time stacking alone cannot remove."))),
                DescribeRole.Theorem))));
}

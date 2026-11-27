using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class CompactMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact Mean", H("Compact Mean"),
        Blocks(
            Paragraph(Text("Smooth and unitary representations; averaging projector over a compact subgroup.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/CompactMean.compactMean_adjoint"),
                H("compactMean_adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For ρ smooth with invariant scalar product B, the mean of ρ over a compact subgroup H (compactMean) is self-adjoint for B.")))))));
}

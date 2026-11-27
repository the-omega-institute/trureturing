using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Trace;

internal sealed class GoodIdempotentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Good Idempotent", H("Good Idempotent"),
        Blocks(
            Paragraph(Text("Spaces Y_j, W_j, ideles, levels, rows, auxiliary pairs on the proof's data. Signs and weight gaps of the data; cusp kernel and finite-dimensionality instances.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Trace/GoodIdempotent.isCuspKernel_paramW"),
                H("isCuspKernel_paramW"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If the doubled parameter Data.paramW v has gap h for the signs s at every infinite place v, then the product function typeKernel on G_∞ for this parameter and s is a cusp kernel (IsCuspKernel) of order h₂.")))))));
}

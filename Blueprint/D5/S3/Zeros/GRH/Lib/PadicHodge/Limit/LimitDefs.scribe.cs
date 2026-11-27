using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Limit;

internal sealed class LimitDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Limit Defs", H("Limit Defs"),
        Blocks(
            Paragraph(Text("A_max periods embed in B_max periods; crystalline with weights in [0,h]; bundled representations.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Limit/LimitDefs.applyVec"),
                H("applyVec"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a Z_p-linear map u from T to square matrices over Q̄_p and a vector v, the Z_p-linear map sending x to u(x)v.")))))));
}

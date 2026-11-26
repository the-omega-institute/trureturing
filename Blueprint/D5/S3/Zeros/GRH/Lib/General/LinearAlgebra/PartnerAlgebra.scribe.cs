using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class PartnerAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partner Algebra", H("Partner Algebra"),
        Blocks(
            Paragraph(Text("Primitive matrices extend to bases; partner data and their laws under integral matrices.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartnerAlgebra.left_mul"),
                H("left_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If Φ, Ψ are partners for χ, then χ(det g)·Φ(gx) = Φ(x) for all g in GL_a(O) and all a × n matrices x.")))))));
}

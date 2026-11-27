using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class CuspidalAtScalarsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cuspidal At Scalars", H("Cuspidal At Scalars"),
        Blocks(
            Paragraph(Text("Values of Steinberg and cuspidal class functions at field elements, by generating series.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalAtScalars.moebius_and_greenCuspidal_lsmul"),
                H("moebius_and_greenCuspidal_lsmul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let F = k[z] have Q elements, g be multiplication by z on an F-space V of dimension m, and N = ∏_{i<m}(X − Q^i). Then 𝟙⁻¹(g) = N(0), and C_η(g) (Hall.greenCuspidal) is −N'(1) times the sum of η over the roots in K of the minimal polynomial of z.")))))));
}

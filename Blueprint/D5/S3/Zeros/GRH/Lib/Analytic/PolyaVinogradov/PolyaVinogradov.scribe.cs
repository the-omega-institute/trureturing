using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Analytic.PolyaVinogradov;

internal sealed class PolyaVinogradovDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polya Vinogradov", H("Polya Vinogradov"),
        Blocks(
            Paragraph(Text("Pólya–Vinogradov inequality for non-principal characters; modulus of primitive Gauss sums.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Analytic/PolyaVinogradov/PolyaVinogradov.polya_vinogradov"),
                H("polya_vinogradov"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Pólya–Vinogradov inequality for a non-principal character χ mod q: |∑_{1 ≤ v ≤ X} χ(v)| ≤ 2√q (1 + log q) for all X.")))))));
}

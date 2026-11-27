using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class DataProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Data Product", H("Data Product"),
        Blocks(
            Paragraph(Text("Standard spaces, Taylor series of theta functions, jets along Schur matrix entries. Weil representation of an orthogonal sum restricts to the tensor product on block elements.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/DataProduct.omega_boxProd"),
                H("omega_boxProd"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If the matrix of g is block diagonal with blocks g₁, g₂ for a sign-compatible splitting of the coordinates, then ω(g)(f₁ ⊠ f₂) = ω(g₁)f₁ ⊠ ω(g₂)f₂.")))))));
}

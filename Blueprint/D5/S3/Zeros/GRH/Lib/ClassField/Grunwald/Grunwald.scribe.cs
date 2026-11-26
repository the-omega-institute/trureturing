using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Grunwald;

internal sealed class GrunwaldDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grunwald", H("Grunwald"),
        Blocks(
            Paragraph(Text("Grunwald's theorem in prime exponent over a totally complex field; symmetrised characters.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Grunwald/Grunwald.grunwald"),
                H("grunwald"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Grunwald in prime exponent: for E totally complex, S finite, ψ a ℚ/ℤ-valued character of the finite ideles with open kernel, pψ = 0, some Galois character χ, pχ = 0, has χ∘Art = ψ on E_u^× for u ∈ S and on local units where N u is not prime.")))))));
}

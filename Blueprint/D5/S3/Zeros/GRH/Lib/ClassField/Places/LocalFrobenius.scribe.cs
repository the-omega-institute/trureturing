using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class LocalFrobeniusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Frobenius", H("Local Frobenius"),
        Blocks(
            Paragraph(Text("Uniformisers and the normalised rational valuation on the algebraic closure of a local field. Frobenius exists and, with inertia, topologically generates a local Galois group.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalFrobenius.frobenius_spec"),
                H("frobenius_spec"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Γ = Gal(Ω/K) be the absolute Galois group of a henselian local field, with valuation ring A of Ω. An arithmetic Frobenius exists; for any such φ the products φ^n·i (n ≥ 0, i in inertia) are dense in Γ; A is integral over A ∩ K.")))))));
}

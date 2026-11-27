using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology;

internal sealed class CupProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cup Product", H("Cup Product"),
        Blocks(
            Paragraph(Text("Cup product on cocycles, Cartier dual module, annihilators and their orders.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/CupProduct.cupProduct_flip"),
                H("cupProduct_flip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The cup product of 1-cocycles is anticommutative: y ∪ x for the flipped pairing equals −(x ∪ y) in H²(W).")))))));
}

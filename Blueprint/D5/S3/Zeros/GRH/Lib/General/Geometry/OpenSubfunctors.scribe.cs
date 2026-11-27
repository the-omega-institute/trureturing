using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class OpenSubfunctorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Open Subfunctors", H("Open Subfunctors"),
        Blocks(
            Paragraph(Text("Functor-of-points basics: open and separated subfunctors, étale charts, atlases, complements of points.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/OpenSubfunctors.isLocallyEverything_of_open_cover"),
                H("isLocallyEverything_of_open_cover"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Θ: C → k-algebras and T ⊂ X∘Θ be such that each field point of X lies in an open O with O∘Θ ⊂ T. Then for y in X(Θc) and m maximal in Θc, some f ∉ m has y in T wherever f becomes a unit.")))))));
}

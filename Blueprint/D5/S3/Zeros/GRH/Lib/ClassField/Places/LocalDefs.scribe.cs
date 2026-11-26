using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class LocalDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Defs", H("Local Defs"),
        Blocks(
            Paragraph(Text("Definitions: uniformiser, order, cyclotomic character, local invariant, local Artin map, chosen place.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalDefs.placeOver"),
                H("placeOver"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a finite prime v of the number field K, a chosen valuation subring of Ω lying over v.")))))));
}

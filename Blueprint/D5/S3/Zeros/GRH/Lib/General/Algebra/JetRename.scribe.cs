using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class JetRenameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jet Rename", H("Jet Rename"),
        Blocks(
            Paragraph(Text("The Fischer pairing is preserved by an injective renaming of the variables.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/JetRename.jet_rename"),
                H("jet_rename"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The jet pairing P(∂)F(0) of a polynomial P with a power series F over a commutative ring is unchanged when both are renamed along an injective map of variables.")))))));
}

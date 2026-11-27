using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class LocalExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Extension", H("Local Extension"),
        Blocks(
            Paragraph(Text("Finite extension of a local field is local, with ef equal to the degree.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalExtension.exists_ordRat_eq_intCast"),
                H("exists_ordRat_eq_intCast"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a local field k, every x in Ω^× fixed by the inertia group has integral order, for the order normalised on k.")))))));
}

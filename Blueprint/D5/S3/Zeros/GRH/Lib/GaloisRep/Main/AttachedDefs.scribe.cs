using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Main;

internal sealed class AttachedDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attached Defs", H("Attached Defs"),
        Blocks(
            Paragraph(Text("Definition of attached representation and statement of the main theorem.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Main/AttachedDefs.SphericalCompat"),
                H("SphericalCompat"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Every eigenform f on the standard space has an attached r; if K_w fixes f, every attached r is unramified or crystalline at w, with the jumps of κ in rank N, and ιQ kills geometric Frobenius when f has Hecke polynomial Q at w.")))))));
}

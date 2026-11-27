using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class CuspidalSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cuspidal Support", H("Cuspidal Support"),
        Blocks(
            Paragraph(Text("Cuspidal class functions vanish unless the characteristic polynomial is a prime power.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/CuspidalSupport.exists_charpoly_eq_pow"),
                H("exists_charpoly_eq_pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Over a finite field k, if F is cuspidal (Hall.IsCuspidal) and does not vanish at the class of an endomorphism g, then the characteristic polynomial of g is a power of an irreducible polynomial.")))))));
}

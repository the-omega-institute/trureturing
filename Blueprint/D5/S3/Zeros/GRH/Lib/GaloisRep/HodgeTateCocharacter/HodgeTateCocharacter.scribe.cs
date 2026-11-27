using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.HodgeTateCocharacter;

internal sealed class HodgeTateCocharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Tate Cocharacter", H("Hodge Tate Cocharacter"),
        Blocks(
            Paragraph(Text("Hodge–Tate cocharacter lies in the Zariski closure of the image near the identity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/HodgeTateCocharacter/HodgeTateCocharacter.aeval_cocharacter_eq_zero"),
                H("aeval_cocharacter_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If a polynomial F over C_p vanishes at (χ(g)^(−κ_i)·g x_i)_i for all g in G_p near 1, then F vanishes at (T^(κ_i)·x_i)_i in the ring of Laurent polynomials C_p[T, T⁻¹].")))))));
}

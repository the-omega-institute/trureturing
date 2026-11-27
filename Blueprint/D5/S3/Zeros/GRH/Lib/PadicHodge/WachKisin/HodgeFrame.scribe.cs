using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class HodgeFrameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Frame", H("Hodge Frame"),
        Blocks(
            Paragraph(Text("Hodge–Tate maps of distinct weights are independent; jumps read from a basis of them. Breuil–Kisin ring W[[z]] inside A_inf: definition, Frobenius, coordinates, Weierstrass division. Hodge frame: invariant B_dR basis adapted to filtration, giving de Rham implies Hodge–Tate.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/HodgeFrame.exists_hodge_frame"),
                H("exists_hodge_frame"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Hodge frame: let j have open image, F be coarser than the near-1 filter, U in GL(B_dR) with N(g)·gU = U for F-almost all g, N(g) over Q̄_p. Then UY = W·diag(t^k_i), again invariant, with W in GL(B_dR^+) and Y in SL(Z̄_p) fixed for F-almost all g.")))))));
}

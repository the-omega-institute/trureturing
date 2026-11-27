using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class StableSpacesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable Spaces", H("Stable Spaces"),
        Blocks(
            Paragraph(Text("A stable space containing a standard datum contains all partner data.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/StableSpaces.partner_mem_of_unimodular_vanishing"),
                H("partner_mem_of_unimodular_vanishing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P be GL_n(F)-stable and M contain all S_z(y) = S₀(y + LzK'y), S₀ the standard datum of K', with L, K' blocks of an IntegralFrame. If P contains each element of M killed by all Λ with Λ(S_z) = ψ(tr Tz)Λ(S₀), and Λ(S₀) = 0 if T is unimodular, then P contains every locally constant function having a partner.")))))));
}

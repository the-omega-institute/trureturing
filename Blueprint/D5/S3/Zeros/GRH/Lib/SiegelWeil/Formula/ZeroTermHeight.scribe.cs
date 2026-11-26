using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.Formula;

internal sealed class ZeroTermHeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero Term Height", H("Zero Term Height"),
        Blocks(
            Paragraph(Text("Lagrangians, their zero terms, torus action and integrable bound for the theta integral. Height bounds for zero terms under the parabolic and along the torus.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/ZeroTermHeight.exists_zeroTerm_normalisedTorus_le"),
                H("exists_zeroTerm_normalisedTorus_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("P, P′ split S completely with frames k, k′; Zk′=1; K compact. For some R: if g∈K, x,u∈ℕ^p, Zgk·diag(2^x) = Zgk·diag(2^u) (2 archimedean), the P′-value at 0 of ω(g,1)(normalisedTorus T P x f) has modulus ≤ R‖f‖·2^{d(∑u−∑x)rk T}, d the number of infinite places.")))))));
}

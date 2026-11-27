using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Endgame;

internal sealed class PrimeErrorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime Error", H("Prime Error"),
        Blocks(
            Paragraph(Text("Weighted non-split prime sums; their Mellin transform has poles at zeros of L-functions.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Endgame/PrimeError.isPolar_primeError"),
                H("isPolar_primeError"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For d ≡ 7 mod 8 prime to M, v ↦ R_M(e^v) is polar (IsPolar) with residue at s equal to ∑_ξ (ord_s L̃(ξ) − ord_s L̃(ξ(·/d))) / (φ(M) s(1 − s)), ξ over the characters mod M, L̃ = entireL.")))))));
}

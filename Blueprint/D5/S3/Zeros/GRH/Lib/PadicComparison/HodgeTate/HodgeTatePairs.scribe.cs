using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate;

internal sealed class HodgeTatePairsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Tate Pairs", H("Hodge Tate Pairs"),
        Blocks(
            Paragraph(Text("Tests with affine spaces of lifts modulo ξ², contraction class and its powers.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTatePairs.wedgePairing"),
                H("wedgePairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The natural map Λ ⊗ Λ → Λ given by the wedge product in ⋀_T M.")))))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class RealPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Pair", H("Real Pair"),
        Blocks(
            Paragraph(Text("Matched real data giving the exchange identity at the top of the tower.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/RealPair.exists_stdExchange_top"),
                H("exists_stdExchange_top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For adapted splittings of X over W₁ (even rank) and of W₁ along a line, and rapid v, v₁, some x, x' satisfy StdExchange for (X, V' ⊕ W₁, V') with factor equalRankThetaRatio of v₁, and x' has slice v at 0 for the opposite splitting.")))))));
}

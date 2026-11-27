using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class PairRealDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair Real", H("Pair Real"),
        Blocks(
            Paragraph(Text("Real dual pair on Fock space; maximal compact subgroups act by substitution and character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairReal.pairWeil_integrated"),
                H("pairWeil_integrated"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If a has weight γ and b has weight γ' (with tame parts ψ, ψ'), then for real points x, y, ω_{a,b}(x,y)(v⊗f) = (Ω(x,y)v)⊗f, where Ω is the real Weil representation of the pair for the weights γ, γ'.")))))));
}

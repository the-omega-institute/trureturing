using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class CrystallineRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Rank", H("Crystalline Rank"),
        Blocks(
            Paragraph(Text("the rank of the crystalline cocycles Z_f(L) is rk L plus the number of negative Hodge–Tate weights; so a power of ℓ that maps Z_f(L) into a submodule bounds the quotient in length.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/CrystallineRank.normLength_defect_le"),
                H("normLength_defect_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let L be potentially crystalline, ℓ^k Z_f(L) ⊆ S for a submodule S, and 2k·rank L ≤ y. Then Z_f(L) modulo Z_f(L) ∩ S has normalised length at most y times the index of j(Γ) in the absolute Galois group of ℚ_ℓ.")))))));
}

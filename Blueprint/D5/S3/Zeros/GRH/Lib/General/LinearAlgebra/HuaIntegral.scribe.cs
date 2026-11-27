using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class HuaIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hua Integral", H("Hua Integral"),
        Blocks(
            Paragraph(Text("Real Heisenberg bicharacter, Gaussian vacuum, creation and annihilation operators, Lie algebra action. Euclidean volume normalised by Gaussian integral one; products and powers. Principal minors: norm bound, multiplicativity, Jacobi's complementary minor theorem. Upper bound for Hua's determinant integral; beta-type integrals.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/HuaIntegral.hua_integral_le"),
                H("hua_integral_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Hua's integral bound: for M positive definite and S invertible of size k, c ≥ 0, r ≥ k, y_i = x_iS + a_i, the integral of c|det(M + Σ_{i∈s} y_iᴴy_i)|^{−(|s|+r)} over rows x_i ∈ ℂ^k, i ∈ s, is at most c(π^k/(k!|det S|²))^{|s|}|det M|^{−r}.")))))));
}

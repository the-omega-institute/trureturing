using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicSignedTransferDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicSignedTransfer.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact signed transfer of Wu’s normalized cubic deficit with both physical squares retained.",
        H("Signed cubic transfer to a raised middle level"),
        Blocks(
            Paragraph(Text("Use the two-mode cubic normalization of Wu v1, Remark 3.15, equations (3.54)–(3.55), with r = exp(β/3). For r ≥ 1 and 0 ≤ m ≤ n ≤ q ≤ 1, use the same complex frame U with UᴴU = I and UUᴴ = I for (m, n, n, 1) and (m, n, q, 1). The jump weight Wᵢⱼ runs from source column j to target row i, with columns numbered from zero.")),
            Entry("signed-increment", "signed_increment", "Exact signed increment",
                "Put T(z) = m³ + n³ + z³ + 1 and let R₂ be the occupation imbalance of column 2. The scalar change I is (h + bias·R₂)(q³ − n³) + α[T(q) log(T(q)/4) − T(n) log(T(n)/4) − q³ log(q³) + n³ log(n³)], with the Gibbs coefficients at r and 0 log 0 = 0. For g(v,w) = c(v − w)²(v + w) + e(v − w)³, the gain P sums the four weighted increases in g from raising column 2 against columns 0 and 1, in both directions. The deficit changes by I + P − d₊W₃₂ − d₋W₂₃, where d₊ = g(1,n) − g(1,q) and d₋ = g(n,1) − g(q,1). P, d₊ and d₋ are nonnegative. In the occupation frame at (r,m,n,q) = (6/5,16/25,4/5,81/100), W₃₂ = 0 and W₂₃ = 1, and the measured loss is 983727/136400000."),
            Entry("raised-lower-bound", "raised_lower_bound", "Transferred lower bound with both physical squares",
                "Let L be γr·holder21 + γr²·holder12 + frameRemainder at the repeated-middle spectrum, with γ = 9/[4(1 + r³)]. WuOneModeCubic supplies the one-mode premise of this bound at every r ≥ 1. For u = U.col 3 and v = U.col 2 put A = (d₊ + d₋)/2 and ρ = (d₊ − d₋)/(d₊ + d₋). The new deficit is at least L + I + P − A(1 + ρRᵤ)(1 − ρRᵥ) + A(2 − ρ²)|η|²/4 + A|σ + ρτ|². The weighted identity in WuPhysicalHighHigh gives this exact rewrite of the subtracted loss using the imbalances and the parity and conjugate-twist pairings of u and v. The last three terms vanish when A = 0 under Lean’s real division convention."),
            Entry("source-deficit-rectangle", "source_deficit_rectangle", "Strict deficit bound on the raised-middle rectangle",
                "For every frame U with UᴴU = I and UUᴴ = I, the normalized deficit at (m, n, q, 1) exceeds 1/200 whenever 6/5 ≤ r ≤ 5/4, 23/50 ≤ m ≤ 1/2, 9/10 ≤ n ≤ 23/25, and n ≤ q ≤ n + 1/40. The proof transfers the repeated-middle estimate and uses W₃₂ + W₂₃ ≤ 1 to bound the total loss by (189/400)(q − n)."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}

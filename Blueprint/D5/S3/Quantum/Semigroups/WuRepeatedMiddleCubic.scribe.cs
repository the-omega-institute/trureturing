using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuRepeatedMiddleCubicDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuRepeatedMiddleCubic.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact decomposition and a conditional lower bound for the signed two-mode cubic spectral deficit on (m, n, n, 1).",
        H("Cubic deficit with a repeated middle level"),
        Blocks(
            Paragraph(Text("In the setting of Wu v1, Remark 3.15, equations (3.54)–(3.55), take a complex frame U with UᴴU = I and UUᴴ = I. In the spectral order (m, n, n, 1), the jump weight from column j to row i is the sum of squared moduli of the two signed jump entries in that frame. The signed imbalances R₀ and R₃ are the negative occupation imbalance of column 0 and the occupation imbalance of column 3, respectively.")),
            Entry("decomposition", "repeated_middle_decomposition", "Exact decomposition of the centered deficit",
                "For real r and nonnegative m and n, put a = ∛(m³ + n³) and b = ∛(n³ + 1). The centered deficit equals the sum of the one-mode deficits on (m, n) at z = −max(0, 2|R₀| − 1), on (n, 1) at z = −max(0, 2|R₃| − 1), and on (a, b) at z = −1, plus the weighted Hölder gaps and the frame remainder. The gaps ab² − (mn² + n) and a²b − (m²n + n²) carry weights γ(r)r and γ(r)r², where γ(r) = 9/[4(1 + r³)] with Lean's division on all reals. The frame remainder consists of the two singleton losses and the signed outer-crossing terms."),
            Entry("lower-bound", "repeated_middle_lower_bound", "Conditional lower bound for the source deficit",
                "Assume r ≥ 1 and 0 ≤ m ≤ n ≤ 1. The exact premise OneModeBound r requires the one-mode deficit at (r, v, w, z) to be nonnegative for every real v, w, and z with 0 ≤ v ≤ w and −1 ≤ z ≤ 1. The weighted sum of the two Hölder gaps and the frame remainder are each nonnegative, and their sum is a lower bound for the source deficit. The proof identifies the source and centered deficits and applies OneModeBound r at all three pairs in the decomposition."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}

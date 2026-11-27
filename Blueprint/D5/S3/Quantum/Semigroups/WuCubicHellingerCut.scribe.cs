using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicHellingerCutDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicHellingerCut.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hellinger bound for the ordinary-trace two-CAR Wu cubic deficit.",
        H("Hellinger bound for the two-mode Wu cubic deficit"),
        Blocks(
            Paragraph(Text("Use the equal-cap, exponent-three specialization of Wu v1, Remark 3.15, equation (3.54), " +
                "with r = exp(β/3), ordered levels (m,n,q,1), and an arbitrary complex unitary eigenframe U. " +
                "Write δ for the normalized ordinary-trace deficit and δocc for the deficit at the occupation frame " +
                "with the same spectrum.")),
            Entry("hellinger-long-crossing", "long_crossing_ge_hellinger", "Endpoint square roots and the CAR crossing",
                "If t₀ and t₃ are the odd masses of the extreme lines, the symmetric long crossing is at least " +
                "(√t₀−√t₃)². The sharp CAR radical uses P = √((1−t₀)t₃) and Q = √(t₀(1−t₃)). " +
                "The identities P²−Q² = t₃−t₀ and P+Q ≤ √t₀+√t₃ give the square-root bound, including zero masses. " +
                "In the deficit estimate this contributes 2κ(√a−√b)² for a = 2t₀, b = 2t₃ and κ = Zlong/4."),
            Entry("hellinger-angular-loss", "hellinger_deficit_bound", "Angular loss for the physical deficit",
                "Use the matched adjacent mixture L₀ with 0 ≤ L₀ ≤ min(Z₀,Z₂). For i = 0,2 put " +
                "Pᵢ = (Aᵢ+Zᵢ−L₀)/2 and Gᵢ = Bᵢ/2−2Pᵢ. Set p = P₀+P₂, k = (P₀−P₂)/p, Gs = G₀+G₂, " +
                "R = G₀−G₂−k Gs and z = a+b+k(a−b). Assume P₀,P₂,κ > 0 and P₀P₂/p−L₀/4 ≥ 0. " +
                "With η ≥ 0, the quadratic in (√a,√b) has positive trace and determinant " +
                "(1−k²)η²+(4κ−kR)η−R²/4. If that determinant is nonnegative, completing the remaining " +
                "quadratic in z ≥ 0 gives δ ≥ δocc−max(0,2η−Gs)²/(4p). The estimate holds throughout the frame " +
                "space under the stated coefficient hypotheses."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}

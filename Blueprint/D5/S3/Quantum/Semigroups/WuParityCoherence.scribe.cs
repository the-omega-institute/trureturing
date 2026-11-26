using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuParityCoherenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuParityCoherence.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed CAR jumps give exact formulas for parity interference and rank-two projection defects.",
        H("Signed parity coherence in two CAR modes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-parity-interference"),
                DeclarationHandle.Create(Owner + "signed_interference"),
                H("Lowering and raising interference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text(
                        "In physical occupation order (00, 01, 10, 11), the lowering jumps are "
                        + "E₀₂ + E₁₃ and −E₀₁ + E₂₃. Write B for the block with rows (00, 11) "
                        + "and columns (01, 10). For a Hermitian M, keep the opposite-parity entries "
                        + "of each jump sum and pair them with M² by the ordinary real trace. "
                        + "The lowering trace is twice the real part of the determinant with rows "
                        + "0 of B(M²) and 1 of B(M). The raising trace uses rows 0 of B(M) and 1 of "
                        + "B(M²).")),
                    Paragraph(Text(
                        "The cubic deficit weights the two traces by −γr² and −γr, respectively, "
                        + "where γ = 9/[4(1 + r³)]. Their sum is −2γr times the real part of "
                        + "r times the lowering determinant plus the raising determinant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-two-projection-four-square-defect"),
                DeclarationHandle.Create(Owner + "rankTwo_projection_defect"),
                H("Exact four-square defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text(
                        "Let Q be a Hermitian projection of trace two. Let A be its even principal "
                        + "block, and let B be its even-row, odd-column block, in the same sector orders. "
                        + "Set L = Re(A₁₁ − A₀₀), and let G be the ordinary real trace pairing of Q "
                        + "with the sum of its lowering and raising sandwiches. The exact defect "
                        + "3 − L² − G equals 3(Re Tr A − 1)² + 4|A₀₁|² "
                        + "+ 2|B₀₀ − overline(B₁₁)|² + 2|B₀₁ + overline(B₁₀)|².")),
                    Paragraph(Text(
                        "The real trace pairing contains +4 Re det B. Expanding the two squared "
                        + "moduli of cross-block entries produces the corresponding −4 Re det B "
                        + "in the defect. The two even-site diagonal equations of Q² = Q supply "
                        + "the remaining terms. The four squares vanish exactly when G = 3 − L²."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-two-projection-occupation-maximum"),
                DeclarationHandle.Create(Owner + "rankTwo_projection_isGreatest"),
                H("Attained maximum at fixed occupation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text(
                        "For each L in [−1, 1], the greatest value of G over Hermitian projections "
                        + "of trace two with Re Tr(NQ) = 2 + L is 3 − L², where the total number "
                        + "operator N is diag(0, 1, 1, 2). An attaining projection on that same "
                        + "slice commutes with first-mode occupation.")),
                    Paragraph(Text(
                        "The four-square identity bounds G on the entire slice. For attainment, "
                        + "take the identity on the first mode tensored with the real one-mode "
                        + "projection with diagonal p = (1 − L)/2 and q = (1 + L)/2 and both "
                        + "off-diagonal entries √(pq). This projection has the required occupation "
                        + "trace and makes all four squares vanish, including at both endpoints."))),
                DescribeRole.Theorem))));
}

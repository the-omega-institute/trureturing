using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfResidualNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/ZeckendorfResidualNormalForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Legal residual normal forms.",
        H("Legal residual normal forms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualnormalform-rank"),
                DeclarationHandle.Create(Prefix + "rank"),
                H("Fixed-length binary rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rank [] = 0 and rank (a :: w) = a.val * 2 ^ w.length + rank w for words over Fin 2. At fixed length this natural-number rank strictly decreases when B1 is replaced by B0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualnormalform-1"),
                DeclarationHandle.Create(Prefix + "normalized_state_cover"),
                H("Legal residual normal forms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem normalized_state_cover (H : ℕ) (hH : 14 ≤ H) (w : List (Fin 2)) (hw : NoAdjacentOnes w) : ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧ ZeckendorfRawWindow.residual (Nat.fib H) w = ZeckendorfRawWindow.residual (Nat.fib H) v ∧ ¬ B1 <:+: v.drop 7`.")),
                    Paragraph(Text("Every complete F_H residual has a legal length H+7 representative whose final H digits avoid 00010101001000. Arbitrary-context replacement preserves the complete residual and strictly decreases fixed-length binary rank; no confluence assumption is required."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfContextualReplacement"))]));
}

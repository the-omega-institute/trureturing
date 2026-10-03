using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfContextualReplacementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/ZeckendorfContextualReplacement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fourteen-digit contextual replacement preserves complete partial Fibonacci parity residuals.",
        H("Contextual Fibonacci Parity Replacement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorfcontextualreplacement-b0"),
                DeclarationHandle.Create(Prefix + "B0"),
                H("Smaller replacement block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B0 : List (Fin 2) is [0,0,0,1,0,0,1,0,1,0,1,0,0,0], the fourteen-digit MSD block 00010010101000."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfcontextualreplacement-b1"),
                DeclarationHandle.Create(Prefix + "B1"),
                H("Larger replacement block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B1 : List (Fin 2) is [0,0,0,1,0,1,0,1,0,0,1,0,0,0], the fourteen-digit MSD block 00010101001000."))),
                DescribeRole.Definition),
            Paragraph(Text("The source conventions are the padded most-significant-digit Fibonacci words of Moradi, Rampersad, and Shallit, arXiv:2603.21645v1. This bridge does not establish a state-count bound or settle Problem 1.")),
            Describe.Lean(
                DescribeId.Create("zeckendorfcontextualreplacement-1"),
                DeclarationHandle.Create(Prefix + "contextual_replacement"),
                H("Equality on every continuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem contextual_replacement (H : ℕ) (p u : List (Fin 2)) (hH : 14 ≤ H) (huH : 14 + u.length ≤ H) (hlegal : NoAdjacentOnes (p ++ B1 ++ u)) : ZeckendorfRawWindow.residual (Nat.fib H) (p ++ B1 ++ u) = ZeckendorfRawWindow.residual (Nat.fib H) (p ++ B0 ++ u)`.")),
                    Paragraph(Text("For H at least fourteen, arbitrary high context p and low context u with fourteen plus the length of u at most H, replacing 00010101001000 by 00010010101000 preserves the entire Option-valued residual at shift F_H. The same realized high and low supports are retained in all three carry regions. The equality includes the empty suffix, every longer suffix, and undefined execution on invalid suffixes."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfRawWindow")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfCarryBarrier"))
        ]));
}

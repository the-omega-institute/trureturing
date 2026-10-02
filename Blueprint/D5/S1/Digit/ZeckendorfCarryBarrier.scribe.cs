using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfCarryBarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/ZeckendorfCarryBarrier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict conjugate estimates bound how far a high Fibonacci addition can change canonical support.",
        H("Canonical Fibonacci Carry Barrier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorfcarrybarrier-1"),
                DeclarationHandle.Create(Prefix + "lower_support_carry_barrier"),
                H("Lower boundary after high addition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem lower_support_carry_barrier (P : List ℕ) (m j : ℕ) (hP : P.IsZeckendorfRep) (hm : 4 ≤ m) (hmin : ∀ k ∈ P, m ≤ k) (hj : m - 1 ≤ j) : ∀ k ∈ wdigits ((P.map Nat.fib).sum + Nat.fib j), m - 2 ≤ k`.")),
                    Paragraph(Text("If P is canonical, m is at least four, every index of P is at least m, and j is at least m minus one, then every index in the canonical support of the sum of P and F_j is at least m minus two. Empty supports and the boundary index are included. Strict finite tails and the open conjugate interval of length one identify the normalized error; least-digit dominance gives the support bound."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/ZeckendorfBeattyBridge"))
        ]));
}

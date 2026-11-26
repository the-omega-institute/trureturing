using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuPhysicalHighHighDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact correlation of the two directed high-high entries for the signed two-mode jumps.",
        H("The two physical high-high weights"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-high-high"),
                DeclarationHandle.Create("D5/S3/Quantum/Semigroups/WuPhysicalHighHigh.weighted_high_high"),
                H("Weighted identity and marginal entry loss"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Specialize the signed-spin hypothesis in Wu v1, Remark 3.15, equations (3.54)–(3.55), to two equal-cap anticommuting modes at exponent three. In occupation order 00, 01, 10, 11 the repository modes are J₂ and −J₁, which give the same squared weights as J₁ and J₂. For orthogonal unit vectors u and v over ℂ, w(u,v) is the sum of squared jump amplitudes from v to u. Write R for the occupation imbalance, η for the parity pairing, and σ and τ for the pairings with the conjugate-twisted vector and its image under the imbalance matrix.")),
                    Paragraph(Text("For nonnegative weights d₊ and d₋, put A = (d₊ + d₋)/2 and ρ = (d₊ − d₋)/(d₊ + d₋). The weighted sum d₊w(u,v) + d₋w(v,u) equals A(1 + ρRᵤ)(1 − ρRᵥ) minus A(2 − ρ²)|η|²/4 and A|σ + ρτ|². The formula includes d₊ = d₋ = 0 using Lean's real division. The proof computes the sum and difference of the two jump sandwiches on arbitrary complex matrices with ordinary trace and the ordinary transpose in the twist. It evaluates them on the rank-one input vvᴴ and uses the even-coordinate determinant identity to complete the squares.")),
                    Paragraph(Text("For any two marginal caps, the second equality gives the weighted sum of their gaps from w(u,v) and w(v,u). It equals the weighted caps minus the product term plus both squares. At u = |00⟩, v = |11⟩ and d₊ = d₋ = 1, the parity square is zero and the twist square is one. Omitting them raises the predicted weight by exactly one.")),
                    Paragraph(Text("For signed transfer from (m,n,n,1) to (m,n,q,1) in a fixed complex frame, assume r ≥ 1 and 0 ≤ m ≤ n ≤ q ≤ 1. Use u at level 1 and v at level q. For g(v,w) = c(v−w)²(v+w) + e(v−w)³ with the cubic coefficients c and e, the direction weights are d₊ = g(1,n) − g(1,q) and d₋ = g(n,1) − g(q,1). The first equality rewrites the loss in the exact deficit increment, which is the signed scalar increment including entropy, plus the nonnegative increases from the two lower levels, minus that loss. The repeated-middle lower bound can then be inserted with both squares retained."))),
                DescribeRole.Theorem))));
}

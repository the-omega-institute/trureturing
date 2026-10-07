using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Gaussian;

internal sealed class GaussianFourthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian moments, independence and operator norm tails.",
        H("Gaussian Fourth"),
        Blocks(
            Paragraph(Text("Gaussian moments, independence and operator norm tails. The results below relate gaussian fourth to the stochastic ellipsoid construction.")),
            Node("claim-1", "pow_four_le_exp", "pow four le exp",
                "y⁴ ≤ 24(e^y + e^{-y}). The i = 4 term of the exponential series at |y|.", DescribeRole.Theorem),
            Node("claim-2", "pow_four_le_of_pos", "pow four le of pos",
                "The domination that gives both the integrability and the moment bound.", DescribeRole.Theorem),
            Node("claim-6", "integral_norm_pow_four_le", "integral norm pow four le",
                "E[‖ξ_k‖⁴] ≤ 100·h²·d², h = c², d = Fintype.card (UT n). Chebyshev's sum inequality replaces the cross terms, so no independence of the coordinates is needed.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

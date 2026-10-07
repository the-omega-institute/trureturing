using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class TruncSumMeanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Trunc Sum Mean"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate trunc sum mean to the stochastic ellipsoid construction.")),
            Node("claim-1", "integral_sum_sqTrunc_ge", "integral sum sq Trunc ge",
                "E[G] from below. G = ∑_{k<K} min(‖ξ_k‖², cap), so the per-step bound sums.", DescribeRole.Theorem),
            Node("claim-2", "driftCen_ge", "drift Cen ge",
                "driftCen from below. The shape hLb consumes: the centre is at least κ(1+ε) times the summed lower bound, the (1+1/ε)(c₃η)² piece being non-negative.", DescribeRole.Theorem),
            Node("claim-3", "etaAdopted_sq", "eta Adopted sq",
                "η² = 2·h·dim·n at the adopted parameters.", DescribeRole.Theorem),
            Node("claim-5", "horizon_mul_card_ge", "horizon mul card ge",
                "T·dim ≥ 8·log n — the drift scale, from below. horizon n = 16·log n/n² and card (UT n) = n(n+1)/2, so the product is 8·log n·(n+1)/n. With κ ≥ 1/2 and 1 + ε ≥ 1, driftCen_ge_adopted then gives driftCen ≥ 4·log n·(1 − 50/n), which is exactly what hLb needs against the −4·log n on the other side.", DescribeRole.Theorem),
            Node("claim-6", "integral_sum_sqTrunc_le", "integral sum sq Trunc le",
                "E[G] from above, the companion hbudget needs: the truncation only lowers, so ∫ min(‖ξ_k‖², cap) ≤ ∫ ‖ξ_k‖² = c²·dim, and summing gives K·c²·dim = T·dim at K = N.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

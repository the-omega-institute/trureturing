using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class StateInvariantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/StateInvariant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("State Invariant"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate state invariant to the stochastic ellipsoid construction.")),
            Node("claim-5", "gaussStep", "gauss Step",
                "The projected Gaussian part of one step.", DescribeRole.Definition),
            Node("claim-6", "liftStep", "lift Step",
                "The one-sided lift applied at one step.", DescribeRole.Definition),
            Node("claim-10", "chain_fst_eq", "chain fst eq",
                "The decomposition. A_k = A₀ + (accumulated projected Gaussian) + (accumulated lifts).", DescribeRole.Theorem),
            Node("claim-11", "scaled", "scaled",
                "N(0, c²·Id) on E: the standard Gaussian scaled by c.", DescribeRole.Definition),
            Node("claim-13", "scaled_conv_scaled", "scaled conv scaled",
                "The convolution identity: N(0,a²) ∗ N(0,b²) = N(0,a²+b²) on E.", DescribeRole.Theorem),
            Node("claim-15", "starProjection_add_self", "star Projection add self",
                "π x + π x = x + R x with R = Submodule.reflection K: the Maurey split at one step.", DescribeRole.Theorem),
            Node("claim-16", "reflStep", "refl Step",
                "The reflected increment R_j ξ_j, R_j = π_j − π̃_j.", DescribeRole.Definition),
            Node("claim-17", "gaussSum_add_self", "gauss Sum add self",
                "The Maurey split, accumulated: 2 Σ_{j<k} π_j ξ_j = Σ_{j<k} ξ_j + Σ_{j<k} R_j ξ_j. Both sums on the right are over *unprojected* increments, which is what makes the induction possible.", DescribeRole.Theorem),
            Node("claim-18", "opNorm_gaussSum_le", "op Norm gauss Sum le",
                "Hence the accumulated projected sum is dominated by the two halves.", DescribeRole.Theorem),
            Node("claim-21", "measureReal_opNorm_symMat_ge", "measure Real op Norm sym Mat ge",
                "Corollary 3.2 for a scaled standard Gaussian on the UT n carrier. If Z has law N(0, ρ²·Id) then its symmetric matrix obeys Klartag's operator-norm tail.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

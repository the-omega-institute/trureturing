using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class StepSecondMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Step Second Moment"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate step second moment to the stochastic ellipsoid construction.")),
            Node("claim-1", "integral_norm_coord_sq", "integral norm coord sq",
                "∫ ‖ω k‖² = dim, from StepInputs.integral_norm_sq_starProjection at the whole space.", DescribeRole.Theorem),
            Node("claim-2", "integral_norm_step_sq", "integral norm step sq",
                "∫ ‖ξ_k‖² = c²·dim at the chain's own step.", DescribeRole.Theorem),
            Node("claim-3", "min_ge_sub_sq_div", "min ge sub sq div",
                "min(x, c) ≥ x − x²/c for 0 ≤ x and 0 < c.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

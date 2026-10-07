using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class StepInputsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/StepInputs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Step Inputs"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate step inputs to the stochastic ellipsoid construction.")),
            Node("claim-1", "memLp_dual", "mem Lp dual",
                "A continuous linear functional is square-integrable for a standard Gaussian.", DescribeRole.Theorem),
            Node("claim-2", "integral_sq_dual", "integral sq dual",
                "The second moment of a linear functional under a standard Gaussian is ‖L‖².", DescribeRole.Theorem),
            Node("claim-3", "norm_sq_starProjection_eq_sum", "norm sq star Projection eq sum",
                "‖π x‖² expanded in an orthonormal basis of the range, with the projection removed.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

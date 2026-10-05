using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStoppedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped to the stochastic ellipsoid construction.")),
            Node("claim-1", "stoppedLogDet", "stopped Log Det",
                "D^τ_k = log det A_{min k (τ−1)}.", DescribeRole.Definition),
            Node("claim-2", "stoppedSub", "stopped Sub",
                "K^τ_k = F(C_k) before the stopping time and ⊥ after: the free subspace the drift's N_k and quadratic term read.", DescribeRole.Definition),
            Node("claim-3", "stoppedV", "stopped V",
                "V^τ_k = π_k(A_k⁻¹) before the stopping time and 0 after.", DescribeRole.Definition),
            Node("claim-8", "integral_errCond", "integral err Cond",
                "The integral is unchanged — which is why substituting errCond for err leaves the drift bound's conclusion alone.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

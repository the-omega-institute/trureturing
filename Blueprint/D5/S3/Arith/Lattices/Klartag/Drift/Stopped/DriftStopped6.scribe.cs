using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped6Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped6"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped6 to the stochastic ellipsoid construction.")),
            Node("claim-1", "le_eigenvalues_of_lower", "le eigenvalues of lower",
                "Every eigenvalue is at least the quadratic form's lower bound. The companion of GoodEvent.abs_eigenvalues_le_opNorm, which the tree has and which supplies the upper bound; this direction is stated nowhere.", DescribeRole.Theorem),
            Node("claim-2", "det_bounds_of_stateBounds", "det bounds of state Bounds",
                "StateBounds is a two-sided determinant bound. m ≤ λᵢ ≤ M for every eigenvalue, so mⁿ ≤ det A ≤ Mⁿ. This is what makes log det of the stopped state a bounded function.", DescribeRole.Theorem),
            Node("claim-3", "continuous_symMat_det", "continuous sym Mat det",
                "symMat is linear in the Frobenius coordinates and det is a polynomial, so the composite is continuous — the route to measurability of logDet.", DescribeRole.Theorem),
            Node("claim-5", "measurable_stoppedLogDet", "measurable stopped Log Det",
                "stoppedLogDet is measurable. min k (τ − 1) takes values in {0, …, k}, so the stopped state is a finite sum of indicators of the fibres of a measurable ℕ-valued map.", DescribeRole.Theorem),
            Node("claim-6", "integrable_stoppedLogDet", "integrable stopped Log Det",
                "intD, the drift's first integrability field. stateBounds_stopped holds for every k and every ω, so the stopped log-determinant is bounded between n·log m and n·log M.", DescribeRole.Theorem),
            Node("claim-10", "integrable_stoppedFreeDim", "integrable stopped Free Dim",
                "intN, the drift's second integrability field — free, as it is for the unstopped chain (ChainWiring.integrable_freeDim): the free dimension never exceeds dim E.", DescribeRole.Theorem),
            Node("claim-14", "r0Adopted", "r0Adopted",
                "r₀ at the adopted parameters: the good event's operator-norm threshold 6√(T·n), which GoodEvent.lean:320 evaluates to 24√(log n / n).", DescribeRole.Definition),
            Node("claim-15", "etaAdopted", "eta Adopted",
                "η at the adopted parameters: √(2 h d n) with h = ParamsAdopted2.stepSizeAdopted2 n; ParamsAdopted2.eta2_le bounds it by √2 · n⁻³.", DescribeRole.Definition),
            Node("claim-17", "mAdopted", "m Adopted",
                "m_adopted: the state's lower bound a₀ − (r₀ + c₃η), SlackHyp's first free argument. a₀ = (1 − 1/n)⁻² is D5.S3.Arith.Lattices.Klartag.a0C (Lemma43Uniform.lean:431).", DescribeRole.Definition),
            Node("claim-18", "MAdopted", "MAdopted",
                "The state's upper bound M = a₀ + (r₀ + c₃η).", DescribeRole.Definition),
            Node("claim-19", "deltaAdopted", "delta Adopted",
                "δ = η / m, the smallest value DriftStopped.hpt_stopped's hδ admits.", DescribeRole.Definition),
            Node("claim-20", "cAdopted", "c Adopted",
                "c_adopted: the drift's quadratic coefficient 1 / (2 M² (1+δ)²), SlackHyp's second free argument — the c at which DriftStopped.hpt_stopped is stated.", DescribeRole.Definition),
            Node("claim-21", "slackAdopted", "slack Adopted",
                "slack_adopted: the slack the middle case must fit into, of order 1.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

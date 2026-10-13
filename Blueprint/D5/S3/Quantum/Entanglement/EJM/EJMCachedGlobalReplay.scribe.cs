using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMCachedGlobalReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMCachedGlobalReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound original-DAG replay using checked local caches",
        H("Sound original-DAG replay using checked local caches"),
        Blocks(
            Paragraph(Text("The exact original shared DAG, original partial contexts, all four split values, actual global symmetry rank descent, F1/F2 and scale 6987435 are retained. Fuel-prefix validity proves every split uses an unknown coordinate before applying the complete local transition receipts. Fuel-zero checks reject and cannot earn a branch. The complete actual globalAccepted computation remains necessary; no imported producer minimum or single successful benchmark leaf supplies it.")),
            Node("Prefix", "Prefix", "Actual future coordinates remain unknown",
                "The invariant bounds fuel by twenty-one and records unknownness of every global coordinate at or beyond the corresponding original prefix depth.", DescribeRole.Definition),
            Node("step-valid", "step_valid", "The original fuel-indexed split preserves full validity",
                "The original node interpretation determines the next coordinate. Positive remaining child fuel excludes the terminal modulo wrap, the prefix proves unknownness, and the full cache update theorem preserves all actual block associations.", DescribeRole.Theorem),
            Node("valid-lower-le-score", "valid_lower_le_score", "Every valid cache bounds every compatible completion",
                "This applies the full original thirty-two-block association theorem. The fuel and prefix do not weaken its exact original score or inequality.", DescribeRole.Theorem),
            Node("globalAccepted", "globalAccepted", "Complete actual original global replay obligation",
                "Acceptance starts at the original root, fuel twenty-one, the proved initial cache and the all-unknown actual event. It checks all actual contexts and value choices of the original DAG.", DescribeRole.Definition),
            Node("accepted-score-lower-bound", "accepted_score_lower_bound", "Accepted full replay earns the original positive scale margin",
                "Generic cached-replay soundness receives complete local kernel receipts, the proved initial/step/lower invariants, actual score-preserving global symmetries and actual strict rank descent. Only complete actual replay acceptance then yields scale at most score for every original full event.", DescribeRole.Theorem),
            Node("accepted-excludes-triangle-local", "accepted_excludes_triangle_local", "The accepted exact score excludes triangle locality",
                "The original score-expectation cancellation theorem turns the earned positive exact score into the actual EJM locality refutation. Global acceptance is still an explicit undisguised remaining obligation until kernel checked.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

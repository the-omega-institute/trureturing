using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class GoodPathCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Good Path Core"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate good path core to the stochastic ellipsoid construction.")),
            Node("claim-12", "constFil", "const Fil",
                "The constant filtration, so the ℱ-relative lemmas of DriftInputsStopped give their ambient forms with no second proof.", DescribeRole.Definition),
            Node("claim-21", "coe_v_adopted", "coe v adopted",
                "v = c² = h at the adopted step scale.", DescribeRole.Theorem),
            Node("claim-22", "step_tail_exponent", "step tail exponent",
                "The per-step tail is exactly e^{−n} — the adopted η = √(2hdn) is chosen for it.", DescribeRole.Theorem),
            Node("claim-24", "accGood_thr", "acc Good thr",
                "The accGood failure bound. The adopted r₀ = 24√(log n/n) is exactly 6·√(N·h)·√n, so the GOE tail closes at s = 1 with equality.", DescribeRole.Theorem),
            Node("claim-29", "measurable_opNorm_smul_symMat", "measurable op Norm smul sym Mat",
                "The operator norm of r • symMat is measurable — Increments.measurable_opNorm_mkMat through Increments.smul_symMat_eq_mkMat.", DescribeRole.Theorem),
            Node("claim-35", "failTotal", "fail Total",
                "The three failure probabilities, summed.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

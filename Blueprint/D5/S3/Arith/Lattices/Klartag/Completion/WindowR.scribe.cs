using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class WindowRDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/WindowR.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Window R"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate window r to the stochastic ellipsoid construction.")),
            Node("claim-1", "mR", "m R",
                "The adopted lower bound on the state's quadratic form, DriftStopped6.mAdopted.", DescribeRole.Definition),
            Node("claim-3", "log_le_four_qrt", "log le four qrt",
                "log n ≤ 4·n^{1/4}, from log x ≤ x − 1 at x = n^{1/4}.", DescribeRole.Theorem),
            Node("claim-4", "qrt_ge", "qrt ge",
                "√√n ≥ 37 at the threshold (√√2 073 600 = 37.947).", DescribeRole.Theorem),
            Node("claim-8", "log_mul_le", "log mul le",
                "9216·log n ≤ n at the threshold.", DescribeRole.Theorem),
            Node("claim-11", "mR_ge", "m R ge",
                "window_small at the reach: mR n ≥ a0C n − 1/2.", DescribeRole.Theorem),
            Node("claim-14", "YR", "YR",
                "The y-endpoint of the reach window: YR n·√T = a0C n − mR n, identically in t.", DescribeRole.Definition),
            Node("claim-15", "reachNum", "reach Num",
                "The reach window's numerator: windowR α n = reachNum n/α + √n/2 by rfl.", DescribeRole.Definition),
            Node("claim-16", "windowR", "window R",
                "The reach window.", DescribeRole.Definition),
            Node("claim-19", "sqrtT_mul_YR", "sqrt T mul YR",
                "√T·YR = a0C − mR, the identity that makes window_small t-free.", DescribeRole.Theorem),
            Node("claim-20", "reachNum_eq", "reach Num eq",
                "reachNum = 1/√(mR).", DescribeRole.Theorem),
            Node("claim-22", "windowR_lt_p", "window R lt p",
                "window_lt_p at the reach: 2·reachNum n ≤ α·p and α·√n ≤ 1 give windowR α n < p.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

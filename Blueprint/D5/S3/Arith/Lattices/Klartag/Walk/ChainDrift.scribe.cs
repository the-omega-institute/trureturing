using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainDriftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain Drift"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain drift to the stochastic ellipsoid construction.")),
            Node("claim-1", "telescope", "telescope",
                "The telescoped drift bound. A one-step decrease with an error term sums to a bound on the terminal value. This is the discrete Riemann sum that replaces -(1/2)∫₀^T δ_s ds.", DescribeRole.Theorem),
            Node("claim-2", "integral_le_of_condExp_le", "integral le of cond Exp le",
                "If a conditional expectation is dominated a.e., the expectations are ordered.", DescribeRole.Theorem),
            Node("claim-4", "integral_step", "integral step",
                "One step, integrated.", DescribeRole.Theorem),
            Node("claim-5", "drift_bound", "drift bound",
                "The telescoped drift bound, integrated (Klartag Lemma 3.3, discrete form).", DescribeRole.Theorem),
            Node("claim-6", "horizon", "horizon",
                "T = 16 log n / n² (Klartag Lemma 5.2, p. 23).", DescribeRole.Definition),
            Node("claim-8", "stepSize", "step Size",
                "h = T / N, so that N·h = T exactly.", DescribeRole.Definition),
            Node("claim-11", "stepSize_le", "step Size le",
                "h ≤ n^{-(e+2)}: the step size the choice of numSteps delivers.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Gaussian;

internal sealed class GaussianMaximal2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian moments, independence and operator norm tails.",
        H("Gaussian Maximal2"),
        Blocks(
            Paragraph(Text("Gaussian moments, independence and operator norm tails. The results below relate gaussian maximal2 to the stochastic ellipsoid construction.")),
            Node("claim-3", "maxNorm_sq_tail", "max Norm sq tail",
                "The square's tail is exponential: P{maxNorm²/(2σ²) > t} ≤ 2dN·e^{−t}.", DescribeRole.Theorem),
            Node("claim-4", "lintegral_maxNorm_sq_le", "lintegral max Norm sq le",
                "The second moment, in lintegral form.", DescribeRole.Theorem),
            Node("claim-6", "expectation_max_norm_sq_le_log", "expectation max norm sq le log",
                "The second moment, in Bochner form, at the optimal level a = log(2dN).", DescribeRole.Theorem),
            Node("claim-7", "measurable_at_index", "measurable at index",
                "An increment read at a measurable random index is measurable: ℕ is countable.", DescribeRole.Theorem),
            Node("claim-8", "IntegrableAtIndex", "Integrable At Index",
                "Both moments at a random index are integrable. Domination by maxNorm and maxNorm².", DescribeRole.Definition),
            Node("claim-10", "maximalHyp2_of_laws", "maximal Hyp2 of laws",
                "DriftStopped4.MaximalHyp2, both moments, with one constant.", DescribeRole.Theorem),
            Node("claim-11", "maximalAtAdopted_step", "maximal At Adopted step",
                "DriftStopped4.MaximalAtAdopted at the drift lane's own increments. ChainSetup.step c is c • coord k, whose coordinates are N(0, c²) by ChainSetup.step_coord_law; so v = c² and σ = c·√d with d = card (UT n).", DescribeRole.Theorem),
            Node("claim-12", "six_le_log", "six le log",
                "log n ≥ 6 at the gate's threshold: e⁶ < 404 < 2 073 600.", DescribeRole.Theorem),
            Node("claim-13", "sqrt_log_majorant", "sqrt log majorant",
                "The majorant. √(2·log K) + 1 ≤ 5·√(log n) whenever log K ≤ 10·log n + 3 and log n ≥ 6. The slack is real but not large: at n = 2 073 600 the left side is 17.51 and the right 19.07.", DescribeRole.Theorem),
            Node("claim-14", "log_two_card_numSteps_le", "log two card num Steps le",
                "log (2·d·N) ≤ 10·log n + 3 at the adopted parameters: d ≤ n² and N = ⌈16·n⁷·log n⌉ ≤ 17·n⁷·log n, so 2dN ≤ 34·n⁹·log n, and log 34 ≤ 4, log (log n) ≤ log n − 1.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}

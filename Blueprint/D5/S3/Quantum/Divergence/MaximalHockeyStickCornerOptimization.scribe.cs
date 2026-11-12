using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickCornerOptimizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact reduction of weighted overlap optimization to its common corner",
        H("Exact reduction of weighted overlap optimization to its common corner"), Blocks(
            Paragraph(Text("The trace weight W is arbitrary in this reduction. Strict positivity is imposed only later on its compression. The reduction preserves the full feasible optimization, rather than only the canonical candidate.")),
            Node("diagonal_feasible", "For d_i in [0,1] and t>=0, diag(min(d_i,t(1-d_i))) is PSD and below both diag(d) and t(1-diag(d)). This supplies the canonical feasible point used in the reduction.", true, false),
            Node("diagonal_optimization_reduction", "For d_i in [0,1], arbitrary W and t>=0, weighted optimality of the diagonal canonical overlap over all ambient PSD common lower bounds is equivalent to weighted optimality on the subtype 0<d_i<1, with both W and the candidate compressed. Support, order-preserving extension and cyclic trace transport prove both directions. CornerCriterion consumes this iff.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-corner-optimization-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}

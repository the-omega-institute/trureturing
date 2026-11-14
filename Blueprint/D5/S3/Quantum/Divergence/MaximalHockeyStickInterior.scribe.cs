using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickInteriorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickInterior.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing the positive lower constraint at an interior optimum",
        H("Removing the positive lower constraint at an interior optimum"), Blocks(
            Paragraph(Text("All matrices have the same arbitrary finite complex index type. The trace objective is its real part. This finite perturbation lemma is a repository proof used by the weighted overlap criterion; it is not a general-convex reverse-test optimality assertion.")),
            Node("positive_interior_relaxation", "For Hermitian-feasible Y0 positive definite and below Hermitian upper bounds A and B, and arbitrary matrix weight W, optimality of Re Tr(WY) over positive common lower bounds is equivalent to optimality over all Hermitian common lower bounds. Given a Hermitian competitor, a sufficiently small convex displacement from Y0 remains positive definite. Threshold.weighted_overlap_optimal_iff consumes this removal of the positivity constraint.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-interior-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}

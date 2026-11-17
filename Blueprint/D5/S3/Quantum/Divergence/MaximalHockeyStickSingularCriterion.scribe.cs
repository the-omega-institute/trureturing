using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickSingularCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical overlap optimality on a singular common interior",
        H("Canonical overlap optimality on a singular common interior"), Blocks(
            Paragraph(Text("C may have eigenvalues zero and one. Neither C nor 1-C is assumed invertible. Strict positivity is required only for the compressed trace weight, as supplied for the original pair by CornerWeight.")),
            Node("canonical_feasible", "For a PSD contraction C and t>=0, canonicalOverlap C t belongs to positiveOverlaps C (t(1-C)). OriginalPair reconstructs this candidate into an actual feasible overlap for A,B.", true, false),
            Node("common_canonical_optimal_iff", "For PSD C<=1, t>0 and W with positive-definite interior compression, canonical weighted optimality is equivalent to thresholdPositive(C,t) (PWP) thresholdNegative(C,t)=0 for P=interiorProjection C. This transports the diagonal criterion through the eigenvector unitary.", true, false),
            Node("common_all_thresholds_iff_commute", "For PSD C<=1 and Hermitian W with positive-definite interior compression, canonical optimality at every t>0 is equivalent to (PWP)(PCP)=(PCP)(PWP). OriginalPair consumes this all-threshold geometric classification; no general-f attainment is part of its assumptions.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-singular-criterion-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}

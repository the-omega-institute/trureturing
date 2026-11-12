using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickProfile.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regularity of the actual overlap value",
        H("Regularity of the actual overlap value"), Blocks(
            Paragraph(Text("These estimates concern the actual common-PSD feasible set for arbitrary finite PSD A,B and their original masses. They supply uniform continuity constants for approximate-test gap transfer, not an optimizer for an arbitrary convex cost.")),
            Node("feasible_le_value", "Every feasible positive common lower bound X has real trace at most overlapValue A B. Boundedness follows from the upper bound A. ReverseTest.maximal_hockey_le and original-pair optimality use this supremum bound.", true, false),
            Node("overlap_increment", "For 0<=s<=t and PSD A,B, the overlap increment O(t)-O(s) lies between zero and (t-s) Tr(B). Monotonic inclusion proves the first inequality; rescaling a maximizing overlap proves the upper bound. overlap_lipschitz consumes both bounds.", true, false),
            Node("overlap_lipschitz", "For nonnegative s,t and PSD A,B, |O(t)-O(s)| <= |t-s| Tr(B). This two-sided estimate follows from ordered increments. Approximate.actual_gap_profile_data uses it together with the classical test estimate.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-profile-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}

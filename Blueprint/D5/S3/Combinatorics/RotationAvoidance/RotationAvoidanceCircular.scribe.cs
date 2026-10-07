using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceCircularDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circular permutations represented with the entry one first relate avoidance at all cuts to avoidance of cyclic rotations of a pattern.",
        H("RotationAvoidanceCircular"),
        Blocks(
            Node("rotationavoidancecircular-circularavoiders-definition", "Circular avoiders rooted at one", "circularAvoiders", "For a nonnegative integer n and a pattern q, the circular avoiders are those permutations of one through n whose first entry is one and whose n rotations all avoid q.", DescribeRole.Definition),
            Node("rotationavoidancecircular-singlebadcircles-definition", "Circles with exactly one containing cut", "singleBadCircles", "For a nonnegative integer n and a pattern q, this set consists of permutations of one through n beginning with one for which there exists exactly one cut among zero through n minus one whose rotation contains q. Every other cut avoids q.", DescribeRole.Definition),
            Node("rotationavoidancecircular-counting-cuts-theorem", "Counting full and all but one rotation avoidance", "counting_cuts", "Let n be positive and let q be any pattern. The cardinality of S_n^(n)(q) is n times the number of circular avoiders rooted at one. The cardinality of S_n^(n minus one)(q) is n times that number plus the number of circles rooted at one with exactly one containing cut.", DescribeRole.Theorem),
            Node("rotationavoidancecircular-unique-bad-cut-iff-theorem", "Characterization of a unique containing cut", "unique_bad_cut_iff", "Let n be at least four, let q be a permutation of one through four and let p be a permutation of one through n. Cut zero is the unique cut whose rotation contains q if and only if p contains q, p avoids each of the three nontrivial cyclic rotations of q, and deleting either the first entry or the last entry of p gives a list avoiding q.", DescribeRole.Theorem),
            Node("rotationavoidancecircular-all-cuts-iff-cycle-avoidance-theorem", "Circular avoidance and the rotations of a pattern", "all_cuts_iff_cycle_avoidance", "Let n be positive, let q be a permutation of one through four and let p be a permutation of one through n. All n rotations of p avoid q if and only if p avoids all four cyclic rotations of q.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

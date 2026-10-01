using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak ascent sequences avoiding 210 and permutations avoiding 2-41-3 define two enumeration problems.",
        H("Weak Ascent Sequences and Vincular Avoidance"),
        Blocks(
            Node("weak-ascent-weakascentdefs-wasc", "The weak ascent count", "wasc",
                "The weak ascent count of a sequence is the number of adjacent pairs for which the first entry is at most the second.", DescribeRole.Definition),
            Node("weak-ascent-weakascentdefs-isweakascent", "Weak ascent sequences", "IsWeakAscent",
                "A sequence of nonnegative integers is a weak ascent sequence when its first entry, if present, is zero and each subsequent entry is at most one plus the weak ascent count of the preceding prefix. The empty sequence is included.", DescribeRole.Definition),
            Node("weak-ascent-weakascentdefs-contains210", "The classical pattern 210", "Contains210",
                "A sequence contains 210 when three entries at strictly increasing positions are strictly decreasing in value.", DescribeRole.Definition),
            Node("weak-ascent-weakascentdefs-containsv2413", "The vincular pattern 2-41-3", "ContainsV2413",
                "A word contains 2-41-3 when there are positions i, j, j + 1, k in strictly increasing order such that the entry at j + 1 is less than the entry at i, which is less than the entry at k, which is less than the entry at j.", DescribeRole.Definition),
            Node("weak-ascent-weakascentdefs-weakavoiders", "Weak ascent avoiders of a fixed length", "weakAvoiders",
                "For every nonnegative n, the set W_n(210) consists of the weak ascent sequences of length n containing no classical pattern 210.", DescribeRole.Definition),
            Node("weak-ascent-weakascentdefs-permavoiders", "Vincular avoiders of a fixed size", "permAvoiders",
                "For every nonnegative n, the set S_n(2-41-3) consists of the permutations of the integers from one through n containing no vincular pattern 2-41-3.", DescribeRole.Definition),
            Node("weak-ascent-weakascentdefs-claim", "The equinumerosity assertion", "claim",
                "For every nonnegative n, the number of 210-avoiding weak ascent sequences of length n equals the number of permutations of one through n avoiding 2-41-3.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

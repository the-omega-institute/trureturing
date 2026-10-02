using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackMaximumIntervalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackMaximumIntervals.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size at least four with maximum second. Suppose that, after its first two entries, the values above its first entry decrease and no value below its first entry has both a smaller and a larger such value later. Then p belongs to C. It has no adjacent entries with consecutive values if and only if it is simple or equals E(h) for some h at least two.",
        H("Intervals when the maximum is second"),
        Blocks(
            Node("pop-stack-popstackmaximumintervals-maximum-second-intervals", "Intervals when the maximum is second", "maximum_second_intervals",
                "Let p be a permutation of size at least four with maximum second. Suppose that, after its first two entries, the values above its first entry decrease and no value below its first entry has both a smaller and a larger such value later. Then p belongs to C. It has no adjacent entries with consecutive values if and only if it is simple or equals E(h) for some h at least two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

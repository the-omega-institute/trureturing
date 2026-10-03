using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackSortDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackSort.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sorting class of the stack avoiding 23-1 is enumerated by the large Schroeder numbers.",
        H("Schroeder Enumeration of the Sorting Class"),
        Blocks(
            Node("vincularstack-vincularstacksort-labelledlevel", "Levels of the labelled tree", "labelledLevel",
                "The labelled tree has a single root of label two. A vertex of label k has k children indexed from zero through k minus one. Its child of index zero has label k plus one; a child of positive index i has label i plus two. A level consists of all vertices at its depth together with their labels.", DescribeRole.Definition),
            Node("vincularstack-vincularstacksort-result", "The Schroeder enumeration", "result",
                "For every positive n, the number of permutations of one through n whose image under the right-greedy stack map avoiding 23-1 avoids the classical pattern 231 equals the large Schroeder number of index n minus one.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("zhao-vincular-stack-sorting-schroeder"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

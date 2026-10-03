using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube312EdgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Edge.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic successor of an earlier value cannot cross a later value in a 312-avoider.",
        H("An Upward Edge and a Later Intermediate Value"),
        Blocks(
            Node("fundamental-bijection-thetacube312edge-no-upward-edge-over-later-value", "Exclusion of a crossing successor", "no_upward_edge_over_later_value",
                "In a 312-avoiding permutation, there are no letters x and z such that x occurs before z and x is smaller than z while z is smaller than the cyclic successor of x in its record block.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

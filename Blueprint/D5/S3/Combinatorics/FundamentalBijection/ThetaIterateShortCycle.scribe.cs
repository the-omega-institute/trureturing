using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateShortCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateShortCycle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two specified successor edges force a single initial record block.",
        H("A Cycle Forced by Two Successors"),
        Blocks(
            Node("fundamental-bijection-thetaiterateshortcycle-second-to-penultimate-forces-one-block", "The return edge to one", "second_to_penultimate_forces_one_block",
                "For a 132-avoiding permutation q of size h at least four, if the cyclic successors of one and two are h and h minus one and the successor of h exceeds one, then the successor of h minus one is one and q begins with h.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

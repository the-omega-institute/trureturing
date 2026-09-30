using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateInsertionCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionCycle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Insertion preserves the distinguished-cycle avoidance condition for inverse parameters.",
        H("Cycle Compatibility of Insertion"),
        Blocks(
            Node("fundamental-bijection-thetaiterateinsertioncycle-insertion-cycle", "The inserted cycle and its image", "insertion_cycle",
                "If q is a permutation of size h at least two beginning with h and ending with one, let r be its inverse fundamental image. The image of I(r) is h plus three, followed by q increased by one, followed by h plus two and one, and the inverse image of this word is I(r). Moreover, P(I(r)) avoids 132 through depth two exactly when P(r) does.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

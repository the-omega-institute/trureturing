using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaBasicInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverse.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Record maxima control prefixes and the inverse fundamental bijection is injective on distinct letters.",
        H("Record Bounds and the Inverse Bijection"),
        Blocks(
            Node("fundamental-bijection-thetabasicinverse-last-record-bounds-prefix", "Bounds from the last record", "last_record_bounds_prefix",
                "For every position i of a word, all entries through i are at most the value of the last left-to-right maximum through i.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetabasicinverse-hat-inj-on", "Distinct cyclic successors", "hat_inj_on",
                "For a word with distinct letters, two letters in the word have the same cyclic successor only when they are equal.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

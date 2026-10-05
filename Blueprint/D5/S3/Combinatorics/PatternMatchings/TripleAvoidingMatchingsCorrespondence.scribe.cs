using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsCorrespondenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsCorrespondence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Encoding and queue decoding are inverse maps between P1-avoiding matchings and accepted action words.",
        H("A bijection between avoiding matchings and accepted words"),
        Blocks(
            Node("bss-correspondence-matchingequiv", "The matching-word correspondence", "matchingEquiv",
                "For every nonnegative integer n, the P1-avoiding perfect matchings on 2n ordered vertices are in bijection with the accepted action words of length 2n. The forward map records the scan actions, and the inverse pairs vertices with the ordered queue. Both closing choices at height two are retained.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

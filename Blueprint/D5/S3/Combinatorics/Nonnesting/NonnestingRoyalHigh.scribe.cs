using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingRoyalHighDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingRoyalHigh.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generating function for nonnesting permutations avoiding 1233 and 1322 satisfies the stated quadratic equation.",
        H("Enumeration for 1233 and 1322"),
        Blocks(
            Node("nonnesting-nonnestingroyalhigh-result", "The 1233 and 1322 generating function", "result",
                "Let R be the ordinary generating function counting doubled nonnesting permutations avoiding 1233 and 1322 by the number of distinct letters. Then xR squared - (1 - x) squared times R + (1 - x) squared equals zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id("claim1233"))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

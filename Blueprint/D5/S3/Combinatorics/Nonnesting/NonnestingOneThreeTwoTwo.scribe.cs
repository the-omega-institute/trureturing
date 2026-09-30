using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnesting permutations avoiding 1322 have the asserted binomial enumeration.",
        H("Enumeration of Nonnesting Permutations Avoiding 1322"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwo-result", "The 1322 enumeration", "result",
                "For every positive n, n times the number of nonnesting permutations of the multiset with two copies of each letter from one through n avoiding 1322 equals the sum, over k from zero through n minus one, of the product of the binomial coefficients choosing k from 3n and choosing n minus one from 2n minus k minus two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id("claim1322"))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
